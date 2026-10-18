use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use isabelle_rs::ml::host::files::{
    EffectSet, FileHostBridge, HostIoError, HostRoots, PhaseEffects, RestrictedHost,
};
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, WorkKind};
use isabelle_rs::ml::{Value, Vm};

static NEXT_AREA: AtomicU64 = AtomicU64::new(0);

struct TestArea(PathBuf);

impl TestArea {
    fn new() -> Self {
        let number = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ml-pretty-sha1-{}-{number}", std::process::id(),));
        fs::create_dir_all(path.join("source")).unwrap();
        fs::create_dir(path.join("staging")).unwrap();
        fs::set_permissions(path.join("staging"), fs::Permissions::from_mode(0o700)).unwrap();
        Self(path)
    }
}

impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn build_vm(area: &TestArea) -> (Vm, BuildLifecycle, Arc<FileHostBridge>) {
    let mut binding = None;
    let mut vm = Vm::with_host_factory(|stop| -> Result<_, HostIoError> {
        let lifecycle = BuildLifecycle::new(stop);
        let lease = lifecycle.start_root(WorkKind::Evaluation, "pretty SHA1 test").unwrap();
        let roots = HostRoots {
            source: area.0.join("source"),
            resources: BTreeMap::new(),
            staging_parent: area.0.join("staging"),
            staging_name: PathBuf::from("build"),
        };
        let grants = EffectSet::default();
        let host = RestrictedHost::new(
            lifecycle.clone(),
            &lease,
            roots,
            grants.clone(),
            grants.clone(),
            PhaseEffects { active: grants.clone(), draining: grants },
            BTreeMap::new(),
        )?;
        let bridge = Arc::new(FileHostBridge::new(host, lease));
        binding = Some((lifecycle, Arc::clone(&bridge)));
        Ok(bridge)
    })
    .unwrap();
    let (lifecycle, bridge) = binding.unwrap();
    vm.install_bootstrap_host(Arc::clone(&bridge)).unwrap();
    (vm, lifecycle, bridge)
}

#[test]
fn printer_original_ml_pretty_then_sha1_registers_real_digest_callback() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    vm.evaluate(
        "sha1-prelude.sml",
        r#"
        structure FixedInt = struct
          type int = int val max = Int.max
          fun fromInt value = value fun toInt value = value
        end;
        structure Unsynchronized = struct datatype ref = datatype ref end;
        fun the_default default NONE = default | the_default _ (SOME value) = value;
        fun quote text = "\"" ^ text ^ "\"";
        val ML_system_pp = PolyML.addPrettyPrinter;
        val ML_system_pretty = PolyML.prettyRepresentation;
        val implode = String.concat;
        val chr = fn value => String.str (Char.chr value);
        fun funpow (0: int) _ value = value
          | funpow count operation value = funpow (count - 1) operation (operation value);
        fun replicate_string (0: int) _ = ""
          | replicate_string 1 text = text
          | replicate_string count text =
              if count mod 2 = 0 then replicate_string (count div 2) (text ^ text)
              else replicate_string (count div 2) (text ^ text) ^ text;
    "#,
    )
    .unwrap();
    vm.evaluate(
        "src/Pure/ML/ml_pretty.ML",
        include_str!("../isabelle-source/src/Pure/ML/ml_pretty.ML"),
    )
    .unwrap();
    vm.evaluate_native_sha1_module(
        "src/Pure/General/sha1.ML",
        include_str!("../isabelle-source/src/Pure/General/sha1.ML"),
    )
    .unwrap();
    vm.evaluate(
        "sha1-pretty.sml",
        "val digest_pretty = ML_Pretty.string_of \
         (PolyML.prettyRepresentation (SHA1.fake \"fixture\", 8));",
    )
    .unwrap();
    assert_eq!(
        vm.lookup_value("digest_pretty").unwrap().and_then(Value::as_text),
        Some("\"fixture\""),
    );
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}
