use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use isabelle_kernel::{Signature, TrustedTheory};
use isabelle_rs::ml::host::files::{
    EffectSet, FileHostBridge, HostIoError, HostRoots, PhaseEffects, RestrictedHost,
};
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, WorkKind};
use isabelle_rs::ml::{Value, Vm};
use sha1::Sha1;
use sha2::{Digest, Sha256};
use std::rc::Rc;

static NEXT_AREA: AtomicU64 = AtomicU64::new(0);

struct TestArea(PathBuf);

impl TestArea {
    fn new() -> Self {
        let number = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ml-bootstrap-{}-{number}", std::process::id()));
        fs::create_dir_all(path.join("source/src/Pure/ML")).unwrap();
        fs::create_dir(path.join("staging")).unwrap();
        fs::set_permissions(path.join("staging"), fs::Permissions::from_mode(0o700)).unwrap();
        Self(path)
    }

    fn write_source(&self, name: &str, content: &str) {
        fs::write(self.0.join("source/src/Pure").join(name), content).unwrap();
    }

    fn root(&self) -> &Path {
        &self.0
    }
}

impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn build_vm_with_clock(
    area: &TestArea,
    is_clock_allowed: bool,
) -> (Vm, BuildLifecycle, Arc<FileHostBridge>) {
    let mut binding = None;
    let mut vm = Vm::with_host_factory(|stop| -> Result<_, HostIoError> {
        let lifecycle = BuildLifecycle::new(stop);
        let lease = lifecycle.start_root(WorkKind::Evaluation, "bootstrap test").unwrap();
        let roots = HostRoots {
            source: area.root().join("source"),
            resources: BTreeMap::new(),
            staging_parent: area.root().join("staging"),
            staging_name: PathBuf::from("build"),
        };
        let grants = EffectSet {
            read_source: true,
            write_staging: true,
            read_clock: is_clock_allowed,
            sleep: is_clock_allowed,
            ..EffectSet::default()
        };
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
fn build_vm(area: &TestArea) -> (Vm, BuildLifecycle, Arc<FileHostBridge>) {
    build_vm_with_clock(area, false)
}

#[test]
fn time_basis_now_and_sleep_use_explicit_leased_effects() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_vm_with_clock(&area, true);
    vm.evaluate(
        "time.sml",
        "val stamp = Time.now (); \
        val seconds = Time.toReal stamp; \
        val _ = OS.Process.sleep (Time.fromReal 0.0);",
    )
    .unwrap();
    assert!(vm.lookup_value("seconds").unwrap().and_then(Value::as_real).unwrap() > 0.0);
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn time_basis_ordering_compares_native_times_without_numeric_overloading() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    vm.evaluate(
        "ordered-time.sml",
        "val ordered = Time.fromReal 1.0 >= Time.fromReal 0.1 \
         andalso Time.fromReal 0.1 < Time.fromReal 1.0;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("ordered").unwrap().and_then(Value::as_bool), Some(true));
    assert_eq!(
        vm.evaluate("numeric-time.sml", "val invalid = Time.fromReal 1.0 + Time.fromReal 2.0;")
            .unwrap_err()
            .kind,
        isabelle_rs::ml::MlErrorKind::Type
    );
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn root_prefix_original_directives_stop_at_context_without_skipping_suffix() {
    let area = TestArea::new();
    let root0 = "(* source prelude *) ML_file \"ML/first.ML\";";
    let root = "chapter \"Pure bootstrap\"; ML_file \"ML/second.ML\";\n\
                section \"Context\"; ML_file \"context.ML\"; ML_file \"after.ML\";";
    area.write_source("ROOT0.ML", root0);
    area.write_source("ROOT.ML", root);
    area.write_source("ML/first.ML", "val first = 20;");
    area.write_source("ML/second.ML", "val second = first + 22;");
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    let progress = vm.evaluate_root_prefix().unwrap();
    assert_eq!(vm.lookup_value("second").unwrap().and_then(Value::as_int), Some(42));
    assert_eq!(
        progress.loaded_files.iter().map(|file| file.path.as_str()).collect::<Vec<_>>(),
        ["src/Pure/ML/first.ML", "src/Pure/ML/second.ML"]
    );
    assert_eq!(progress.next_ml_file, "src/Pure/context.ML");
    assert_eq!(progress.remaining_files, ["src/Pure/context.ML", "src/Pure/after.ML"]);
    assert_eq!(
        progress.root0_sha256,
        base16ct::lower::encode_string(&Sha256::digest(root0.as_bytes()))
    );
    assert_eq!(
        progress.root_sha256,
        base16ct::lower::encode_string(&Sha256::digest(root.as_bytes()))
    );
    assert!(vm.lookup_value("after").unwrap().is_none());
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn root_context_invalid_source_revokes_vm_and_build() {
    let area = TestArea::new();
    area.write_source("ROOT0.ML", "");
    area.write_source("ROOT.ML", "ML_file \"context.ML\";");
    fs::write(area.root().join("source/src/Pure/context.ML"), [0xff]).unwrap();
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    let lease = Rc::new(lifecycle.start_root(WorkKind::Evaluation, "Context decode").unwrap());
    let failure = vm
        .evaluate_root_with_context(
            lifecycle.clone(),
            Rc::clone(&lease),
            TrustedTheory::root("Pure", Signature::new()),
        )
        .unwrap_err();
    assert_eq!(failure.failed_source, "src/Pure/context.ML");
    assert!(vm.check_stop().is_err(), "failed handoff must stop its VM");
    assert!(lifecycle.cancellation().is_requested(), "failed handoff must cancel its build");
    drop(vm);
    assert!(Rc::try_unwrap(lease).ok().unwrap().complete().is_err());
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn root_prefix_empty_compiler_with_file_label_cannot_attest_original_source() {
    let area = TestArea::new();
    area.write_source("ROOT0.ML", "ML_file \"ML/first.ML\";");
    area.write_source("ROOT.ML", "ML_file \"context.ML\";");
    area.write_source("ML/first.ML", "val must_execute = 42;");
    let (mut vm, _lifecycle, _bridge) = build_vm(&area);
    vm.evaluate(
        "fake-loader.sml",
        r#"
        fun ML_file file =
          let val input = TextIO.openIn file;
              val _ = TextIO.inputAll input;
              val _ = TextIO.closeIn input;
              val _ = PolyML.compiler (fn () => NONE,
                [PolyML.Compiler.CPFileName file]) ();
          in () end;
    "#,
    )
    .unwrap();
    let failure =
        vm.evaluate_root_prefix().expect_err("empty compiler must not attest original source");
    assert_eq!(failure.failed_source, "src/Pure/ML/first.ML");
    assert!(
        failure.error.cause.contains("without compiling requested source"),
        "unexpected failure: {}",
        failure.error
    );
    assert!(vm.check_stop().is_err(), "mismatched compiler input must revoke this VM");
}

#[test]
fn root_prefix_rebound_loader_rejects_wrong_input_before_effect() {
    let area = TestArea::new();
    area.write_source("ROOT0.ML", "ML_file \"ML/first.ML\";");
    area.write_source("ROOT.ML", "ML_file \"context.ML\";");
    area.write_source("ML/first.ML", "val first = 20;");
    let (mut vm, _lifecycle, _bridge) = build_vm(&area);
    vm.evaluate(
        "rebound-loader.sml",
        "val original_loader = ML_file; \
        val saved = ref 0; \
        fun ML_file (n: int) = (saved := n; original_loader \"ML/first.ML\");",
    )
    .unwrap();
    let failure = vm.evaluate_root_prefix().expect_err("loader must accept a string");
    assert_eq!(failure.error.kind, isabelle_rs::ml::MlErrorKind::Type);
    vm.evaluate("rebound-state.sml", "val saved_unchanged = !saved = 0;").unwrap();
    assert_eq!(vm.lookup_value("saved_unchanged").unwrap().and_then(Value::as_bool), Some(true));
}

#[test]
fn text_io_source_stream_close_releases_stream_lease() {
    let area = TestArea::new();
    area.write_source("ML/entry.ML", "val answer = 42;");
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    vm.evaluate("stream.sml", "val s = TextIO.openIn \"ML/entry.ML\";").unwrap();
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Stream), 1);
    vm.evaluate(
        "stream.sml",
        "val text = TextIO.inputAll s; val empty = TextIO.inputAll s; TextIO.closeIn s;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("text").unwrap().and_then(Value::as_text), Some("val answer = 42;"));
    assert_eq!(vm.lookup_value("empty").unwrap().and_then(Value::as_text), Some(""));
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Stream), 0);
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn bootstrap_missing_source_raises_catchable_io_and_keeps_lease_active() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    vm.evaluate("missing.sml", "val caught = (ML_file \"missing.ML\"; 0) handle IO.Io _ => 1;")
        .unwrap();
    assert_eq!(vm.lookup_value("caught").unwrap().and_then(Value::as_int), Some(1));
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Evaluation), 1);
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn text_io_standard_output_writes_ordered_authorized_diagnostic_chunks() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    vm.evaluate(
        "stdout.sml",
        "val _ = TextIO.output (TextIO.stdOut, \"alpha\"); \
        val _ = TextIO.output (TextIO.stdErr, \"beta\"); \
        val _ = TextIO.flushOut TextIO.stdOut;",
    )
    .unwrap();
    assert_eq!(fs::read(area.root().join("staging/build/diagnostics/0.stdout")).unwrap(), b"alpha");
    assert_eq!(fs::read(area.root().join("staging/build/diagnostics/1.stderr")).unwrap(), b"beta");
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn native_sha1_bridge_sml_bytes_and_padding_boundaries_match_raw_bytes() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    let function = vm.lookup_value("Native_SHA1.digest_string").unwrap().unwrap().clone();
    for bytes in [
        (0u8..=255).collect::<Vec<u8>>(),
        vec![0, 255, 0, 255],
        vec![b'x'; 55],
        vec![b'x'; 56],
        vec![b'x'; 63],
        vec![b'x'; 64],
        vec![b'x'; 65],
    ] {
        let expected = base16ct::lower::encode_string(&Sha1::digest(&bytes));
        let result = vm.apply(&function, &[Value::bytes(bytes)]).unwrap();
        assert_eq!(result.as_text(), Some(expected.as_str()));
    }
    vm.evaluate(
        "sha1-bytes.sml",
        "val escaped = Native_SHA1.digest_string \"\\000\\255\"; \
        val utf8 = Native_SHA1.digest_string \"é\"; \
        val numeric_utf8 = Native_SHA1.digest_string \"\\195\\169\";",
    )
    .unwrap();
    assert_eq!(
        vm.lookup_value("escaped").unwrap().and_then(Value::as_text),
        Some(base16ct::lower::encode_string(&Sha1::digest([0, 255])).as_str())
    );
    assert_eq!(
        vm.lookup_value("utf8").unwrap().and_then(Value::as_text),
        vm.lookup_value("numeric_utf8").unwrap().and_then(Value::as_text)
    );
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn native_sha1_official_module_preserves_public_digest_and_hides_bridge() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    // ROOT's ml_init.ML supplies chr; library.ML supplies both helpers.
    vm.evaluate(
        "sha1-prelude.sml",
        r#"
structure FixedInt =
struct
  type int = int
  val max = Int.max
  fun fromInt value = value
  fun toInt value = value
end;
structure Unsynchronized = struct datatype ref = datatype ref end;
fun the_default default NONE = default | the_default _ (SOME value) = value;
fun quote text = "\"" ^ text ^ "\"";
val ML_system_pp = PolyML.addPrettyPrinter;
val ML_system_pretty = PolyML.prettyRepresentation;
val chr = fn n => String.str (Char.chr n);
val implode = String.concat;
fun funpow (0: int) _ x = x
  | funpow n f x = funpow (n - 1) f (f x);
fun replicate_string (0: int) _ = ""
  | replicate_string 1 a = a
  | replicate_string k a =
      if k mod 2 = 0 then replicate_string (k div 2) (a ^ a)
      else replicate_string (k div 2) (a ^ a) ^ a;
"#,
    )
    .unwrap();
    vm.evaluate(
        "src/Pure/ML/ml_pretty.ML",
        include_str!("../isabelle-source/src/Pure/ML/ml_pretty.ML"),
    )
    .unwrap();
    let source = include_str!("../isabelle-source/src/Pure/General/sha1.ML");
    let identity = vm.evaluate_native_sha1_module("src/Pure/General/sha1.ML", source).unwrap();
    assert_eq!(
        identity.source_sha256,
        base16ct::lower::encode_string(&Sha256::digest(source.as_bytes()))
    );
    assert_ne!(identity.source_sha256, identity.executable_sha256);
    assert!(vm.lookup_value("Native_SHA1.digest_string").unwrap().is_none());
    vm.evaluate(
        "sha1-public.sml",
        "val actual = SHA1.rep (SHA1.digest \"abc\"); \
        val fake = SHA1.rep (SHA1.fake \"fixture\"); SHA1.test_samples ();",
    )
    .unwrap();
    assert_eq!(
        vm.lookup_value("actual").unwrap().and_then(Value::as_text),
        Some("a9993e364706816aba3e25717850c26c9cd0d89d")
    );
    assert_eq!(vm.lookup_value("fake").unwrap().and_then(Value::as_text), Some("fixture"));
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn official_ml_name_space_builds_live_global_tables_from_native_vm() {
    let area = TestArea::new();
    let source = include_str!("../isabelle-source/src/Pure/ML/ml_name_space.ML");
    area.write_source("ML/ml_name_space.ML", source);
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    vm.register_host_type("Native_Context.probe", 0, false).unwrap();
    let loaded = vm.evaluate_source_file("src/Pure/ML/ml_name_space.ML").unwrap();
    assert_eq!(loaded.path, "src/Pure/ML/ml_name_space.ML");
    assert_eq!(loaded.sha256, base16ct::lower::encode_string(&Sha256::digest(source.as_bytes())));
    let values = vm.lookup_value("ML_Name_Space.sml_val").unwrap().unwrap();
    let values = values.as_list().unwrap();
    assert!(
        values.iter().filter_map(Value::as_tuple).any(|entry| entry[0].as_text() == Some("real"))
    );
    assert!(
        !values.iter().filter_map(Value::as_tuple).any(|entry| entry[0].as_text() == Some("use"))
    );
    assert!(vm.lookup_structure("Native_Context").unwrap().is_some());
    let structures = vm.lookup_value("ML_Name_Space.sml_structure").unwrap().unwrap();
    assert!(
        !structures
            .as_list()
            .unwrap()
            .iter()
            .filter_map(Value::as_tuple)
            .any(|entry| entry[0].as_text() == Some("Native_Context"))
    );
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn polyml_compiler_uses_original_namespace_enter_callback_for_renamed_binding() {
    let area = TestArea::new();
    area.write_source(
        "ML/ml_name_space.ML",
        include_str!("../isabelle-source/src/Pure/ML/ml_name_space.ML"),
    );
    let (mut vm, lifecycle, bridge) = build_vm(&area);
    vm.evaluate_source_file("src/Pure/ML/ml_name_space.ML").unwrap();
    vm.evaluate(
        "renamed-namespace.sml",
        "val input = ref (String.explode \"val injected = 8;\"); \
         fun get () = case !input of [] => NONE | c :: rest => (input := rest; SOME c); \
         val namespace = ML_Name_Space.global_values [(\"injected\", \"linked\")]; \
         val compiled = PolyML.compiler (get, [PolyML.Compiler.CPNameSpace namespace]); \
         val _ = compiled ();",
    )
    .unwrap();
    assert!(vm.lookup_value("injected").unwrap().is_none());
    assert_eq!(vm.lookup_value("linked").unwrap().and_then(Value::as_int), Some(8));
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}
