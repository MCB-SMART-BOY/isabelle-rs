use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use isabelle_rs::ml::host::files::{EffectSet, HostRoots, PhaseEffects, RestrictedHost};
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, TaskLease, WorkKind};
use isabelle_rs::ml::{DenyHost, Vm};
use isabelle_rs::theory::native::source::{NATIVE_ROOTS, NativeSourceGraph, SourceGraphError};
use sha2::{Digest, Sha256};

static NEXT_AREA: AtomicU64 = AtomicU64::new(0);

struct TestArea(PathBuf);

impl TestArea {
    fn new() -> Self {
        let id = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("native-source-{}-{id}", std::process::id()));
        fs::create_dir(&path).unwrap();
        fs::create_dir(path.join("source")).unwrap();
        fs::create_dir(path.join("staging")).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, source: &str) {
        let path = self.0.join("source").join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

    fn host(&self) -> (Vm, TaskLease, RestrictedHost) {
        self.host_at(self.0.join("source"))
    }

    fn host_at(&self, source: PathBuf) -> (Vm, TaskLease, RestrictedHost) {
        let vm = Vm::new(DenyHost);
        let lifecycle = BuildLifecycle::new(vm.stop_handle());
        let lease = lifecycle.start_root(WorkKind::Evaluation, "native source graph test").unwrap();
        let grant = EffectSet { read_source: true, ..EffectSet::default() };
        let roots = HostRoots {
            source,
            resources: BTreeMap::new(),
            staging_parent: self.0.join("staging"),
            staging_name: PathBuf::from("private"),
        };
        let host = RestrictedHost::new(
            lifecycle,
            &lease,
            roots,
            grant.clone(),
            grant.clone(),
            PhaseEffects { active: grant.clone(), draining: grant },
            BTreeMap::new(),
        )
        .unwrap();
        (vm, lease, host)
    }
}

impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn source_graph_diamond_preserves_import_order_and_exact_bytes() {
    let area = TestArea::new();
    area.write("src/HOL/Root.thy", "theory Root imports Left Right begin\nend\n");
    area.write("src/HOL/Left.thy", "theory Left imports Shared begin\nend\n");
    area.write("src/HOL/Right.thy", "theory Right imports Shared begin\nend\n");
    area.write("src/HOL/Shared.thy", "theory Shared imports Pure begin\nend\n");
    area.write("src/Pure/Pure.thy", "theory Pure begin\nend\n");
    let (_vm, lease, host) = area.host();
    let graph = NativeSourceGraph::load(&host, &lease, &["HOL.Root"]).unwrap();
    let names: Vec<_> = graph.theories().iter().map(|theory| theory.name.as_str()).collect();
    assert_eq!(names, ["Pure", "HOL.Shared", "HOL.Left", "HOL.Right", "HOL.Root"]);
    let root = graph.theories().last().unwrap();
    assert_eq!(root.parents, ["HOL.Left", "HOL.Right"]);
    assert_eq!(root.header.imports, ["Left", "Right"]);
    assert_eq!(root.bytes(), root.text().as_bytes());
    assert_eq!(root.sha256, base16ct::lower::encode_string(&Sha256::digest(root.bytes())));
    area.write("src/HOL/Root.thy", "theory Root begin\nchanged\n");
    assert_eq!(root.text(), "theory Root imports Left Right begin\nend\n");
    assert_eq!(root.sha256, base16ct::lower::encode_string(&Sha256::digest(root.bytes())));
}

#[test]
fn source_graph_missing_import_is_typed_failure() {
    let area = TestArea::new();
    area.write("src/HOL/Root.thy", "theory Root imports Missing begin");
    let (_vm, lease, host) = area.host();
    let error = NativeSourceGraph::load(&host, &lease, &["HOL.Root"]).unwrap_err();
    assert!(matches!(error, SourceGraphError::Missing { name, path, .. }
        if name == "HOL.Missing" && path == Path::new("src/HOL/Missing.thy")));
}

#[test]
fn source_graph_cycle_reports_import_chain() {
    let area = TestArea::new();
    area.write("src/HOL/A.thy", "theory A imports B begin");
    area.write("src/HOL/B.thy", "theory B imports A begin");
    let (_vm, lease, host) = area.host();
    let error = NativeSourceGraph::load(&host, &lease, &["HOL.A"]).unwrap_err();
    assert!(matches!(error, SourceGraphError::Cycle { chain }
        if chain == ["HOL.A", "HOL.B", "HOL.A"]));
}

#[test]
fn source_graph_long_import_chain_preserves_topological_order() {
    const CHAIN_LENGTH: usize = 2048;
    let area = TestArea::new();
    area.write("src/Pure/Pure.thy", "theory Pure begin end");
    for index in 0..CHAIN_LENGTH {
        let parent =
            if index + 1 == CHAIN_LENGTH { "Pure".to_owned() } else { format!("A{}", index + 1) };
        area.write(
            &format!("src/HOL/A{index}.thy"),
            &format!("theory A{index} imports {parent} begin end"),
        );
    }
    let (_vm, lease, host) = area.host();
    let graph = NativeSourceGraph::load(&host, &lease, &["HOL.A0"]).unwrap();
    let expected: Vec<_> = std::iter::once("Pure".to_owned())
        .chain((0..CHAIN_LENGTH).rev().map(|index| format!("HOL.A{index}")))
        .collect();
    assert_eq!(
        graph.theories().iter().map(|theory| &theory.name).collect::<Vec<_>>(),
        expected.iter().collect::<Vec<_>>(),
    );
}

#[test]
fn source_graph_import_path_aliases_reuse_one_source_node() {
    let area = TestArea::new();
    area.write("src/HOL/Root.thy", r#"theory Root imports Shared "./Shared" HOL.Shared begin"#);
    area.write("src/HOL/Shared.thy", "theory Shared begin");
    let (_vm, lease, host) = area.host();
    let graph = NativeSourceGraph::load(&host, &lease, &["HOL.Root"]).unwrap();
    let names: Vec<_> = graph.theories().iter().map(|theory| theory.name.as_str()).collect();
    assert_eq!(names, ["HOL.Shared", "HOL.Root"]);
    assert_eq!(graph.theories()[1].parents, ["HOL.Shared", "HOL.Shared", "HOL.Shared"]);
}

#[test]
fn source_graph_aliased_self_import_reports_cycle() {
    let area = TestArea::new();
    area.write("src/HOL/Root.thy", r#"theory Root imports "./Root" begin"#);
    let (_vm, lease, host) = area.host();
    assert!(matches!(
        NativeSourceGraph::load(&host, &lease, &["HOL.Root"]),
        Err(SourceGraphError::Cycle { chain }) if chain == ["HOL.Root", "HOL.Root"],
    ));
}

#[test]
fn source_graph_duplicate_qualified_name_from_different_paths_rejected() {
    let area = TestArea::new();
    area.write("src/HOL/Root.thy", "theory Root imports \"Sub/Shared\" Shared begin");
    area.write("src/HOL/Sub/Shared.thy", "theory Shared begin");
    area.write("src/HOL/Shared.thy", "theory Shared begin");
    let (_vm, lease, host) = area.host();
    let error = NativeSourceGraph::load(&host, &lease, &["HOL.Root"]).unwrap_err();
    assert!(matches!(error, SourceGraphError::Conflict { name, first, second }
        if name == "HOL.Shared" && first == Path::new("src/HOL/Sub/Shared.thy")
            && second == Path::new("src/HOL/Shared.thy")));
}

#[test]
fn source_graph_traversal_outside_session_rejected_before_read() {
    let area = TestArea::new();
    area.write("src/HOL/Root.thy", "theory Root imports \"../../other/Bad\" begin");
    let (_vm, lease, host) = area.host();
    let error = NativeSourceGraph::load(&host, &lease, &["HOL.Root"]).unwrap_err();
    assert!(matches!(error, SourceGraphError::Escape { from, import }
        if from == "HOL.Root" && import == "../../other/Bad"));
}

#[test]
fn source_graph_declared_name_mismatch_rejected() {
    let area = TestArea::new();
    area.write("src/HOL/Root.thy", "theory Other begin");
    let (_vm, lease, host) = area.host();
    assert!(matches!(NativeSourceGraph::load(&host, &lease, &["HOL.Root"]),
        Err(SourceGraphError::HeaderName { name, declared, .. })
            if name == "HOL.Root" && declared == "Other"));
}

#[test]
fn source_graph_unapproved_session_rejected_before_source_read() {
    let area = TestArea::new();
    let (_vm, lease, host) = area.host();
    assert!(matches!(NativeSourceGraph::load(&host, &lease, &["Other.Root"]),
        Err(SourceGraphError::InvalidName { name }) if name == "Other.Root"));
}

#[test]
fn source_graph_empty_roots_rejected() {
    let area = TestArea::new();
    let (_vm, lease, host) = area.host();
    assert!(matches!(
        NativeSourceGraph::load(&host, &lease, &[]),
        Err(SourceGraphError::EmptyRoots)
    ));
}

#[test]
fn source_graph_symlink_import_is_never_followed() {
    let area = TestArea::new();
    area.write("src/HOL/Root.thy", "theory Root imports Escape begin");
    area.write("src/Pure/Pure.thy", "theory Escape begin");
    std::os::unix::fs::symlink(
        area.0.join("source/src/Pure/Pure.thy"),
        area.0.join("source/src/HOL/Escape.thy"),
    )
    .unwrap();
    let (_vm, lease, host) = area.host();
    assert!(matches!(NativeSourceGraph::load(&host, &lease, &["HOL.Root"]),
        Err(SourceGraphError::Read { name, .. }) if name == "HOL.Escape"));
}

#[test]
fn source_graph_fixed_source_smoke_is_live_and_unique() {
    let area = TestArea::new();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("isabelle-source");
    let (_vm, lease, host) = area.host_at(source);
    let graph = NativeSourceGraph::load_fixed(&host, &lease).unwrap();
    assert_eq!(graph.roots().iter().map(String::as_str).collect::<Vec<_>>(), NATIVE_ROOTS);
    let names: BTreeSet<_> = graph.theories().iter().map(|theory| theory.name.as_str()).collect();
    assert_eq!(names.len(), graph.theories().len());
    assert!(names.contains("Pure"));
    assert!(names.contains("Tools.Code_Generator"));
    for root in NATIVE_ROOTS {
        assert!(names.contains(root));
    }
    for theory in graph.theories() {
        assert_eq!(theory.sha256, base16ct::lower::encode_string(&Sha256::digest(theory.bytes())));
        for parent in &theory.parents {
            assert!(names.contains(parent.as_str()));
        }
    }
}
