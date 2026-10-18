use std::{
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use isabelle_rs::{
    core::types::Typ,
    theory::{session_builder::SessionBuilder, verify_classifier::VerifyStatus},
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TheoryDirectory(PathBuf);

impl TheoryDirectory {
    fn create() -> Self {
        let index = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir()
            .join(format!("isabelle-session-contract-{}-{index}", std::process::id()));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, filename: &str, source: &str) -> PathBuf {
        let path = self.0.join(filename);
        std::fs::write(&path, source).unwrap();
        path
    }

    fn scan(&self) -> SessionBuilder {
        let mut builder = SessionBuilder::new();
        builder.scan(&self.0).unwrap();
        builder
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TheoryDirectory {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn build_missing_parent_and_cycle_only_schedule_independent_theory() {
    let dir = TheoryDirectory::create();
    dir.write("A.thy", "theory A imports B begin end");
    dir.write("B.thy", "theory B imports A begin end");
    dir.write("C.thy", "theory C imports A begin end");
    dir.write("Missing.thy", "theory Missing imports Absent begin end");
    dir.write("D.thy", "theory D imports Pure begin end");
    let mut builder = dir.scan();
    assert_eq!(builder.resolve_dependencies(), ["D"]);
    let result = builder.build();
    assert_eq!((result.total, result.loaded, result.failed), (5, 1, 4));
    assert_eq!(result.theory_names, ["D"]);
    for name in ["A", "B", "C", "Missing"] {
        assert!(builder.registry().lookup(name).is_none(), "registered {name}");
    }
    assert!(
        result.error_messages.iter().any(|msg| msg.contains("A.thy") && msg.contains("unresolved"))
    );
    assert!(
        result
            .error_messages
            .iter()
            .any(|msg| msg.contains("Missing.thy") && msg.contains("Absent"))
    );
}

#[test]
fn build_duplicate_theory_names_including_pure_reject_every_claimant() {
    let dir = TheoryDirectory::create();
    dir.write("First.thy", "theory Duplicate imports Pure begin end");
    dir.write("Second.thy", "theory Duplicate imports Pure begin end");
    dir.write("Pure.thy", "theory Pure imports Pure begin end");
    dir.write("Child.thy", "theory Child imports Duplicate begin end");
    dir.write("Valid.thy", "theory Valid imports Pure begin end");
    let mut builder = dir.scan();
    let result = builder.build();
    assert_eq!((result.total, result.loaded, result.failed), (5, 1, 4));
    assert_eq!(result.theory_names, ["Valid"]);
    assert!(builder.registry().lookup("Duplicate").is_none());
    assert!(builder.registry().lookup("Child").is_none());
    assert_eq!(builder.registry().lookup("Pure").unwrap().name(), "Pure");
    for path in ["First.thy", "Second.thy", "Pure.thy"] {
        assert!(
            result
                .error_messages
                .iter()
                .any(|error| error.contains(path) && error.contains("duplicate"))
        );
    }
}

#[test]
fn build_malformed_headers_and_unreadable_files_count_every_path() {
    let dir = TheoryDirectory::create();
    dir.write("Malformed.thy", "not a theory");
    let unreadable = dir.write("Unreadable.thy", "theory Unreadable imports Pure begin end");
    dir.write("Valid.thy", "theory Valid imports Pure begin end");
    let mut builder = dir.scan();
    std::fs::remove_file(unreadable).unwrap();
    let result = builder.build();
    assert_eq!((result.total, result.loaded, result.failed), (3, 1, 2));
    assert!(
        result
            .error_messages
            .iter()
            .any(|msg| msg.contains("Malformed.thy") && msg.contains("header"))
    );
    assert!(
        result
            .error_messages
            .iter()
            .any(|msg| msg.contains("Unreadable.thy") && msg.contains("read"))
    );
    assert!(builder.registry().lookup("Valid").is_some());
    assert!(builder.registry().lookup("Unreadable").is_none());
}

#[test]
fn build_reused_builder_rejects_corrupted_parent_and_child() {
    let dir = TheoryDirectory::create();
    let parent =
        dir.write("Parent.thy", "theory Parent imports Pure begin typedecl inherited_type end");
    dir.write("Child.thy", "theory Child imports Parent begin end");
    let mut builder = dir.scan();
    let first = builder.build();
    assert_eq!((first.total, first.loaded, first.failed), (2, 2, 0));
    let child = builder.registry().lookup("Child").unwrap();
    assert!(child.signature().certify_type(&Typ::base("inherited_type")).is_ok());
    std::fs::write(&parent, "theory Parent imports Pure begin typedecl inherited_type").unwrap();
    let second = builder.build();
    assert_eq!((second.total, second.loaded, second.failed), (2, 0, 2));
    assert!(builder.registry().lookup("Parent").is_none());
    assert!(builder.registry().lookup("Child").is_none());
    assert!(
        second.error_messages.iter().any(|msg| msg.contains("Parent.thy") && msg.contains("end"))
    );
    assert!(
        second.error_messages.iter().any(|msg| msg.contains("Child.thy") && msg.contains("Parent"))
    );
}

#[test]
fn classifier_matches_build_registry_for_runtime_failure_and_scan_failures() {
    let dir = TheoryDirectory::create();
    dir.write(
        "Parent.thy",
        "theory Parent imports Pure begin typedecl duplicate_type typedecl duplicate_type end",
    );
    dir.write("Child.thy", "theory Child imports Parent begin end");
    dir.write("Valid.thy", "theory Valid imports Pure begin typedecl valid_type end");
    dir.write("NoHeader.thy", "end");
    let mut builder = dir.scan();
    let build = builder.build();
    assert_eq!((build.total, build.loaded, build.failed), (4, 1, 3));
    let registered_after_build: Vec<_> = ["Parent", "Child", "Valid"]
        .into_iter()
        .filter(|name| builder.registry().lookup(name).is_some())
        .collect();
    let report = builder.build_with_classifier();
    assert_eq!(report.total, build.total);
    assert_eq!(registered_after_build, ["Valid"]);
    for name in ["Parent", "Child", "Valid"] {
        assert_eq!(
            builder.registry().lookup(name).is_some(),
            registered_after_build.contains(&name)
        );
    }
    assert!(
        report
            .results
            .iter()
            .any(|r| r.name == "Parent" && matches!(r.status, VerifyStatus::TypeError { .. }))
    );
    assert!(
        report
            .results
            .iter()
            .any(|r| r.name == "Child" && matches!(r.status, VerifyStatus::DependencyError { .. }))
    );
    assert!(
        report
            .results
            .iter()
            .any(|r| r.name == "Valid" && matches!(r.status, VerifyStatus::NoLemmas))
    );
    assert!(report.results.iter().any(|r| r.path.ends_with("NoHeader.thy")
        && matches!(r.status, VerifyStatus::SyntaxError { .. })));
    assert!(!report.is_success());
}

#[test]
fn classifier_missing_and_failed_imports_report_dependency_without_publishing() {
    let dir = TheoryDirectory::create();
    dir.write("Missing.thy", "theory Missing imports Absent begin end");
    dir.write(
        "Broken.thy",
        "theory Broken imports Pure begin typedecl repeated typedecl repeated end",
    );
    dir.write("Child.thy", "theory Child imports Broken begin end");
    dir.write("Malformed.thy", "not a theory");
    let mut builder = dir.scan();

    let report = builder.build_with_classifier();
    assert_eq!(report.total, 4);
    assert_eq!(report.total_theorems, 0);
    assert_eq!(report.overall_rate, 0.0);
    assert_eq!(report.counts.get("DEPEND"), Some(&2));
    assert_eq!(report.counts.get("TYPE"), Some(&1));
    assert_eq!(report.counts.get("SYNTAX"), Some(&1));
    assert!(!report.is_success());
    for name in ["Missing", "Broken", "Child"] {
        assert!(builder.registry().lookup(name).is_none(), "registered {name}");
    }
    for (name, import) in [("Missing", "Absent"), ("Child", "Broken")] {
        let result = report.results.iter().find(|row| row.name == name).unwrap();
        assert!(matches!(&result.status, VerifyStatus::DependencyError { message, attempted: 0 }
            if message.contains(import) && message.contains(name)));
        assert_eq!(result.theorem_count, 0);
        assert!(!result.status.has_verified());
    }
    assert!(report.results.iter().any(|row| row.name == "Broken"
        && matches!(row.status, VerifyStatus::TypeError { .. })));
    assert!(report.results.iter().any(
        |row| row.name == "Malformed" && matches!(row.status, VerifyStatus::SyntaxError { .. })
    ));
}

#[test]
fn scan_enumeration_error_invalidates_success_without_inventing_theories() {
    let dir = TheoryDirectory::create();
    dir.write("Valid.thy", "theory Valid imports Pure begin end");
    let mut builder = dir.scan();
    let nonexistent = dir.path().join("missing-directory");
    assert!(builder.scan(&nonexistent).is_err());
    let build = builder.build();
    assert_eq!((build.total, build.loaded, build.failed), (1, 1, 0));
    assert!(!build.is_success());
    assert!(build.scan_error.as_ref().is_some_and(|message| message.contains("missing-directory")));
    let report = builder.build_with_classifier();
    assert_eq!(report.total, 1);
    assert!(!report.is_success());
    assert!(
        report.scan_error.as_ref().is_some_and(|message| message.contains("missing-directory"))
    );
}

#[test]
fn scan_repeated_path_does_not_double_count_theory() {
    let dir = TheoryDirectory::create();
    dir.write("Once.thy", "theory Once imports Pure begin end");
    let mut builder = SessionBuilder::new();
    assert_eq!(builder.scan(dir.path()).unwrap(), 1);
    assert_eq!(builder.scan(dir.path()).unwrap(), 0);
    let result = builder.build();
    assert_eq!((result.total, result.loaded, result.failed), (1, 1, 0));
}

#[test]
fn theory_file_parse_uses_complete_multiline_header_and_rejects_invalid_headers() {
    use isabelle_rs::theory::{loader::TheoryLoadError, session_builder::TheoryFile};

    let dir = TheoryDirectory::create();
    let multiline = dir
        .write("DifferentStem.thy", "(* header *)\ntheory Actual\n  imports Parent\n  begin\nend");
    let parsed = TheoryFile::parse(&multiline).unwrap();
    assert_eq!(parsed.name, "Actual");
    assert_eq!(parsed.imports, ["Parent"]);
    let malformed = dir.write("Malformed.thy", "theory Broken imports");
    assert!(matches!(TheoryFile::parse(&malformed), Err(TheoryLoadError::Header { .. })));
}

#[test]
fn build_parentless_theory_and_its_multi_import_child_are_rejected() {
    let dir = TheoryDirectory::create();
    dir.write("Parentless.thy", "theory Parentless begin end");
    dir.write("Multi.thy", "theory Multi imports Pure Parentless begin end");
    dir.write("Independent.thy", "theory Independent imports Pure begin end");
    let mut builder = dir.scan();
    let result = builder.build();
    assert_eq!((result.total, result.loaded, result.failed), (3, 1, 2));
    assert!(builder.registry().lookup("Parentless").is_none());
    assert!(builder.registry().lookup("Multi").is_none());
    assert!(builder.registry().lookup("Independent").is_some());
}

#[test]
fn scan_invalid_utf8_file_is_a_counted_io_failure() {
    let dir = TheoryDirectory::create();
    std::fs::write(dir.path().join("Invalid.thy"), [0xff]).unwrap();
    dir.write("Valid.thy", "theory Valid imports Pure begin end");
    let mut builder = SessionBuilder::new();
    assert_eq!(builder.scan(dir.path()).unwrap(), 2);
    let result = builder.build();
    assert_eq!((result.total, result.loaded, result.failed), (2, 1, 1));
    assert!(
        result.error_messages.iter().any(|msg| msg.contains("Invalid.thy") && msg.contains("read"))
    );
    let report = builder.build_with_classifier();
    assert!(
        report
            .results
            .iter()
            .any(|row| row.name == "Invalid" && matches!(row.status, VerifyStatus::IoError { .. }))
    );
}

#[test]
fn build_multiple_imports_preserves_both_signatures_and_parent_facts() {
    let dir = TheoryDirectory::create();
    dir.write(
        "Left.thy",
        "theory Left imports Pure begin typedecl left_type
         lemma identity: \"!!x::prop. x ==> x\"
         proof fix x::prop assume \"x::prop\" show \"x::prop\" by assumption qed end",
    );
    dir.write("Right.thy", "theory Right imports Pure begin typedecl right_type end");
    dir.write(
        "Join.thy",
        "theory Join imports Left Right begin
         lemma inherited: \"!!x::prop. x ==> x\" by (rule identity) end",
    );
    let mut builder = dir.scan();
    let result = builder.build();
    assert!(result.is_success(), "{:?}", result.error_messages);
    assert_eq!((result.loaded, result.theorems), (3, 2));
    let joined = builder.registry().lookup("Join").unwrap();
    for name in ["left_type", "right_type"] {
        assert!(joined.signature().certify_type(&Typ::base(name)).is_ok());
    }
    let inherited = joined.lookup_theorem("inherited").unwrap();
    let parent = joined.lookup_theorem("identity").unwrap();
    assert!(inherited.is_strict_closed_proved());
    assert_eq!(inherited.prop(), parent.prop());
}

#[test]
fn build_diamond_and_redundant_imports_preserve_shared_declaration_identity() {
    let dir = TheoryDirectory::create();
    dir.write("Base.thy", "theory Base imports Pure begin typedecl shared_type end");
    dir.write("Left.thy", "theory Left imports Base begin typedecl left_type end");
    dir.write("Right.thy", "theory Right imports Base begin typedecl right_type end");
    dir.write("Join.thy", "theory Join imports Pure Base Left Right Left begin end");
    let mut builder = dir.scan();
    let result = builder.build();
    assert!(result.is_success(), "{:?}", result.error_messages);
    let joined = builder.registry().lookup("Join").unwrap();
    for name in ["shared_type", "left_type", "right_type"] {
        assert!(joined.signature().certify_type(&Typ::base(name)).is_ok());
    }
    assert_eq!(
        joined.parents().iter().map(|parent| parent.name()).collect::<Vec<_>>(),
        ["Left", "Right"]
    );
}

#[test]
fn build_conflicting_imports_do_not_publish_child_or_descendants() {
    let dir = TheoryDirectory::create();
    dir.write("Left.thy", "theory Left imports Pure begin typedecl collision end");
    dir.write("Right.thy", "theory Right imports Pure begin typedecl collision end");
    dir.write("Join.thy", "theory Join imports Left Right begin typedecl unpublished end");
    dir.write("Child.thy", "theory Child imports Join Left begin end");
    let mut builder = dir.scan();
    let result = builder.build();
    assert_eq!((result.loaded, result.failed), (2, 2));
    for name in ["Join", "Child"] {
        assert!(builder.registry().lookup(name).is_none());
    }
    assert!(builder.registry().lookup("Left").is_some());
    assert!(builder.registry().lookup("Right").is_some());
}

#[test]
fn build_multi_import_missing_or_failed_parent_never_falls_back_to_other_parent() {
    let dir = TheoryDirectory::create();
    dir.write("Valid.thy", "theory Valid imports Pure begin end");
    dir.write("Broken.thy", "theory Broken imports Pure begin typedecl unpublished");
    dir.write("Missing.thy", "theory Missing imports Valid Absent begin end");
    dir.write("Blocked.thy", "theory Blocked imports Valid Broken begin end");
    let mut builder = dir.scan();
    let result = builder.build();
    assert_eq!((result.loaded, result.failed), (1, 3));
    for name in ["Broken", "Missing", "Blocked"] {
        assert!(builder.registry().lookup(name).is_none());
    }
    assert_eq!(result.theory_names, ["Valid"]);
}
