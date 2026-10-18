use std::{
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use isabelle_rs::{
    core::types::Typ,
    theory::{loader::TheoryProcessor, session_builder::SessionBuilder},
};

// Only allocates unique temporary paths; it carries no theory or test state.
static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TheoryDirectory(PathBuf);

impl TheoryDirectory {
    fn create() -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir()
            .join(format!("isabelle-load-contract-{}-{sequence}", std::process::id()));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, file: &str, source: &str) -> PathBuf {
        let path = self.0.join(file);
        std::fs::write(&path, source).unwrap();
        path
    }

    fn path(&self) -> &Path {
        &self.0
    }

    fn scan(&self) -> SessionBuilder {
        let mut builder = SessionBuilder::new();
        builder.scan(self.path()).unwrap();
        builder.resolve_dependencies();
        builder
    }
}

impl Drop for TheoryDirectory {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn process_file_missing_header_returns_error() {
    let directory = TheoryDirectory::create();
    let path = directory.write("Header.thy", "end");
    assert!(TheoryProcessor::process_file(&path).is_err());
}

#[test]
fn process_file_missing_end_returns_error() {
    let directory = TheoryDirectory::create();
    let path = directory.write("MissingEnd.thy", "theory MissingEnd imports Pure begin");
    assert!(TheoryProcessor::process_file(&path).is_err());
}

#[test]
fn process_file_missing_import_returns_error() {
    let directory = TheoryDirectory::create();
    let path =
        directory.write("MissingImport.thy", "theory MissingImport imports Absent begin end");
    assert!(TheoryProcessor::process_file(&path).is_err());
}

#[test]
fn process_file_typedecl_persists_in_signature() {
    let directory = TheoryDirectory::create();
    let path = directory.write("D.thy", "theory D imports Pure begin typedecl audit_type end");
    let theory = TheoryProcessor::process_file(&path).unwrap();
    assert!(theory.signature().certify_type(&Typ::base("audit_type")).is_ok());
    assert!(theory.lookup_theorem("audit_type.type").is_none());
}

#[test]
fn build_mixed_invalid_files_registers_only_complete_theory() {
    let directory = TheoryDirectory::create();
    directory.write("T.thy", "theory T imports Missing begin end");
    directory.write("U.thy", "theory U imports Pure begin");
    directory.write("D.thy", "theory D imports Pure begin typedecl audit_type end");
    let mut builder = directory.scan();
    let result = builder.build();
    assert_eq!((result.total, result.loaded, result.failed), (3, 1, 2));
    assert!(!result.is_success());
    assert!(builder.registry().lookup("T").is_none());
    assert!(builder.registry().lookup("U").is_none());
    let theory = builder.registry().lookup("D").unwrap();
    assert!(theory.signature().certify_type(&Typ::base("audit_type")).is_ok());
}

#[test]
fn build_cycle_and_dependents_fail_without_blocking_independent_theory() {
    let directory = TheoryDirectory::create();
    directory.write("A.thy", "theory A imports B begin end");
    directory.write("B.thy", "theory B imports A begin end");
    directory.write("C.thy", "theory C imports A begin end");
    directory.write("D.thy", "theory D imports Pure begin end");
    let mut builder = directory.scan();
    let result = builder.build();
    assert_eq!((result.total, result.loaded, result.failed), (4, 1, 3));
    assert_eq!(result.theory_names, ["D"]);
    for name in ["A", "B", "C"] {
        assert!(builder.registry().lookup(name).is_none());
    }
}

const IDENTITY_SOURCE: &str = r#"theory Identity imports Pure begin
lemma identity: "!!x::prop. x ==> x"
proof
  fix x::prop
  assume "x::prop"
  show "x::prop" by assumption
qed
end"#;

#[test]
fn process_source_checked_scoped_identity_publishes_exact_closed_theorem() {
    let mut processor = TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
    let theory = processor.process_source(IDENTITY_SOURCE).unwrap();
    let theorem = theory.lookup_theorem("identity").unwrap();
    let expected = isabelle_rs::isar::term_parser::parse_term("!!x::prop. x ==> x").unwrap();
    assert!(theorem.is_strict_closed_proved());
    assert_eq!(theorem.prop().term(), &expected);
    assert_eq!(processor.closed_theorem_count(), 1);
}

#[test]
fn process_source_second_lemma_resolves_first_lemma_in_its_transaction() {
    let source = IDENTITY_SOURCE
        .replace("\nend", "\nlemma identity_again: \"!!x::prop. x ==> x\" by (rule identity)\nend");
    let mut processor = TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
    let theory = processor.process_source(&source).unwrap();
    let first = theory.lookup_theorem("identity").unwrap();
    let second = theory.lookup_theorem("identity_again").unwrap();
    assert!(second.is_strict_closed_proved());
    assert_eq!(second.prop(), first.prop());
    assert_eq!(processor.closed_theorem_count(), 2);
}

#[test]
fn process_source_failure_after_proved_lemma_discards_all_staged_results() {
    let source = IDENTITY_SOURCE.replace("\nend", "\nconsts unsupported :: prop\nend");
    let mut processor = TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
    assert!(processor.process_source(&source).is_err());
    assert_eq!(processor.lemma_count, 1);
    assert_eq!(processor.theorem_count(), 0);
    assert_eq!(processor.indexed_theorem_count(), 0);
    assert!(processor.lookup_theorem("identity").is_none());
    assert!(matches!(processor.process_source(IDENTITY_SOURCE),
        Err(errors) if matches!(errors.as_slice(), [isabelle_rs::theory::loader::TheoryLoadError::TransactionConsumed])));
}

#[test]
fn process_source_unimplemented_commands_never_publish_partial_theory() {
    for command in [
        "definition x where \"x = x\"",
        "axiomatization x::prop",
        "ML \"()\"",
        "consts x::prop",
        "datatype x = X",
        "locale L",
        "setup \"x\"",
        "lemma unfinished: \"!!x::prop. x ==> x\"",
        "qed",
        "sorry",
    ] {
        let source = format!("theory Rejected imports Pure begin {command} end");
        let mut processor =
            TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
        assert!(processor.process_source(&source).is_err(), "{command}");
        assert_eq!(processor.theorem_count(), 0);
    }
}

#[test]
fn process_source_trailing_and_malformed_lexical_input_is_rejected() {
    for suffix in
        ["; garbage", " orphan", " end", " (* unclosed", " \"unterminated", " typedecl after_end"]
    {
        let source = format!("theory Rejected imports Pure begin end{suffix}");
        let mut processor =
            TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
        assert!(processor.process_source(&source).is_err(), "{suffix}");
    }
}

#[test]
fn process_source_end_argument_discards_staged_theorems() {
    let source = format!("{IDENTITY_SOURCE}?");
    let mut processor = TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
    let errors = processor.process_source(&source).unwrap_err();
    assert!(matches!(
        errors.as_slice(),
        [isabelle_rs::theory::loader::TheoryLoadError::UnexpectedCommand { command, .. }]
            if command == "end"
    ));
    assert_eq!(processor.lemma_count, 1);
    assert_eq!(processor.theorem_count(), 0);
    assert_eq!(processor.indexed_theorem_count(), 0);
    assert!(processor.lookup_theorem("identity").is_none());
}

#[test]
fn process_source_comments_and_document_strings_preserve_command_boundaries() {
    let source = "(* header (* nested *) *) theory Document imports Pure begin
        text \"end lemma qed\" (* gap *) typedecl 'a item end (* legal trailing *)";
    let mut processor = TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
    let theory = processor.process_source(source).unwrap();
    assert!(theory.signature().certify_type(&Typ::apply("item", vec![Typ::base("prop")],)).is_ok());
    assert_eq!(processor.theorem_count(), 0);
}

#[test]
fn process_source_duplicate_and_malformed_types_are_rejected() {
    for body in [
        "typedecl prop",
        "typedecl item typedecl item",
        "typedecl 'a 'a item",
        "typedecl item trailing",
    ] {
        let mut processor =
            TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
        assert!(
            processor
                .process_source(&format!("theory Types imports Pure begin {body} end"))
                .is_err(),
            "{body}"
        );
    }
}

#[test]
fn process_source_conflicting_nested_annotation_rejects_complete_proof() {
    let source = IDENTITY_SOURCE.replace("assume \"x::prop\"", "assume \"((x::nat)::prop)\"");
    let mut processor = TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
    assert!(processor.process_source(&source).is_err());
    assert_eq!(processor.theorem_count(), 0);
    assert!(processor.lookup_theorem("identity").is_none());
}

#[test]
fn process_source_empty_type_variable_rejects_declaration() {
    for parameter in ["'", "''"] {
        let mut processor =
            TheoryProcessor::new(isabelle_rs::theory::registry::TheoryRegistry::new());
        let source = format!("theory Invalid imports Pure begin typedecl {parameter} item end");
        assert!(processor.process_source(&source).is_err(), "{parameter}");
    }
}
