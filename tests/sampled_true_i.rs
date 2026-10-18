use isabelle_rs::{
    hol::sampled_true_i::compile_sampled_true_i,
    isar::source_ast::SourceId,
    kernel::{KernelRules, Term, Ty},
};

const HOL_SOURCE: &str = include_str!("../theories/HOL/HOL.thy");
const FUN_ARITY_AXIOM: &str =
    r#"axiomatization where fun_arity: "OFCLASS('a \<Rightarrow> 'b, type_class)""#;
const FUN_ARITY_INSTANCE: &str = r#"instance "fun" :: (type, type) type by (rule fun_arity)"#;

fn compile(
    source: &str,
) -> Result<isabelle_rs::theory::trusted_loader::TrustedSourceBuild, String> {
    compile_sampled_true_i(source, SourceId::new("theories/HOL/HOL.thy"))
        .map_err(|error| error.to_string())
}

fn mutate_once(original: &str, old: &str, new: &str) -> String {
    assert_eq!(original.matches(old).count(), 1, "mutation precondition");
    original.replacen(old, new, 1)
}

#[test]
fn sampled_true_i_real_hol_source_returns_replayable_exact_token() {
    let build = compile(HOL_SOURCE).expect("real HOL source must compile through the projection");
    assert_eq!(build.theorem.name().as_str(), "TrueI");
    assert!(KernelRules::theorem_ref(&build.theory, &build.theorem).is_ok());
    assert_eq!(
        build.theorem.dependencies().len(),
        4,
        "refl, True definition, bool and function arities must be replayed",
    );

    let Some((head, argument)) = build.theorem.prop().term().dest_app() else {
        panic!("TrueI proposition must be an application");
    };
    assert!(matches!(
        head,
        Term::Const { name, ty }
            if name.as_str() == "HOL.Trueprop"
                && ty == &Ty::arrow(Ty::base("bool").unwrap(), Ty::prop())
    ));
    assert!(matches!(
        argument,
        Term::Const { name, ty } if name.as_str() == "HOL.True" && ty == &Ty::base("bool").unwrap()
    ));
}

#[test]
fn sampled_true_i_unapproved_imports_are_rejected() {
    for imports in [
        "imports Pure Other Tools.Code_Generator",
        "imports Tools.Code_Generator Pure",
        "imports Pure Try0 Tools.Code_Generator Extra",
    ] {
        let source = mutate_once(HOL_SOURCE, "imports Pure Try0 Tools.Code_Generator", imports);
        assert!(compile(&source).is_err(), "{imports}");
    }
}

#[test]
fn sampled_true_i_missing_function_arity_axiom_is_rejected() {
    let source = mutate_once(HOL_SOURCE, FUN_ARITY_AXIOM, "");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_missing_function_arity_instance_is_rejected() {
    let source = mutate_once(HOL_SOURCE, FUN_ARITY_INSTANCE, "");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_function_arity_schema_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        FUN_ARITY_AXIOM,
        r#"axiomatization where fun_arity: "OFCLASS('a itself, type_class)""#,
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_function_instance_sort_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        FUN_ARITY_INSTANCE,
        r#"instance "fun" :: (type, type) itself by (rule fun_arity)"#,
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_function_instance_proof_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        FUN_ARITY_INSTANCE,
        r#"instance "fun" :: (type, type) type by (rule itself_arity)"#,
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_reordered_function_arity_is_rejected() {
    let original = format!("{FUN_ARITY_AXIOM}\n{FUN_ARITY_INSTANCE}");
    let reordered = format!("{FUN_ARITY_INSTANCE}\n{FUN_ARITY_AXIOM}");
    let source = mutate_once(HOL_SOURCE, &original, &reordered);
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_duplicate_function_arity_is_rejected() {
    for (original, duplicate) in [
        (FUN_ARITY_AXIOM, format!("{FUN_ARITY_AXIOM}\n{FUN_ARITY_AXIOM}")),
        (FUN_ARITY_INSTANCE, format!("{FUN_ARITY_INSTANCE}\n{FUN_ARITY_INSTANCE}")),
    ] {
        let source = mutate_once(HOL_SOURCE, original, &duplicate);
        assert!(compile(&source).is_err(), "{original}");
    }
}

#[test]
fn sampled_true_i_local_function_arity_is_rejected() {
    let original = format!("{FUN_ARITY_AXIOM}\n{FUN_ARITY_INSTANCE}");
    let local = format!("context begin\n{FUN_ARITY_AXIOM}\n{FUN_ARITY_INSTANCE}\nend");
    let source = mutate_once(HOL_SOURCE, &original, &local);
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_statement_is_rejected() {
    let source = mutate_once(HOL_SOURCE, "lemma TrueI: True", "lemma TrueI: False");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_fixture_source_is_not_the_sampled_hol_theory() {
    let source = r#"
theory Fixture
imports HOL
begin
lemma TrueI: True
  unfolding True_def by (rule refl)
end
"#;
    assert!(compile(source).is_err());
}

#[test]
fn sampled_true_i_changed_definition_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        r#"where "True \<equiv> ((\<lambda>x::bool. x) = (\<lambda>x. x))""#,
        r#"where "True \<equiv> ((\<lambda>x::bool. x) = (\<lambda>x. True))""#,
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_default_sort_is_rejected() {
    let source = mutate_once(HOL_SOURCE, "default_sort type", "default_sort bool");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_trueprop_schema_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        r#"judgment Trueprop :: "bool \<Rightarrow> prop""#,
        r#"judgment Trueprop :: "prop \<Rightarrow> prop""#,
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_refl_schema_is_rejected() {
    let source = mutate_once(HOL_SOURCE, r#"refl: "t = (t::'a)""#, r#"refl: "t = (s::'a)""#);
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_equality_schema_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        r#"and eq :: "['a, 'a] \<Rightarrow> bool""#,
        r#"and eq :: "[bool, bool] \<Rightarrow> bool""#,
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_changed_proof_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        "unfolding True_def by (rule refl)",
        "unfolding True_def by (rule sym)",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_related_redeclaration_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        "lemma TrueI: True",
        "definition True :: bool where \"True \\<equiv> True\"\n\nlemma TrueI: True",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_local_statement_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        "lemma TrueI: True\n  unfolding True_def by (rule refl)",
        "context begin\nlemma TrueI: True\n  unfolding True_def by (rule refl)\nend",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_unclosed_theory_scope_is_rejected() {
    let source =
        mutate_once(HOL_SOURCE, "hide_const (open) eq equal\n\nend", "hide_const (open) eq equal");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_hidden_dependencies_are_rejected() {
    for command in ["hide_const (open) True", "hide_fact (open) refl"] {
        let source = mutate_once(
            HOL_SOURCE,
            "lemma TrueI: True",
            &format!("{command}\n\nlemma TrueI: True"),
        );
        assert!(compile(&source).is_err(), "{command}");
    }
}

#[test]
fn sampled_true_i_extra_proof_method_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        "unfolding True_def by (rule refl)",
        "unfolding True_def by (rule refl) (rule missing_fact)",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_private_definition_is_rejected() {
    let source =
        mutate_once(HOL_SOURCE, "definition True :: bool", "private definition True :: bool");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_qualified_refl_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        "axiomatization where\n  refl:",
        "qualified axiomatization where\n  refl:",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_header_defined_wrapper_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        r#""quickcheck_params" :: thy_decl"#,
        r#""masked" :: thy_decl and "quickcheck_params" :: thy_decl"#,
    );
    let source = mutate_once(&source, "definition True :: bool", "masked definition True :: bool");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_rebound_input_equality_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        "notation (input)\n  eq  (infixl",
        "notation (input)\n  implies  (infixl",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_dependency_environment_mutations_are_rejected() {
    for command in [
        "hide_type (open) bool",
        "hide_const (open) HOL.Trueprop",
        "hide_const (open) HOL.eq",
        "hide_const (open) HOL.True",
        "hide_fact (open) True_def",
        "hide_fact (open) HOL.refl",
        "alias local_true_def = True_def",
        "no_notation (input) eq (infixl \\<open>=\\<close> 50)",
        "notation (input) implies (infixl \\<open>=\\<close> 50)",
        "context begin",
    ] {
        let source =
            mutate_once(HOL_SOURCE, "lemma TrueI: True", &format!("{command}\nlemma TrueI: True"));
        assert!(compile(&source).is_err(), "{command}");
    }
}

#[test]
fn sampled_true_i_trailing_proof_command_is_rejected() {
    for tail in ["sorry", "oops", "by (rule refl)", "apply (rule refl)", "unknown_garbage"] {
        let source = mutate_once(
            HOL_SOURCE,
            "unfolding True_def by (rule refl)",
            &format!("unfolding True_def by (rule refl) {tail}"),
        );
        assert!(compile(&source).is_err(), "{tail}");
    }
}

#[test]
fn sampled_true_i_renamed_required_global_is_rejected() {
    let source = mutate_once(HOL_SOURCE, "typedecl bool", "typedecl truth");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_bundled_required_definition_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        "definition True :: bool",
        "open_bundle local_truth\nbegin\ndefinition True :: bool",
    );
    let source = mutate_once(
        &source,
        r#"where "True \<equiv> ((\<lambda>x::bool. x) = (\<lambda>x. x))""#,
        "where \"True \\<equiv> ((\\<lambda>x::bool. x) = (\\<lambda>x. x))\"\nend",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_renamed_refl_axiom_is_rejected() {
    let source = mutate_once(HOL_SOURCE, r#"refl: "t = (t::'a)""#, r#"refl_alpha: "t = (t::'a)""#);
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_extra_primitive_axiom_name_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        r#"and eq :: "['a, 'a] \<Rightarrow> bool""#,
        r#"and refl :: bool and eq :: "['a, 'a] \<Rightarrow> bool""#,
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_header_alias_for_equality_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        r#"abbrevs "?<" = "\<exists>\<^sub>\<le>\<^sub>1""#,
        r#"abbrevs "=" = "\<exists>\<^sub>\<le>\<^sub>1""#,
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_quoted_equality_override_before_definition_is_rejected() {
    let source = mutate_once(
        HOL_SOURCE,
        "definition True :: bool",
        "notation (input) implies (infixl \"=\" 50)\ndefinition True :: bool",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_later_const_declaration_cannot_rebind_equality() {
    let source = mutate_once(
        HOL_SOURCE,
        "definition True :: bool",
        "consts unrelated :: bool and eq :: \"[bool, bool] => bool\"\ndefinition True :: bool",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_later_fact_binding_cannot_rebind_definition() {
    let source = mutate_once(
        HOL_SOURCE,
        "lemma TrueI: True",
        "lemmas unrelated = refl and True_def = refl\nlemma TrueI: True",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_attributed_axiom_binding_cannot_rebind_refl() {
    let source = mutate_once(
        HOL_SOURCE,
        "lemma TrueI: True",
        "axiomatization where harmless: \"True\" and refl [simp]: \"True\"\nlemma TrueI: True",
    );
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_later_default_sort_override_is_rejected() {
    let source =
        mutate_once(HOL_SOURCE, "lemma TrueI: True", "default_sort HOL.type\nlemma TrueI: True");
    assert!(compile(&source).is_err());
}

#[test]
fn sampled_true_i_quoted_binding_heads_cannot_rebind_dependencies() {
    for command in [
        "lemmas unrelated = refl and \"True_def\" = refl",
        "consts unrelated :: bool and \"True\" :: bool",
        "axiomatization where harmless: \"True\" and \"refl\" [simp]: \"True\"",
    ] {
        let source =
            mutate_once(HOL_SOURCE, "lemma TrueI: True", &format!("{command}\nlemma TrueI: True"));
        assert!(compile(&source).is_err(), "{command}");
    }
}
