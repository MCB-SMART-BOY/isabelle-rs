use isabelle_rs::{hol::sampled_true_i::compile_sampled_true_i, isar::source_ast::SourceId};

const HOL_SOURCE: &str = include_str!("../theories/HOL/HOL.thy");
const CLASS_SETUP: &str =
    r"setup \<open>Axclass.class_axiomatization (\<^binding>\<open>type\<close>, [])\<close>";
const BASE_SORT_SETUP: &str =
    r"setup \<open>Object_Logic.add_base_sort \<^sort>\<open>type\<close>\<close>";
const FUN_INSTANCE: &str = r#"instance "fun" :: (type, type) type by (rule fun_arity)"#;

fn reject_mutation(original: &str, replacement: &str) {
    assert_eq!(HOL_SOURCE.matches(original).count(), 1, "mutation precondition");
    let source = HOL_SOURCE.replacen(original, replacement, 1);
    let result = compile_sampled_true_i(&source, SourceId::new("mutated-HOL.thy"));
    assert!(result.is_err(), "accepted altered source: {replacement}");
}

#[test]
fn sampled_true_i_missing_class_setup_is_rejected() {
    reject_mutation(CLASS_SETUP, "");
}

#[test]
fn sampled_true_i_changed_class_name_is_rejected() {
    reject_mutation(CLASS_SETUP, &CLASS_SETUP.replace("type", "another_type"));
}

#[test]
fn sampled_true_i_nonempty_class_superclasses_are_rejected() {
    reject_mutation(CLASS_SETUP, &CLASS_SETUP.replace("[]", "[\"other_class\"]"));
}

#[test]
fn sampled_true_i_missing_object_base_sort_is_rejected() {
    reject_mutation(BASE_SORT_SETUP, "");
}

#[test]
fn sampled_true_i_changed_object_base_sort_is_rejected() {
    reject_mutation(BASE_SORT_SETUP, &BASE_SORT_SETUP.replace("type", "another_type"));
}

#[test]
fn sampled_true_i_duplicate_class_configuration_is_rejected() {
    for command in [CLASS_SETUP, BASE_SORT_SETUP] {
        reject_mutation(command, &format!("{command}\n{command}"));
    }
}

#[test]
fn sampled_true_i_reordered_class_configuration_is_rejected() {
    let original = format!("{CLASS_SETUP}\ndefault_sort type\n{BASE_SORT_SETUP}");
    reject_mutation(&original, &format!("default_sort type\n{CLASS_SETUP}\n{BASE_SORT_SETUP}"));
    reject_mutation(&original, &format!("{CLASS_SETUP}\n{BASE_SORT_SETUP}\ndefault_sort type"));
}

#[test]
fn sampled_true_i_local_class_configuration_is_rejected() {
    for command in [CLASS_SETUP, BASE_SORT_SETUP] {
        reject_mutation(command, &format!("context begin\n{command}\nend"));
    }
}

#[test]
fn sampled_true_i_function_instance_proof_suffix_is_rejected() {
    for suffix in ["oops", "sorry", "by (rule fun_arity)", "apply (rule fun_arity)"] {
        reject_mutation(FUN_INSTANCE, &format!("{FUN_INSTANCE}\n{suffix}"));
    }
}
