use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

#[test]
fn function_result_annotation_checks_curried_and_function_results() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "annotated-functions.sml",
        r#"
        type state = {stage: int};
        fun make_state () : state = {stage = 4};
        fun add x y : int = x + y;
        fun offset x : int -> int = fn y => x + y;
        val answer = add (#stage (make_state ())) (offset 5 6);
    "#,
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(15));
}

#[test]
fn function_result_annotation_conflicting_clause_rejects_before_effects() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("marker.sml", "val marker = ref 0;").unwrap();
    let error = vm
        .evaluate(
            "invalid-annotation.sml",
            r#"
        structure Invalid = struct
          val _ = marker := 1
          fun choose 0 : int = 1 | choose n : bool = true
        end;
    "#,
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("read-marker.sml", "val answer = !marker;").unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(0));
}

#[test]
fn function_result_annotation_infix_clause_constrains_body() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "infix-result.sml",
        r#"
        infix 6 plus;
        fun (x plus y) : int = x + y;
        val answer = 2 plus 3;
    "#,
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(5));
}
