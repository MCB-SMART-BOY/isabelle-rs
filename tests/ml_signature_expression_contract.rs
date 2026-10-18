use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

#[test]
fn signature_inline_nested_structure_resolves_enclosing_abstract_type() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "nested-signature.sml",
        r#"
        signature OUTER = sig
          type t
          structure Inner: sig val value: t end
        end;
        structure Outer: OUTER = struct
          type t = int
          structure Inner = struct val value = 42 end
        end;
        val answer = Outer.Inner.value + 1;
    "#,
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(43));
}

#[test]
fn signature_inline_functor_and_result_enforce_public_surface() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "inline-functor.sml",
        r#"
        functor Copy(X: sig type t val value: t end): sig type t val value: t end =
        struct type t = X.t val value = X.value val private_value = 99 end;
        structure Result = Copy(struct type t = int val value = 7 end);
        val answer = Result.value + 1;
    "#,
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(8));
    assert!(vm.lookup_value("Result.private_value").unwrap().is_none());
}

#[test]
fn signature_inline_invalid_value_rejects_before_effects() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("marker.sml", "val marker = ref 0;").unwrap();
    let error = vm
        .evaluate(
            "invalid-signature.sml",
            r#"
        structure Invalid: sig val value: bool end =
        struct val _ = marker := 1 val value = 7 end;
    "#,
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("read-marker.sml", "val answer = !marker;").unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(0));
}
