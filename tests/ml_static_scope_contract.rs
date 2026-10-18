use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

fn assert_preflight_preserves_marker(setup: &str, source: &str) {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("setup.sml", setup).unwrap();
    let error = vm.evaluate("invalid.sml", source).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type, "{error}");
    vm.evaluate("observe.sml", "val observed = !marker;").unwrap();
    assert_eq!(vm.lookup_value("observed").unwrap().and_then(Value::as_int), Some(0));
}

#[test]
fn local_constrained_structure_type_error_preserves_reference() {
    assert_preflight_preserves_marker(
        "val marker = ref 0; signature E = sig end;",
        "local val _ = marker := 1;
           structure Bad : E = struct val bad = 1 + true end
         in val ok = 0 end;",
    );
}

#[test]
fn local_constrained_structure_signature_mismatch_preserves_reference() {
    assert_preflight_preserves_marker(
        "val marker = ref 0; signature S = sig val n : int end;",
        "local val _ = marker := 1;
           structure Hidden : S = struct val n = true end
         in val result = 0 end;",
    );
}

#[test]
fn structure_nested_local_type_error_preserves_reference() {
    assert_preflight_preserves_marker(
        "val marker = ref 0;",
        "structure Outer = struct
           local val _ = marker := 1 in val bad = 1 + true end
         end;",
    );
}

#[test]
fn local_constrained_structure_exports_typed_member() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "local-signature.sml",
        "signature S = sig val n : int end;
         local structure Hidden : S = struct val n = 2 end
         in val result = Hidden.n + 1 end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(3));
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
}

#[test]
fn local_nested_open_exports_value_to_enclosing_body() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "nested-local-open.sml",
        "local
           local structure Hidden = struct val n = 2 end in open Hidden end
         in val result = n + 1 end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(3));
    assert!(vm.lookup_value("n").unwrap().is_none());
}

#[test]
fn local_outer_weak_reference_retains_element_constraint() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("setup.sml", "val cell = ref [];").unwrap();
    vm.evaluate("constrain.sml", "local val _ = cell := [1] in val exported = () end;").unwrap();
    let error = vm.evaluate("wrong-type.sml", "val bad : bool list = !cell;").unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type, "{error}");
    vm.evaluate("correct-type.sml", "val result : int = List.hd (!cell);").unwrap();
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(1));
}

#[test]
fn flexible_record_generalized_selector_rejects_disconnected_result_annotation() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "row-result.sml",
            "val result = let val g = fn r => #foo r in (g {foo=true} : int) end;",
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type, "{error}");
}

#[test]
fn functor_invalid_definition_rejects_before_local_reference_effect() {
    assert_preflight_preserves_marker(
        "val marker = ref 0; signature S = sig val n : int end;",
        "local val _ = marker := 1;
           functor Broken(X:S) = struct val bad = X.n + true end
         in val result = 0 end;",
    );
}

#[test]
fn signature_invalid_private_member_rejects_before_local_reference_effect() {
    assert_preflight_preserves_marker(
        "val marker = ref 0;",
        "local val _ = marker := 1;
           signature Broken = sig val n : missing end
         in val result = 0 end;",
    );
}

#[test]
fn constrained_open_datatype_cannot_fake_exception_before_local_effect() {
    assert_preflight_preserves_marker(
        "val marker = ref 0; signature E = sig exception K end;
         structure Data = struct datatype t = K end;",
        "local val _ = marker := 1;
           structure Bad : E = struct open Data end
         in val result = 0 end;",
    );
}

#[test]
fn nested_local_exports_structure_without_exporting_private_name() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "nested-structure.sml",
        "local local structure Hidden = struct val n = 2 end
               in structure Public = Hidden end
         in val result = Public.n + 1 end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(3));
    assert!(vm.lookup_structure("Public").unwrap().is_none());
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
}

#[test]
fn weak_reference_after_raised_declaration_retains_element_constraint() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("weak-setup.sml", "val cell = ref [];").unwrap();
    let error = vm.evaluate("weak-raise.sml", "val _ = (cell := [1]; raise Div);").unwrap_err();
    assert!(matches!(error.kind, MlErrorKind::Exception(_)), "{error}");
    let error = vm.evaluate("weak-wrong.sml", "val bad : bool list = !cell;").unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type, "{error}");
    vm.evaluate("weak-correct.sml", "val good : int = List.hd (!cell);").unwrap();
    assert_eq!(vm.lookup_value("good").unwrap().and_then(Value::as_int), Some(1));
}

#[test]
fn reopened_structure_does_not_restore_stale_weak_reference_scheme() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("module-weak.sml", "structure S = struct val cell = ref [] end;").unwrap();
    vm.evaluate("module-constrain.sml", "val _ = S.cell := [1];").unwrap();
    let error = vm
        .evaluate("module-reopen.sml", "val bad : bool list = let open S in !cell end;")
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type, "{error}");
    vm.evaluate("module-read.sml", "val good = List.hd (!S.cell);").unwrap();
    assert_eq!(vm.lookup_value("good").unwrap().and_then(Value::as_int), Some(1));
}

#[test]
fn nested_local_open_exposes_value_as_structure_member() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "nested-open.sml",
        "structure Outer = struct
           local structure Hidden = struct val n = 2 end in open Hidden end
         end;
         val answer = Outer.n + 1;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(3));
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
}
