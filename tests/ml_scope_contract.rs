use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

#[test]
fn ml_struct_shadowed_value_is_exported() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("struct-shadow.sml", "val x = 1; structure S = struct val x = 2 end;").unwrap();
    assert_eq!(
        vm.lookup_structure("S").unwrap().unwrap().lookup_value("x").and_then(Value::as_int),
        Some(2)
    );
    assert_eq!(vm.lookup_value("x").unwrap().and_then(Value::as_int), Some(1));
}

#[test]
fn ml_struct_exception_restores_private_signature_environment() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("outer.sml", "exception Oops;").unwrap();
    let error = vm
        .evaluate(
            "struct-leak.sml",
            "structure Bad = struct signature Leaked = sig end; val fail = raise Oops end;",
        )
        .unwrap_err();
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
    assert!(vm.lookup_signature("Leaked").unwrap().is_none());
    assert!(vm.lookup_structure("Bad").unwrap().is_none());
}

#[test]
fn ml_functor_uses_definition_site_types_after_different_type_rebinding() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "functor-types.sml",
        "val seed = 2; signature E = sig end;
        functor F(X:E) = struct val result = seed + 1 end;
        val seed = true; signature E = sig val demanded : int end;
        structure A = struct end; structure Out = F(A);",
    )
    .unwrap();
    assert_eq!(
        vm.lookup_structure("Out").unwrap().unwrap().lookup_value("result").and_then(Value::as_int),
        Some(3)
    );
    assert_eq!(vm.lookup_value("seed").unwrap().and_then(Value::as_bool), Some(true));
}

#[test]
fn ml_local_open_exports_usable_value_and_type() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "local-open.sml",
        "local structure Hidden = struct val n = 2 end in open Hidden end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("n").unwrap().and_then(Value::as_int), Some(2));
    vm.evaluate("use-open.sml", "val answer = n + 1;").unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(3));
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
}

#[test]
fn ml_local_structure_members_are_inferred_before_any_local_effect() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("setup.sml", "val marker = ref 0;").unwrap();
    vm.evaluate(
        "local-structure-valid.sml",
        "local structure Hidden = struct val n = 2 end
         in val result = Hidden.n + 1 end;",
    )
    .expect("private structure member remains available while elaborating local body");
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(3));
    let error = vm
        .evaluate(
            "local-structure-invalid.sml",
            "local val _ = marker := 1;
         structure Hidden = struct val n = 2 end
         in val bad = Hidden.n + true end;",
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("observe.sml", "val observed = !marker;").unwrap();
    assert_eq!(vm.lookup_value("observed").unwrap().and_then(Value::as_int), Some(0));
}

#[test]
fn ml_local_structure_open_member_is_available_during_elaboration() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "local-open-member.sml",
        "local structure Outer = struct
           structure Inner = struct val n = 4 end;
           open Inner
         end in val result = Outer.n + Outer.Inner.n end;",
    )
    .expect("nested open exports bare and qualified module members");
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(8));
}

#[test]
fn ml_exported_closure_private_exception_does_not_catch_another_exception() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "exception-scope.sml",
        "exception Other;
        local exception Hidden in
          fun f () = (raise Other) handle Hidden => 1 | Other => 2
        end; val answer = f ();",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(2));
    assert!(vm.lookup_value("Hidden").unwrap().is_none());
}

#[test]
fn ml_nested_struct_rebinding_exports_declared_values_and_substructures() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "nested-struct.sml",
        "val x = 1; structure Child = struct val n = 1 end;
         structure Outer = struct
           val x = 2; structure Child = struct val n = 3 end;
           structure Inner = struct val y = 4 end; open Inner
         end;",
    )
    .unwrap();
    let outer = vm.lookup_structure("Outer").unwrap().unwrap();
    assert_eq!(outer.lookup_value("x").and_then(Value::as_int), Some(2));
    assert_eq!(outer.lookup_value("y").and_then(Value::as_int), Some(4));
    assert_eq!(
        outer.lookup_structure("Child").unwrap().lookup_value("n").and_then(Value::as_int),
        Some(3),
    );
    assert_eq!(vm.lookup_value("x").unwrap().and_then(Value::as_int), Some(1));
    assert_eq!(
        vm.lookup_structure("Child").unwrap().unwrap().lookup_value("n").and_then(Value::as_int),
        Some(1),
    );
    assert!(vm.lookup_structure("Inner").unwrap().is_none());
}

#[test]
fn ml_let_exception_restores_modules_types_and_preserves_reference_effects() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("let-setup.sml", "val cell = ref 1; exception Boom;").unwrap();
    let error = vm
        .evaluate(
            "let-failure.sml",
            "val discarded = let
           signature Private = sig end;
           structure Hidden = struct val n = 7 end;
           type secret = int;
           val _ = cell := 3;
           val _ = raise Boom
         in 0 end;",
        )
        .unwrap_err();
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
    assert!(vm.lookup_signature("Private").unwrap().is_none());
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
    assert!(vm.lookup_value("discarded").unwrap().is_none());
    assert_eq!(
        vm.evaluate("let-after.sml", "val leaked = (1 : secret);").unwrap_err().kind,
        MlErrorKind::Type,
    );
    vm.evaluate("let-effect.sml", "val answer = !cell;").unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(3));
}

#[test]
fn ml_local_open_exports_datatype_constructor_and_annotation() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "local-datatype.sml",
        "local structure Hidden = struct datatype token = Token end
         in open Hidden end;
         val answer = case (Token : token) of Token => 1;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(1));
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
}

#[test]
fn ml_let_success_keeps_local_modules_private() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "let-success.sml",
        "val answer = let signature Private = sig end;
           structure Hidden = struct val n = 9 end
         in 5 end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(5));
    assert!(vm.lookup_signature("Private").unwrap().is_none());
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
}

#[test]
fn ml_struct_nested_local_open_exports_only_public_bindings() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "nested-local-struct.sml",
        "structure Outer = struct
           local structure Hidden = struct val n = 6 end
           in open Hidden end
         end;
         val answer = Outer.n + 1;",
    )
    .unwrap();
    assert_eq!(
        vm.lookup_structure("Outer").unwrap().unwrap().lookup_value("n").and_then(Value::as_int),
        Some(6),
    );
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(7));
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
}
