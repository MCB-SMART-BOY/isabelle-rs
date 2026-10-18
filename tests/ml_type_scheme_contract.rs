use isabelle_rs::ml::{DenyHost, MlError, MlErrorKind, Type, TypeScheme, Value, Vm};

fn identity(_vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(args[0].clone())
}

fn variable(id: u64) -> Type {
    Type::Variable(id)
}

fn identity_scheme(id: u64) -> TypeScheme {
    TypeScheme::polymorphic(
        vec![id],
        Type::Function(Box::new(variable(id)), Box::new(variable(id))),
    )
}

fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_int).expect("integer value")
}

#[test]
fn scheme_host_quantified_ids_remain_polymorphic_across_evaluations() {
    let mut vm = Vm::new(DenyHost);
    for (name, id) in [("host_a", 2), ("host_b", 3), ("host_max", u64::MAX)] {
        vm.register_native(name, identity_scheme(id), identity).expect("register native identity");
    }
    vm.evaluate("host-quantified-a.sml", "val first = host_a 13; val second = host_b true;")
        .expect("independent host schemes");
    vm.evaluate("host-quantified-b.sml", "val third = host_a true; val fourth = host_max 17;")
        .expect("later inference must not capture host quantified ids");
    vm.evaluate("host-quantified-c.sml", "val fifth = host_max false; val sixth = host_b 23;")
        .expect("host schemes remain polymorphic");
    assert_eq!(integer(&vm, "first"), 13);
    assert_eq!(integer(&vm, "fourth"), 17);
    assert_eq!(integer(&vm, "sixth"), 23);
    assert_eq!(vm.lookup_value("fifth").unwrap().and_then(Value::as_bool), Some(false));
}

#[test]
fn scheme_generalization_preserves_constructor_polymorphism() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "constructor-generalization.sml",
        "val first = SOME 1; \
        val mapped = List.map (fn x => true) [1]; \
        val option = SOME []; \
        val ints = Option.getOpt (option, [1]); \
        val bools = Option.getOpt (option, [true]); \
        val count = List.length bools; val map_count = List.length mapped;",
    )
    .expect("constructor application is nonexpansive, unlike ordinary calls");
    assert_eq!(integer(&vm, "count"), 0);
    assert_eq!(integer(&vm, "map_count"), 1);
}

#[test]
fn scheme_let_scope_preserves_fresh_ids_for_sibling_expressions() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("let-fresh.sml", "val (xs, _) = (let in [] end, SOME 1); val ys = true :: xs;")
        .expect("independent list and option type variables");
    assert!(vm.lookup_value("ys").unwrap().is_some());
}

#[test]
fn scheme_signature_hidden_constructor_has_ordinary_value_restriction() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "hidden-constructor-restriction.sml",
            "signature S = sig val SOME : 'a -> 'a option end; \
         structure A : S = Option; open A; \
         val wrapped = SOME []; \
         val ints = Option.getOpt (wrapped, [1]); \
         val bools = Option.getOpt (wrapped, [true]);",
        )
        .expect_err("a signature val spec erases constructor status");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn scheme_exception_replication_rejects_ordinary_value_alias() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate("exception-replication.sml", "exception E; val e = E; exception F = e;")
        .expect_err("replication requires exception-constructor identifier status");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn scheme_exception_replication_preserves_original_identity() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "exception-replication-valid.sml",
        "exception E; exception F = E; val result = (raise E) handle F => 1;",
    )
    .expect("exception constructor replication preserves identity");
    assert_eq!(integer(&vm, "result"), 1);
}

#[test]
fn scheme_signature_exception_rejects_plain_value_alias() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "exception-signature.sml",
            "signature E = sig exception Boom end; \
         structure S : E = struct exception Real; val Boom = Real end;",
        )
        .expect_err("exception specs require constructor status, not exn-typed values");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn scheme_hidden_exception_cannot_be_replicated_through_val_spec() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "hidden-exception.sml",
            "signature V = sig val E : exn end; \
         structure S : V = struct exception E end; \
         exception F = S.E;",
        )
        .expect_err("signature val hides the exception-constructor identifier status");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn scheme_constructor_value_alias_remains_expansive() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "constructor-alias.sml",
            "val result = let \
        val make = SOME val s = make [] \
        in (Option.getOpt (s, [1]), Option.getOpt (s, [true])) end;",
        )
        .expect_err("a val-bound alias has ordinary value identifier status");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn scheme_host_free_variable_remains_weak_across_registrations() {
    let mut vm = Vm::new(DenyHost);
    let weak = TypeScheme::mono(Type::Function(Box::new(variable(3)), Box::new(variable(3))));
    vm.register_native("weak_a", weak.clone(), identity).expect("register first weak value");
    vm.register_native("weak_b", weak, identity).expect("register shared weak value");
    vm.evaluate("weak-first.sml", "val first = weak_a 7;").expect("initial weak constraint");
    let error = vm
        .evaluate("weak-second.sml", "val wrong = weak_b true;")
        .expect_err("shared unquantified variable cannot change type");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn scheme_ref_value_restriction_and_function_equality_reject_invalid_types() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("ref-first.sml", "val box = ref []; val _ = box := [1];")
        .expect("first mutation fixes the weak element type");
    let error = vm
        .evaluate("ref-second.sml", "val _ = box := [true];")
        .expect_err("weak ref element must not generalize");
    assert_eq!(error.kind, MlErrorKind::Type);
    let error = vm
        .evaluate("function-equality.sml", "val bad = (fn x => x) = (fn y => y);")
        .expect_err("functions do not admit equality");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn scheme_replicated_ref_application_preserves_weak_element_type() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "replicated-ref-first.sml",
        "structure Refs = struct datatype alias = datatype ref end; \
         val cell = Refs.ref []; val _ = cell := [1];",
    )
    .expect("replicated ref constructor preserves reference behavior");
    let error = vm
        .evaluate("replicated-ref-second.sml", "val _ = cell := [true];")
        .expect_err("replicated ref application must not generalize its element type");
    assert_eq!(error.kind, MlErrorKind::Type);
}
