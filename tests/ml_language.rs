use isabelle_rs::ml::{
    DenyHost, HostBridge, HostFailure, MlErrorKind, Type, TypeScheme, Value, Vm,
};

fn int_result(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name)
        .expect("live VM lookup must work")
        .and_then(Value::as_int)
        .expect("program must bind the named integer")
}

#[test]
fn ml_recursive_patterns_and_records_compute_result() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "rec.sml",
        "fun factorial 0 = 1 | factorial n = n * factorial (n - 1); \
        val {x = first, y = second} = {x = factorial 5, y = 3}; \
        val answer = first + second;",
    )
    .expect("valid Standard ML declarations must evaluate");
    assert_eq!(int_result(&vm, "answer"), 123);
}

#[test]
fn ml_application_unparenthesized_let_operand_evaluates() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "let-operand.sml",
        "fun increment n = n + 1; val answer = increment let val x = 41 in x end;",
    )
    .expect("let expression is an atomic argument in Standard ML");
    assert_eq!(int_result(&vm, "answer"), 42);
}

#[test]
fn ml_refs_preserve_left_to_right_updates() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "refs.sml",
        "val cell = ref 1; val _ = cell := !cell + 2; \
        val _ = cell := !cell * 3; val answer = !cell;",
    )
    .expect("reference program must evaluate");
    assert_eq!(int_result(&vm, "answer"), 9);
}

#[test]
fn ml_exception_alias_matches_original_identity_only() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "exn.sml",
        "exception Original; exception Alias = Original; \
        exception Other; val answer = (raise Original) handle Other => 0 | Alias => 19;",
    )
    .expect("exception alias must preserve constructor identity");
    assert_eq!(int_result(&vm, "answer"), 19);
}

#[test]
fn ml_equality_rejects_functions_before_evaluation() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate("bad-eq.sml", "val bad = (fn x => x) = (fn y => y);")
        .expect_err("functions cannot be compared with Standard ML equality");
    assert_eq!(error.kind, MlErrorKind::Type);
    assert!(vm.lookup_value("bad").expect("live VM lookup must work").is_none());
}

#[test]
fn ml_value_restriction_rejects_polymorphic_reference_reuse() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("weak.sml", "val cell = ref []; val _ = cell := [1];")
        .expect("first weak-variable use fixes element type");
    let error = vm
        .evaluate("weak-again.sml", "val _ = cell := [true];")
        .expect_err("value restriction must prevent polymorphic reference use");
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn ml_gc_reclaims_unreachable_reference_closure_cycle() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "cycle.sml",
        "val answer = let val cell = ref (fn x => x); \
        val _ = cell := (fn x => (!cell) x) in 7 end;",
    )
    .expect("well-typed local reference cycle must evaluate");
    assert_eq!(int_result(&vm, "answer"), 7);
    assert!(vm.collect_garbage().expect("GC should complete") >= 2);
}

#[test]
fn ml_supervisor_stop_cannot_be_handled_in_ml() {
    let mut vm = Vm::new(DenyHost);
    let stop = vm.stop_handle();
    stop.request_stop();
    let error = vm
        .evaluate("stopped.sml", "(while true do ()) handle _ => ();")
        .expect_err("supervisor cancellation must not enter ML handlers");
    assert_eq!(error.kind, MlErrorKind::Stopped);
}

#[test]
fn ml_native_and_host_ids_reject_cross_vm_use() {
    let mut first = Vm::new(DenyHost);
    let second = Vm::new(DenyHost);
    let object =
        first.insert_host_object(std::rc::Rc::new(7_i64)).expect("live VM may add host object");
    let Err(error) =
        second.get_host_object(object.as_host_object().expect("host object has private ID"))
    else {
        panic!("foreign runtime must reject same-index object");
    };
    assert_eq!(error.kind, MlErrorKind::HostFailure);
    let native = first
        .lookup_value("+")
        .expect("live VM lookup must work")
        .expect("Basis addition must exist")
        .clone();
    let mut third = Vm::new(DenyHost);
    let error =
        third.apply(&native, &[Value::unit()]).expect_err("foreign native ID must be rejected");
    assert_eq!(error.kind, MlErrorKind::HostFailure);
}

struct RecursiveHost;
impl HostBridge for RecursiveHost {
    fn invoke(&self, vm: &mut Vm, operation: &str, _: &[Value]) -> Result<Value, HostFailure> {
        match operation {
            "outer" => vm.call_host("inner", &[]).map_err(|error| HostFailure::Failed {
                operation: "outer".to_owned(),
                resource: "nested callback".to_owned(),
                cause: error.to_string(),
            }),
            "inner" => Ok(Value::int(31)),
            _ => Err(HostFailure::Permission {
                operation: operation.to_owned(),
                resource: "unknown operation".to_owned(),
                cause: "not granted".to_owned(),
            }),
        }
    }
}
fn fetch_from_host(vm: &mut Vm, _: &[Value]) -> Result<Value, isabelle_rs::ml::MlError> {
    vm.call_host("outer", &[])
}

#[test]
fn ml_nested_host_callback_reenters_without_losing_host() {
    let mut vm = Vm::new(RecursiveHost);
    vm.register_native(
        "fetch",
        TypeScheme::mono(Type::Function(
            Box::new(Type::Constructor("unit".to_owned(), vec![])),
            Box::new(Type::Constructor("int".to_owned(), vec![])),
        )),
        fetch_from_host,
    )
    .expect("active VM may register native function");
    vm.evaluate("host.sml", "val answer = fetch ();")
        .expect("nested host call must reuse same bridge");
    assert_eq!(int_result(&vm, "answer"), 31);
}

#[test]
fn ml_denied_host_effect_survives_exception_handler_as_failed_runtime() {
    let mut vm = Vm::new(DenyHost);
    vm.register_host_effect(
        "File.read",
        TypeScheme::mono(Type::Function(
            Box::new(Type::Constructor("string".to_owned(), vec![])),
            Box::new(Type::Constructor("string".to_owned(), vec![])),
        )),
        "filesystem.read",
    )
    .expect("host effect signature may be registered");
    let error = vm
        .evaluate("denied.sml", "val answer = (File.read \"private\") handle _ => \"forged\";")
        .expect_err("denied effect is supervisor failure, not catchable ML exception");
    assert_eq!(error.kind, MlErrorKind::HostPermission);
    assert_eq!(
        vm.lookup_value("answer").expect_err("runtime cannot be revived").kind,
        MlErrorKind::Stopped
    );
}

#[test]
fn ml_local_body_rebinding_exports_matching_value_and_type() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "rebinding.sml",
        "val x = true; local val hidden = 1 in val x = hidden + 1 end; val answer = x + 3;",
    )
    .expect("body rebinding must replace both the outer value and its type");
    assert_eq!(int_result(&vm, "x"), 2);
    assert_eq!(int_result(&vm, "answer"), 5);
    assert!(vm.lookup_value("hidden").unwrap().is_none());
    assert_eq!(
        vm.evaluate("hidden.sml", "val leak = hidden;").unwrap_err().kind,
        MlErrorKind::Type,
    );
}

#[test]
fn ml_local_body_exports_new_and_rebound_names_without_local_names() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "local.sml",
        "val x = 1; local val hidden = 8 in val x = hidden; val result = x + 2 end;",
    )
    .expect("body declarations must export");
    assert_eq!(int_result(&vm, "x"), 8);
    assert_eq!(int_result(&vm, "result"), 10);
    assert!(vm.lookup_value("hidden").unwrap().is_none());
}

#[test]
fn ml_local_exception_restores_outer_names_and_type_environment() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("outer.sml", "val x = true; exception Oops;").unwrap();
    let error = vm
        .evaluate(
            "failed-local.sml",
            "local val hidden = 9 in val x = hidden; val discarded = raise Oops end;",
        )
        .expect_err("body exception must propagate");
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
    assert!(vm.lookup_value("x").unwrap().unwrap().as_bool().unwrap());
    assert!(vm.lookup_value("hidden").unwrap().is_none());
    assert!(vm.lookup_value("discarded").unwrap().is_none());
    vm.evaluate("after.sml", "val answer = if x then 3 else 4;").unwrap();
    assert_eq!(int_result(&vm, "answer"), 3);
}

#[test]
fn ml_host_value_retains_object_without_vm_slot() {
    let mut vm = Vm::new(DenyHost);
    let object = vm.insert_host_object(std::rc::Rc::new(42_i64)).unwrap();
    drop(vm);
    assert_eq!(object.downcast_host_object::<i64>(), Some(&42));
}

#[test]
fn ml_local_module_exports_only_body_structures() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "local-module.sml",
        "local structure Hidden = struct val n = 2 end \
         in structure Visible = Hidden end;",
    )
    .unwrap();
    assert!(vm.lookup_structure("Hidden").unwrap().is_none());
    assert_eq!(
        vm.lookup_structure("Visible").unwrap().unwrap().lookup_value("n").and_then(Value::as_int),
        Some(2),
    );
}

#[test]
fn ml_functor_application_uses_definition_site_values() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "functor-lexical.sml",
        "val seed = 2; signature Empty = sig end; \
         functor Make(X:Empty) = struct val result = seed + 1 end; \
         val seed = 9; structure Arg = struct val n = 0 end; \
         structure Out = Make(Arg);",
    )
    .unwrap();
    assert_eq!(
        vm.lookup_structure("Out").unwrap().unwrap().lookup_value("result").and_then(Value::as_int),
        Some(3),
    );
    assert_eq!(int_result(&vm, "seed"), 9);
}

#[test]
fn ml_local_private_exception_restores_outer_scope() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("outer.sml", "val x = 7; exception Oops;").unwrap();
    let error = vm
        .evaluate("failed-private.sml", "local val hidden = raise Oops in val x = 8 end;")
        .unwrap_err();
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
    assert_eq!(int_result(&vm, "x"), 7);
    assert!(vm.lookup_value("hidden").unwrap().is_none());
    vm.evaluate("after.sml", "val answer = x + 1;").unwrap();
    assert_eq!(int_result(&vm, "answer"), 8);
}
