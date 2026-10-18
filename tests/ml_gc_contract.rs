use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("gc-contract.sml", source).expect("valid ML program should evaluate");
    vm
}

fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_int).expect("integer binding")
}

fn boolean(vm: &Vm, name: &str) -> bool {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_bool).expect("boolean binding")
}

#[test]
fn basis_gc_preserves_live_array_after_collection() {
    let mut vm = evaluate(
        "val live = Array.fromList [41]; \
        val _ = let val discarded = Array.fromList [ref 3] in () end;",
    );
    vm.collect_garbage().expect("collection must preserve rooted array");
    vm.evaluate(
        "basis-after-gc.sml",
        "val _ = Array.update (live, 0, 43); val result = Array.sub (live, 0);",
    )
    .expect("array alias must stay usable after collection");
    assert_eq!(integer(&vm, "result"), 43);
}

#[test]
fn basis_gc_reclaims_unreachable_array_closure_cycle() {
    let mut vm = evaluate(
        "val _ = let val arr = Array.array (1, fn x => x) \
        val _ = Array.update (arr, 0, fn x => (Array.sub (arr, 0)) x) in () end;",
    );
    assert!(vm.collect_garbage().expect("array cycle should be collectable") >= 2);
}

#[test]
fn weak_reference_some_none_and_nested_ref_patterns_preserve_identity() {
    let vm = evaluate(
        "fun peek (ref (SOME (ref item))) = SOME item | peek _ = NONE; \
         val token = ref 17; \
         val weak = Weak.weak (SOME token); \
         val alias = weak; \
         val empty = Weak.weak NONE; \
         val active = peek weak = SOME 17 andalso !weak = SOME token; \
         val absent = peek empty = NONE andalso !empty = NONE; \
         val same = weak = alias andalso weak <> Weak.weak (SOME token);",
    );
    assert!(boolean(&vm, "active"));
    assert!(boolean(&vm, "absent"));
    assert!(boolean(&vm, "same"));
}

#[test]
fn weak_reference_keeps_strongly_reachable_token_after_collection() {
    let mut vm = evaluate(
        "val token = ref 23; \
         val weak = Weak.weak (SOME token); \
         val immediate = !weak = SOME token;",
    );
    assert!(boolean(&vm, "immediate"));
    vm.collect_garbage().expect("strong token remains live");
    vm.evaluate("weak-strong.sml", "val retained = !weak = SOME token;")
        .expect("the strong reference must retain its token");
    assert!(boolean(&vm, "retained"));
}

#[test]
fn weak_reference_clears_only_during_collection_without_strong_token() {
    let mut vm = evaluate(
        "val weak = let val token = ref 31 in Weak.weak (SOME token) end; \
         val immediate = case !weak of SOME (ref 31) => true | _ => false;",
    );
    assert!(boolean(&vm, "immediate"));
    vm.collect_garbage().expect("unreachable token is clearable");
    vm.evaluate("weak-cleared.sml", "val cleared = !weak = NONE;")
        .expect("collection changes the weak slot to NONE");
    assert!(boolean(&vm, "cleared"));
}

#[test]
fn weak_reference_assignment_changes_weakly_held_token_and_preserves_aliases() {
    let mut vm = evaluate(
        "val weak = Weak.weak NONE; \
         val alias = weak; \
         val _ = let val token = ref 41 in weak := SOME token end; \
         val initially_active = case !alias of SOME (ref 41) => true | _ => false;",
    );
    assert!(boolean(&vm, "initially_active"));
    vm.collect_garbage().expect("assigned weak token is clearable");
    vm.evaluate("weak-assigned-gc.sml", "val cleared = !alias = NONE;")
        .expect("assignment remains weak after GC");
    assert!(boolean(&vm, "cleared"));
    vm.evaluate(
        "weak-reassigned.sml",
        "val strong = ref 42; val _ = alias := SOME strong; \
         val reassigned = !weak = SOME strong andalso weak = alias;",
    )
    .expect("an alias updates the same weak reference");
    assert!(boolean(&vm, "reassigned"));
    vm.collect_garbage().expect("assigned strong token remains live");
    vm.evaluate("weak-reassigned-gc.sml", "val retained = !alias = SOME strong;")
        .expect("strongly referenced reassigned token must survive");
    assert!(boolean(&vm, "retained"));
}

#[test]
fn weak_reference_collector_clears_cyclic_token() {
    let mut vm = evaluate(
        "datatype token = Link of token ref option; \
         val weak = let val node = ref (Link NONE) in \
           node := Link (SOME node); Weak.weak (SOME node) end;",
    );
    vm.collect_garbage().expect("unreachable cyclic token is clearable");
    vm.evaluate("weak-cycle-gc.sml", "val cleared = !weak = NONE;")
        .expect("a cycle does not keep a weak token alive");
    assert!(boolean(&vm, "cleared"));
}

#[test]
fn weak_reference_collector_refuses_stopped_vm() {
    let mut vm = evaluate("val weak = Weak.weak (SOME (ref 1));");
    vm.request_stop();
    assert_eq!(vm.collect_garbage().unwrap_err().kind, MlErrorKind::Stopped);
}

#[test]
fn weak_reference_rejects_non_reference_option_at_type_boundary() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate("weak-invalid.sml", "val bad = Weak.weak (SOME 5);")
        .expect_err("weak reference requires a reference token");
    assert_eq!(error.kind, MlErrorKind::Type);
}

fn clone_value(vm: &Vm, name: &str) -> Value {
    vm.lookup_value(name).expect("active VM").expect("binding exists").clone()
}

#[test]
fn weak_reference_dynamic_non_option_assignment_rejects_without_mutation() {
    let mut vm = evaluate("val weak = Weak.weak NONE; val token = ref 7;");
    let assign = clone_value(&vm, ":=");
    let weak = clone_value(&vm, "weak");
    let token = clone_value(&vm, "token");
    let error = vm
        .apply(&assign, &[Value::tuple(vec![weak, token])])
        .expect_err("a weak slot cannot contain a bare reference");
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.collect_garbage().unwrap();
    vm.evaluate("weak-invalid-assignment.sml", "val unchanged = !weak = NONE andalso !token = 7;")
        .unwrap();
    assert!(boolean(&vm, "unchanged"));
}

fn assert_weak_assignment_rejected(vm: &mut Vm, value: Value) {
    let assign = clone_value(vm, ":=");
    let weak = clone_value(vm, "weak");
    let error = vm.apply(&assign, &[Value::tuple(vec![weak, value])]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.collect_garbage().unwrap();
    vm.evaluate("weak-unchanged.sml", "val unchanged = !weak = NONE;").unwrap();
    assert!(boolean(vm, "unchanged"));
}

#[test]
fn weak_reference_dynamic_non_reference_payload_rejects_without_mutation() {
    let mut vm = evaluate("val weak = Weak.weak NONE;");
    let invalid = vm.make_option(Some(Value::int(5))).unwrap();
    assert_weak_assignment_rejected(&mut vm, invalid);
}

#[test]
fn weak_reference_dynamic_foreign_option_revokes_vm() {
    let mut vm = evaluate("val weak = Weak.weak NONE;");
    let mut foreign = Vm::new(DenyHost);
    let invalid = foreign.make_option(None).unwrap();
    let assign = clone_value(&vm, ":=");
    let weak = clone_value(&vm, "weak");
    let error = vm.apply(&assign, &[Value::tuple(vec![weak, invalid])]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::HostFailure);
    assert_eq!(vm.collect_garbage().unwrap_err().kind, MlErrorKind::Stopped);
    assert_eq!(
        vm.evaluate("weak-stopped.sml", "val recovered = (!weak handle _ => NONE);")
            .unwrap_err()
            .kind,
        MlErrorKind::Stopped
    );
}

#[test]
fn weak_reference_dynamic_same_named_option_rejects_without_mutation() {
    let mut vm = evaluate(
        "val weak = Weak.weak NONE; \
         structure Forged = struct datatype 'a option = NONE | SOME of 'a end; \
         val invalid = Forged.SOME (ref 7);",
    );
    let invalid = clone_value(&vm, "invalid");
    assert_weak_assignment_rejected(&mut vm, invalid);
}

#[test]
fn weak_reference_rust_strong_root_retains_until_released() {
    let mut vm = evaluate("val token = ref 7; val weak = Weak.weak (SOME token);");
    let root = clone_value(&vm, "token");
    vm.evaluate("shadow-token.sml", "val token = ();").unwrap();
    vm.collect_garbage().unwrap();
    vm.evaluate("rust-root.sml", "val retained = case !weak of SOME (ref 7) => true | _ => false;")
        .unwrap();
    assert!(boolean(&vm, "retained"));
    drop(root);
    vm.collect_garbage().unwrap();
    vm.evaluate("released-root.sml", "val cleared = !weak = NONE;").unwrap();
    assert!(boolean(&vm, "cleared"));
}

#[test]
fn weak_reference_separate_option_root_retains_until_shadowed() {
    let mut vm = evaluate("val held = SOME (ref 7); val weak = Weak.weak held;");
    vm.collect_garbage().unwrap();
    vm.evaluate("option-root.sml", "val retained = !weak = held;").unwrap();
    assert!(boolean(&vm, "retained"));
    vm.evaluate("shadow-option.sml", "val held = ();").unwrap();
    vm.collect_garbage().unwrap();
    vm.evaluate("released-option.sml", "val cleared = !weak = NONE;").unwrap();
    assert!(boolean(&vm, "cleared"));
}

#[test]
fn weak_reference_nested_weak_token_preserves_live_identity_then_clears() {
    let mut vm =
        evaluate("val inner = Weak.weak (SOME (ref 7)); val outer = Weak.weak (SOME inner);");
    vm.collect_garbage().unwrap();
    vm.evaluate("nested-weak.sml", "val retained = !outer = SOME inner andalso !inner = NONE;")
        .unwrap();
    assert!(boolean(&vm, "retained"));
    vm.evaluate("shadow-inner.sml", "val inner = ();").unwrap();
    vm.collect_garbage().unwrap();
    vm.evaluate("released-inner.sml", "val cleared = !outer = NONE;").unwrap();
    assert!(boolean(&vm, "cleared"));
}

#[test]
fn weak_reference_collected_partial_closure_preserves_shared_live_environment() {
    let mut vm = evaluate(
        "val (survivor, weak) = let fun f x y = x + y val discarded = f 1 \
         in (f 2, Weak.weak (SOME (ref discarded))) end;",
    );
    vm.collect_garbage().unwrap();
    vm.evaluate("shared-closure.sml", "val cleared = !weak = NONE; val answer = survivor 3;")
        .unwrap();
    assert!(boolean(&vm, "cleared"));
    assert_eq!(integer(&vm, "answer"), 5);
}
