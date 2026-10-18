use isabelle_rs::ml::{DenyHost, MlError, MlErrorKind, Type, TypeScheme, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("list-option-contract.sml", source).expect("Basis contract should evaluate");
    vm
}

fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_int).expect("integer binding")
}

fn boolean(vm: &Vm, name: &str) -> bool {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_bool).expect("boolean binding")
}

#[test]
fn list_endpoints_slice_and_concatenation_preserve_contents_and_boundary_exceptions() {
    let vm = evaluate(
        "val last = List.last [1, 2, 3]; \
        val one = List.getItem [4, 5]; val (head, remaining) = Option.valOf one; \
        val rest = remaining = [5]; \
        val empty = Option.isSome (List.getItem []); \
        val taken = List.take ([1, 2, 3], 2) = [1, 2]; \
        val dropped = List.drop ([1, 2, 3], 2) = [3]; \
        val zero = List.take ([], 0) = [] andalso List.drop ([], 0) = []; \
        val combined = List.concat [[1, 2], [], [3]] = [1, 2, 3]; \
        val joined = List.revAppend ([1, 2], [3, 4]) = [2, 1, 3, 4]; \
        val appended = List.@ ([1], [2]) = [1, 2]; \
        val empty_error = (List.last []; false) handle List.Empty => true; \
        val neg_take = (List.take ([1], ~1); false) handle General.Subscript => true; \
        val long_take = (List.take ([1], 2); false) handle Subscript => true; \
        val neg_drop = (List.drop ([], ~1); false) handle Subscript => true; \
        val long_drop = (List.drop ([1], 2); false) handle Subscript => true;",
    );
    assert_eq!(integer(&vm, "last"), 3);
    assert_eq!(integer(&vm, "head"), 4);
    assert!(boolean(&vm, "rest"));
    assert!(!boolean(&vm, "empty"));
    for name in [
        "taken",
        "dropped",
        "zero",
        "combined",
        "joined",
        "appended",
        "empty_error",
        "neg_take",
        "long_take",
        "neg_drop",
        "long_drop",
    ] {
        assert!(boolean(&vm, name), "{name}");
    }
}

#[test]
fn list_callbacks_visit_left_to_right_and_short_circuit() {
    let vm = evaluate(
        "val seen = ref 0; \
        val tabulated = List.tabulate (3, fn i => (seen := !seen * 10 + i + 1; i + 4)); \
        val tab_order = !seen; val tab_values = tabulated = [4, 5, 6]; \
        val partial = List.mapPartial (fn n => (seen := !seen * 10 + n; \
            if n = 2 then NONE else SOME (n * 3))) [1, 2, 3] = [3, 9]; \
        val map_order = !seen; seen := 0; \
        val found = List.find (fn n => (seen := !seen * 10 + n; n = 2)) [1, 2, 3]; \
        val found_value = Option.valOf found; val find_order = !seen; seen := 0; \
        val filtered = List.filter (fn n => (seen := !seen * 10 + n; n = 2)) [1, 2, 3] = [2]; \
        val filter_order = !seen; seen := 0; \
        val (yes, no) = List.partition (fn n => (seen := !seen * 10 + n; n = 2)) [1, 2, 3]; \
        val partition_order = !seen; val selected = yes = [2] andalso no = [1, 3]; \
        val none = Option.isSome (List.find (fn _ => true) []); \
        val size_error = (List.tabulate (~1, fn _ => 1); false) handle Size => true;",
    );
    assert_eq!(integer(&vm, "tab_order"), 123);
    assert!(boolean(&vm, "tab_values"));
    assert!(boolean(&vm, "partial"));
    assert_eq!(integer(&vm, "map_order"), 123123);
    assert_eq!(integer(&vm, "found_value"), 2);
    assert_eq!(integer(&vm, "find_order"), 12);
    assert!(boolean(&vm, "filtered"));
    assert_eq!(integer(&vm, "filter_order"), 123);
    assert!(boolean(&vm, "selected"));
    assert_eq!(integer(&vm, "partition_order"), 123);
    assert!(!boolean(&vm, "none"));
    assert!(boolean(&vm, "size_error"));
}

#[test]
fn list_collate_respects_lexical_order_short_circuit_and_runtime_stamps() {
    let mut vm = evaluate(
        "val old_less = LESS; val old_equal = EQUAL; \
        datatype unrelated = LESS | EQUAL | GREATER;",
    );
    vm.collect_garbage().expect("rooted order constructors survive collection");
    vm.evaluate(
        "list-order.sml",
        "val count = ref 0; \
        val compare = fn (a, b) => (count := !count + 1; \
            if a = b then old_equal else old_less); \
        val first = List.collate compare ([1, 2, 3], [1, 4, 5]) = old_less; \
        val first_count = !count; \
        val shorter = List.collate compare ([1], [1, 2]) = old_less; \
        val equal = List.collate compare ([], []) = old_equal; \
        val greater = List.collate compare ([1], []) = old_less; \
        val final_count = !count;",
    )
    .expect("list ordering follows original Basis stamps");
    assert!(boolean(&vm, "first"));
    assert_eq!(integer(&vm, "first_count"), 2);
    assert!(boolean(&vm, "shorter"));
    assert!(boolean(&vm, "equal"));
    assert!(!boolean(&vm, "greater"));
    assert_eq!(integer(&vm, "final_count"), 3);
}

#[test]
fn option_transformations_preserve_short_circuit_and_callback_order() {
    let vm = evaluate(
        "val calls = ref 0; \
        val mapper = Option.map (fn x => (calls := !calls * 10 + 1; x + 2)); \
        val map_none = Option.isSome (mapper NONE); val mapped = Option.valOf (mapper (SOME 3)); \
        val partial = Option.mapPartial (fn x => (calls := !calls * 10 + 2; \
            if x = 0 then NONE else SOME (x * 2))); \
        val partial_none = Option.isSome (partial NONE); \
        val partial_empty = Option.isSome (partial (SOME 0)); \
        val partial_value = Option.valOf (partial (SOME 4)); \
        val joined = Option.valOf (Option.join (SOME (SOME 7))); \
        val join_none = Option.isSome (Option.join (SOME NONE)); \
        val join_outer_none = Option.isSome (Option.join NONE); \
        val keep = Option.valOf (Option.filter (fn x => (calls := !calls * 10 + 3; x = 8)) 8); \
        val reject = Option.isSome (Option.filter (fn x => x = 0) 8); \
        val _ = Option.app (fn n => calls := !calls * 10 + n) NONE; \
        val _ = Option.app (fn n => calls := !calls * 10 + n) (SOME 4); \
        val trace = !calls;",
    );
    assert!(!boolean(&vm, "map_none"));
    assert_eq!(integer(&vm, "mapped"), 5);
    assert!(!boolean(&vm, "partial_none"));
    assert!(!boolean(&vm, "partial_empty"));
    assert_eq!(integer(&vm, "partial_value"), 8);
    assert_eq!(integer(&vm, "joined"), 7);
    assert!(!boolean(&vm, "join_none"));
    assert!(!boolean(&vm, "join_outer_none"));
    assert_eq!(integer(&vm, "keep"), 8);
    assert!(!boolean(&vm, "reject"));
    assert_eq!(integer(&vm, "trace"), 12234);
}

#[test]
fn option_composition_applies_right_before_left_only_for_present_values() {
    let vm = evaluate(
        "val calls = ref 0; \
        val f = fn x => (calls := !calls * 10 + 2; x * 2); \
        val g = fn x => (calls := !calls * 10 + 1; if x = 0 then NONE else SOME (x + 1)); \
        val composed = Option.compose (f, g); \
        val absent = Option.isSome (composed 0); \
        val present = Option.valOf (composed 3); val first_trace = !calls; calls := 0; \
        val partial = Option.composePartial (fn x => (calls := !calls * 10 + 3; \
            if x = 2 then NONE else SOME (x * 3)), g); \
        val missing = Option.isSome (partial 0); \
        val rejected = Option.isSome (partial 1); \
        val produced = Option.valOf (partial 2); val second_trace = !calls;",
    );
    assert!(!boolean(&vm, "absent"));
    assert_eq!(integer(&vm, "present"), 8);
    assert_eq!(integer(&vm, "first_trace"), 112);
    assert!(!boolean(&vm, "missing"));
    assert!(!boolean(&vm, "rejected"));
    assert_eq!(integer(&vm, "produced"), 9);
    assert_eq!(integer(&vm, "second_trace"), 11313);
}

#[test]
fn list_option_callbacks_reenter_basis_and_preserve_exception_identity() {
    let vm = evaluate(
        "val matching = List.filter (fn n => \
        Option.isSome (List.find (fn x => x = n) [2, 4])) [1, 2, 3, 4] = [2, 4]; \
        val composed = Option.compose (fn x => Option.valOf (Option.map (fn y => y + 1) (SOME x)), \
            fn x => SOME x); \
        val composed_result = Option.valOf (composed 5); \
        val list_error = (List.mapPartial (fn n => if n = 2 then raise Subscript else SOME n) [1, 2, 3]; false) \
            handle General.Subscript => true; \
        val option_error = (Option.map (fn _ => raise Size) (SOME 2); false) \
            handle General.Size => true;",
    );
    assert!(boolean(&vm, "matching"));
    assert_eq!(integer(&vm, "composed_result"), 6);
    assert!(boolean(&vm, "list_error"));
    assert!(boolean(&vm, "option_error"));
}

fn stop_on_two(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let index = args[0].as_int().expect("callback receives an int");
    if index == 2 {
        vm.request_stop();
    }
    Ok(Value::int(index))
}

#[test]
fn list_tabulate_callback_stop_cannot_be_caught_by_ml() {
    let mut vm = Vm::new(DenyHost);
    let integer = Type::Constructor("int".to_owned(), vec![]);
    vm.register_native(
        "stop_on_two",
        TypeScheme::mono(Type::Function(Box::new(integer.clone()), Box::new(integer))),
        stop_on_two,
    )
    .expect("register stop callback");
    let error = vm
        .evaluate(
            "list-stop.sml",
            "val result = (List.tabulate (4, stop_on_two); 99) handle _ => 77;",
        )
        .expect_err("supervisor stop is not an ML exception");
    assert_eq!(error.kind, MlErrorKind::Stopped);
}
