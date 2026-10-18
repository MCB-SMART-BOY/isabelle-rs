use isabelle_rs::ml::{DenyHost, MlError, MlErrorKind, Type, TypeScheme, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("collection-contract.sml", source).expect("collection contract should evaluate");
    vm
}

fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_int).expect("integer binding")
}

fn boolean(vm: &Vm, name: &str) -> bool {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_bool).expect("boolean binding")
}

#[test]
fn collection_vector_map_indexed_fold_and_application_follow_index_order() {
    let vm = evaluate(
        "val v = Vector.fromList [1, 2, 3]; \
        val m = Vector.map (fn x => x * 2) v; \
        val mi = Vector.mapi (fn (i, x) => i + x) v; \
        val l = Vector.foldli (fn (i, x, n) => n * 10 + i + x) 0 v; \
        val r = Vector.foldri (fn (i, x, n) => n * 10 + i + x) 0 v; \
        val seen = ref 0; \
        val _ = Vector.app (fn x => seen := !seen * 10 + x) v; \
        val _ = Vector.appi (fn (i, x) => seen := !seen * 10 + i + x) v; \
        val mapped = Vector.sub (m, 1); val indexed = Vector.sub (mi, 2); val visited = !seen;",
    );
    assert_eq!(integer(&vm, "mapped"), 4);
    assert_eq!(integer(&vm, "indexed"), 5);
    assert_eq!(integer(&vm, "l"), 135);
    assert_eq!(integer(&vm, "r"), 531);
    assert_eq!(integer(&vm, "visited"), 123135);
}

#[test]
fn collection_vector_concat_update_and_empty_preserve_value_contract() {
    let vm = evaluate(
        "val original = Vector.fromList [3, 4]; \
        val same = Vector.concat [original] = original; \
        val combined = Vector.concat [Vector.fromList [], original, Vector.fromList [5]]; \
        val edited = Vector.update (combined, 1, 8); \
        val old = Vector.sub (combined, 1); val new = Vector.sub (edited, 1); \
        val empty = Vector.length (Vector.concat []); \
        val bad = (Vector.update (combined, 3, 9); false) handle Subscript => true; \
        val bounds = Int.< (3, Vector.maxLen) andalso Int.< (3, Array.maxLen);",
    );
    assert!(boolean(&vm, "same"));
    assert_eq!(integer(&vm, "old"), 4);
    assert_eq!(integer(&vm, "new"), 8);
    assert_eq!(integer(&vm, "empty"), 0);
    assert!(boolean(&vm, "bad"));
    assert!(boolean(&vm, "bounds"));
}

#[test]
fn collection_partial_callbacks_wait_for_collection_argument() {
    let vm = evaluate(
        "val calls = ref 0; \
        val mapper = Vector.map (fn x => (calls := !calls + 1; x + 1)); \
        val modifier = Array.modify (fn x => (calls := !calls + 1; x + 1)); \
        val calls_before = !calls; \
        val vec = mapper (Vector.fromList [4, 5]); \
        val arr = Array.fromList [6]; val _ = modifier arr; \
        val after = !calls; val mapped = Vector.sub (vec, 0); \
        val modified = Array.sub (arr, 0);",
    );
    assert_eq!(integer(&vm, "calls_before"), 0);
    assert_eq!(integer(&vm, "after"), 3);
    assert_eq!(integer(&vm, "mapped"), 5);
    assert_eq!(integer(&vm, "modified"), 7);
}

#[test]
fn collection_find_and_collate_stop_at_first_result() {
    let vm = evaluate(
        "val v = Vector.fromList [2, 4, 6]; \
        val calls = ref 0; \
        val found = Vector.find (fn n => (calls := !calls + 1; n = 4)) v; \
        val indexed = Vector.findi (fn (i, n) => i = 2 andalso n = 6) v; \
        val count = !calls; \
        val none = Option.isSome (Vector.find (fn _ => true) (Vector.fromList [])); \
        val less = Vector.collate (fn (x, y) => if Int.< (x, y) then LESS else if x = y then EQUAL else GREATER) \
          (v, Vector.fromList [2, 5]); \
        val shorter = Vector.collate (fn (_, _) => EQUAL) (v, Vector.fromList [2, 4, 6, 8]); \
        val equal = Vector.collate (fn (_, _) => EQUAL) (v, v); \
        val found_value = Option.valOf found; \
        val (found_index, _) = Option.valOf indexed; \
        val less_matches = less = LESS; val shorter_matches = shorter = LESS; \
        val equal_matches = equal = EQUAL;",
    );
    assert_eq!(integer(&vm, "count"), 2);
    assert_eq!(integer(&vm, "found_value"), 4);
    assert_eq!(integer(&vm, "found_index"), 2);
    assert!(!boolean(&vm, "none"));
    assert!(boolean(&vm, "less_matches"));
    assert!(boolean(&vm, "shorter_matches"));
    assert!(boolean(&vm, "equal_matches"));
}

#[test]
fn collection_array_modify_and_fold_observe_prior_mutations() {
    let vm = evaluate(
        "val a = Array.fromList [1, 2, 3]; \
        val _ = Array.modifyi (fn (i, x) => (if i = 0 then Array.update (a, 1, 7) else (); x + i)) a; \
        val second = Array.sub (a, 1); \
        val folded = Array.foldli (fn (i, x, n) => \
            (if i = 0 then Array.update (a, 2, 9) else (); n * 10 + x)) 0 a; \
        val reversed = Array.foldri (fn (i, x, n) => n * 10 + x + i) 0 a; \
        val visited = ref 0; \
        val _ = Array.appi (fn (i, x) => visited := !visited * 10 + i + x) a; \
        val _ = Array.app (fn x => visited := !visited * 10 + x) (Array.fromList []); \
        val visit = !visited;",
    );
    assert_eq!(integer(&vm, "second"), 8);
    assert_eq!(integer(&vm, "folded"), 189);
    assert_eq!(integer(&vm, "reversed"), 1191);
    assert_eq!(integer(&vm, "visit"), 201);
}

#[test]
fn collection_array_copy_vec_snapshot_and_bounds_preserve_source() {
    let vm = evaluate(
        "val a = Array.fromList [1, 2, 3]; \
        val snapshot = Array.vector a; val _ = Array.update (a, 1, 7); \
        val original = Vector.sub (snapshot, 1); \
        val dst = Array.array (5, 0); \
        val _ = Array.copy {src = a, dst = dst, di = 1}; \
        val copied = Array.sub (dst, 2); \
        val _ = Array.copyVec {src = snapshot, dst = dst, di = 2}; \
        val copied_vec = Array.sub (dst, 3); \
        val _ = Array.copy {src = a, dst = a, di = 0}; \
        val bad = (Array.copy {src = a, dst = a, di = 1}; false) handle Subscript => true; \
        val unchanged = Array.sub (a, 1); \
        val empty = Array.fromList []; \
        val _ = Array.copy {src = empty, dst = dst, di = 5};",
    );
    assert_eq!(integer(&vm, "original"), 2);
    assert_eq!(integer(&vm, "copied"), 7);
    assert_eq!(integer(&vm, "copied_vec"), 2);
    assert_eq!(integer(&vm, "unchanged"), 7);
    assert!(boolean(&vm, "bad"));
}

#[test]
fn collection_array_find_collate_and_modify_exception_preserve_prior_writes() {
    let vm = evaluate(
        "val a = Array.fromList [1, 2, 3]; \
        val result = (Array.modify (fn n => if n = 3 then raise Subscript else n + 10) a; 0) \
          handle Subscript => Array.sub (a, 1); \
        val found = Array.find (fn n => n = 12) a; \
        val indexed = Array.findi (fn (i, n) => i = 2 andalso n = 3) a; \
        val compare = Array.collate (fn (x, y) => if x = y then EQUAL else GREATER) \
          (a, Array.fromList [11, 12, 3]); \
        val compare_same = compare = EQUAL; \
        val found_value = Option.valOf found; \
        val (found_index, _) = Option.valOf indexed;",
    );
    assert_eq!(integer(&vm, "result"), 12);
    assert_eq!(integer(&vm, "found_value"), 12);
    assert!(boolean(&vm, "compare_same"));
    assert_eq!(integer(&vm, "found_index"), 2);
}

fn stop_at_one(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let index = args[0].as_int().expect("callback receives an int");
    if index == 1 {
        vm.request_stop();
    }
    Ok(Value::int(index))
}

#[test]
fn collection_vector_map_stop_cannot_be_caught_by_ml() {
    let mut vm = Vm::new(DenyHost);
    let int = Type::Constructor("int".to_owned(), vec![]);
    vm.register_native(
        "stop_at_one",
        TypeScheme::mono(Type::Function(Box::new(int.clone()), Box::new(int))),
        stop_at_one,
    )
    .expect("native callback registration");
    let error = vm
        .evaluate(
            "collection-stop.sml",
            "val mapped = Vector.map stop_at_one (Vector.fromList [0, 1, 2]);",
        )
        .expect_err("supervisor stop must abort collection traversal");
    assert_eq!(error.kind, MlErrorKind::Stopped);
}

#[test]
fn collection_signatures_preserve_shared_array_vector_types() {
    let vm = evaluate(
        "structure V : VECTOR = Vector; structure A : ARRAY = Array; \
        val a : int A.array = A.fromList [2, 4]; \
        val v : int Array.vector = A.vector a; \
        val shared : int V.vector = v; \
        val result = V.sub (shared, 1);",
    );
    assert_eq!(integer(&vm, "result"), 4);
}

#[test]
fn collection_collate_shadowed_order_preserves_callback_and_length_results() {
    let mut vm = evaluate(
        "val old_less = LESS; val old_equal = EQUAL; \
        datatype unrelated = LESS | EQUAL | GREATER;",
    );
    vm.collect_garbage().unwrap();
    vm.evaluate(
        "collection-order.sml",
        "val vector_result = Vector.collate (fn (_, _) => old_less) \
            (Vector.fromList [1], Vector.fromList [2]) = old_less; \
         val array_result = Array.collate (fn (_, _) => old_equal) \
            (Array.fromList [1], Array.fromList [1, 2]) = old_less;",
    )
    .unwrap();
    assert!(boolean(&vm, "vector_result"));
    assert!(boolean(&vm, "array_result"));
}
