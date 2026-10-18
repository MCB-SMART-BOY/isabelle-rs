use isabelle_rs::ml::{DenyHost, Value, Vm};

#[test]
fn pure_basics_fold_selects_clause_after_all_curried_arguments() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("Pure/General/exn.ML", include_str!("../isabelle-source/src/Pure/General/exn.ML"))
        .expect("original exception helpers load");
    vm.evaluate(
        "Pure/General/basics.ML",
        include_str!("../isabelle-source/src/Pure/General/basics.ML"),
    )
    .expect("original Pure Basics load");
    vm.evaluate(
        "fold-consumer.ML",
        "val result = fold (fn x => fn acc => x + acc) [1, 2, 3] 0; \
         val reverse = fold_rev (fn x => fn acc => acc * 10 + x) [1, 2, 3] 0;",
    )
    .expect("all curried arguments select the same source clause");
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(6));
    assert_eq!(vm.lookup_value("reverse").unwrap().and_then(Value::as_int), Some(321));
}

#[test]
fn ml_curried_partial_survives_collection_without_erasing_shared_closure() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "partial.sml",
        "fun choose 0 x = x | choose n x = n + x; \
         val partial = choose 1; \
         fun discarded n x = n + x; val discarded = 0;",
    )
    .expect("partial function and discarded recursive closure evaluate");
    vm.collect_garbage().expect("collection preserves reachable partial closures");
    vm.evaluate("after-collection.sml", "val result = partial 2; val zero = choose 0 3;")
        .expect("partial and original closure remain callable");
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(3));
    assert_eq!(vm.lookup_value("zero").unwrap().and_then(Value::as_int), Some(3));
}
