use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("pretty-printer-security.sml", source)
        .expect("valid ML printer program should evaluate");
    vm
}

fn boolean(vm: &Vm, name: &str) -> bool {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_bool).expect("boolean binding")
}

#[test]
fn printer_weak_target_parameter_rejects_registration() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "pretty-weak-target.sml",
            "val saved = ref []; \
         val _ = PolyML.addPrettyPrinter \
           (fn depth => fn pretty => fn xs => \
             (saved := xs; case xs of [] => PolyML.PrettyString \"\" \
              | x :: _ => pretty (x, depth)));",
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn printer_public_apply_rejects_before_native_callback_or_saved_ref_effects() {
    let mut vm = evaluate(
        "val saved = ref 0; val hits = ref 0; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn (_: int) => \
             (hits := !hits + 1; PolyML.PrettyString \"int\")); \
         fun store (x: int) = saved := x; \
         fun render_int (value: int) = \
           List.map PolyML.prettyRepresentation [(value, 8)];",
    );
    for name in ["store", "render_int"] {
        let function = vm.lookup_value(name).unwrap().unwrap().clone();
        let error = vm.apply(&function, &[Value::text("not-an-int")]).unwrap_err();
        assert_eq!(error.kind, MlErrorKind::Type);
    }
    vm.evaluate(
        "pretty-side-effects.sml",
        "val saved_unchanged = !saved = 0; val hits_unchanged = !hits = 0;",
    )
    .unwrap();
    assert!(boolean(&vm, "saved_unchanged"));
    assert!(boolean(&vm, "hits_unchanged"));
}

#[test]
fn public_apply_shared_list_dag_checks_each_typed_node_once() {
    const DEPTH: usize = 32;
    let mut vm = Vm::new(DenyHost);
    let input_type = format!("int{}", " list".repeat(DEPTH));
    vm.evaluate("shared-input.sml", &format!("fun consume (_: {input_type}) = 7;")).unwrap();
    let consume = vm.lookup_value("consume").unwrap().unwrap().clone();
    let mut input = Value::int(1);
    for _ in 0..DEPTH {
        input = Value::list(vec![input.clone(), input]);
    }
    let result = vm.apply(&consume, &[input]).unwrap();
    assert_eq!(result.as_int(), Some(7));
}
#[test]
fn public_apply_oversized_distinct_graph_rejects_before_effect() {
    const OVERSIZED_LIST_LENGTH: usize = 20_000;
    let mut vm = evaluate(
        "val hits = ref 0; \
         fun consume (_: int list) = (hits := !hits + 1; 7);",
    );
    let consume = vm.lookup_value("consume").unwrap().unwrap().clone();
    let items = (0..OVERSIZED_LIST_LENGTH).map(|_| Value::int(1)).collect();
    let error = vm.apply(&consume, &[Value::list(items)]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("oversized-side-effect.sml", "val unchanged = !hits = 0;").unwrap();
    assert!(boolean(&vm, "unchanged"));
}

#[test]
fn printer_late_opaque_identity_is_hidden_from_older_closure() {
    let vm = evaluate(
        "fun render value = PolyML.prettyRepresentation (value, 8); \
         structure Secret :> sig type t val item: t end = \
           struct type t = string val item = \"private-marker\" end; \
         val hidden = case render Secret.item of \
           PolyML.PrettyString value => value | _ => \"\";",
    );
    assert_eq!(vm.lookup_value("hidden").unwrap().and_then(Value::as_text), Some("<opaque>"),);
}

#[test]
fn printer_late_raw_registration_cannot_disclose_sealed_datatype() {
    let vm = evaluate(
        "structure Raw = struct datatype t = Wrap of string end; \
         structure Secret :> sig type t val item: t end = struct \
           datatype t = datatype Raw.t; val item = Wrap \"private-marker\" end; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn Raw.Wrap text => PolyML.PrettyString text); \
         val disclosed = case PolyML.prettyRepresentation (Secret.item, 8) of \
           PolyML.PrettyString text => text | _ => \"\";",
    );
    assert_eq!(vm.lookup_value("disclosed").unwrap().and_then(Value::as_text), Some("<opaque>"));
}

#[test]
fn printer_opaque_view_propagates_to_returned_closure() {
    let vm = evaluate(
        "structure A :> sig type t val x: t val make: unit -> t -> int end = \
           struct datatype t = T val x = T \
             fun make () = fn (_: t) => 1 end; \
         val opaque_result = A.make () A.x;",
    );
    assert_eq!(vm.lookup_value("opaque_result").unwrap().and_then(Value::as_int), Some(1),);
}

#[test]
fn printer_resealed_borrowed_function_preserves_original_alias_and_export() {
    let vm = evaluate(
        "structure A :> sig type t val x: t val run: t -> int end = \
           struct type t = int val x = 1 fun run (_: t) = 7 end; \
         structure B :> sig type t val x: t val run: t -> int end = \
           struct type t = A.t val x = A.x val run = A.run end; \
         val earlier_result = A.run A.x; \
         val exported_result = B.run B.x;",
    );
    assert_eq!(vm.lookup_value("earlier_result").unwrap().and_then(Value::as_int), Some(7));
    assert_eq!(vm.lookup_value("exported_result").unwrap().and_then(Value::as_int), Some(7));
}

#[test]
fn printer_resealed_shared_reference_keeps_both_callback_type_views() {
    let vm = evaluate(
        "structure A :> sig type t val x: t val callback: (t -> int) ref end = \
           struct datatype t = T val x = T \
             val callback = ref (fn (_: t) => 7) end; \
         structure B :> sig type t val x: t val callback: (t -> int) ref end = \
           struct type t = A.t val x = A.x val callback = A.callback end; \
         val earlier_result = (!A.callback) A.x; \
         val later_result = (!B.callback) B.x;",
    );
    assert_eq!(vm.lookup_value("earlier_result").unwrap().and_then(Value::as_int), Some(7));
    assert_eq!(vm.lookup_value("later_result").unwrap().and_then(Value::as_int), Some(7));
}

#[test]
fn printer_resealed_borrowed_generic_closure_does_not_reveal_opaque_value() {
    let vm = evaluate(
        "fun render value = PolyML.prettyRepresentation (value, 8); \
         structure B :> sig type t val x: t val render: t -> PolyML.pretty end = \
           struct type t = string val x = \"private-marker\" val render = render end; \
         val disclosed = case B.render B.x of \
           PolyML.PrettyString value => value | _ => \"\"; \
         val hidden = case render B.x of \
           PolyML.PrettyString value => value | _ => \"\";",
    );
    assert_eq!(vm.lookup_value("hidden").unwrap().and_then(Value::as_text), Some("<opaque>"));
    assert_eq!(
        vm.lookup_value("disclosed").unwrap().and_then(Value::as_text),
        Some("\"private-marker\"")
    );
}

#[test]
fn public_apply_rejects_unresolved_weak_closure_input_before_effect() {
    let mut vm = evaluate(
        "val saved = ref []; val hits = ref 0; \
         fun store x = (hits := !hits + 1; saved := [x]);",
    );
    let store = vm.lookup_value("store").unwrap().unwrap().clone();
    let error = vm.apply(&store, &[Value::text("untyped")]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("weak-side-effect.sml", "val hits_unchanged = !hits = 0;").unwrap();
    assert!(boolean(&vm, "hits_unchanged"));
    vm.evaluate("specialize-weak.sml", "val _ = saved := [1];").unwrap();
}

#[test]
fn printer_native_partial_and_composition_retain_instantiated_evidence() {
    let vm = evaluate(
        "val hits = ref 0; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn (_: int) => \
             (hits := !hits + 1; PolyML.PrettyString \"int\")); \
         val render_all = List.map PolyML.prettyRepresentation; \
         val trees = render_all [(1, 5)]; \
         val render = PolyML.prettyRepresentation o (fn n => (n, 5)); \
         val tree = render 1; \
         val evidence_hits = !hits;",
    );
    assert_eq!(vm.lookup_value("evidence_hits").unwrap().and_then(Value::as_int), Some(2),);
}

#[test]
fn printer_shared_large_body_consumes_edge_budget() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "pretty-shared-body-budget.sml",
            "val leaf = PolyML.PrettyString \"x\"; \
         val body = List.tabulate (20000, fn _ => leaf); \
         val blocks = List.tabulate \
           (20000, fn _ => PolyML.PrettyBlock (0, false, [], body)); \
         val tree = PolyML.PrettyBlock (0, false, [], blocks); \
         val _ = PolyML.prettyPrint (fn _ => (), 80) tree;",
        )
        .unwrap_err();
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
}

#[test]
fn printer_same_structure_opaque_identity_is_hidden_immediately() {
    let vm = evaluate(
        "structure Leak = struct \
           structure Secret :> sig type t val item: t end = \
             struct type t = string val item = \"private-marker\" end; \
           val tree = PolyML.prettyRepresentation (Secret.item, 8) \
         end; \
         val hidden = case Leak.tree of \
           PolyML.PrettyString value => value | _ => \"\";",
    );
    assert_eq!(vm.lookup_value("hidden").unwrap().and_then(Value::as_text), Some("<opaque>"),);
}

#[test]
fn printer_generic_constructor_preserves_opaque_parameter_dispatch() {
    let vm = evaluate(
        "datatype 'a wrap = Wrap of 'a; \
         structure Secret :> sig type t val item: t end = \
           struct type t = string val item = \"private-marker\" end; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn (_: Secret.t) => PolyML.PrettyString \"<redacted>\"); \
         val output = ref \"\"; \
         val tree = PolyML.prettyRepresentation (Wrap Secret.item, 8); \
         val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 80) tree; \
         val protected = !output = \"Wrap <redacted>\";",
    );
    assert!(boolean(&vm, "protected"));
}

#[test]
fn printer_higher_order_registration_rejects_weak_target() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "pretty-higher-order-weak.sml",
            "val saved = ref []; \
         val _ = List.app PolyML.addPrettyPrinter \
           [fn depth => fn pretty => fn xs => \
             (saved := xs; case xs of [] => PolyML.PrettyString \"\" \
              | x :: _ => pretty (x, depth))];",
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn printer_saved_weak_type_refines_to_later_opaque_identity() {
    let vm = evaluate(
        "val saved = ref NONE; \
         fun render () = case !saved of \
           NONE => PolyML.PrettyString \"none\" \
         | SOME value => PolyML.prettyRepresentation (value, 8); \
         structure Secret :> sig type t val item: t end = \
           struct type t = string val item = \"private-marker\" end; \
         val _ = saved := SOME Secret.item; \
         val hidden = case render () of \
           PolyML.PrettyString value => value | _ => \"\";",
    );
    assert_eq!(vm.lookup_value("hidden").unwrap().and_then(Value::as_text), Some("<opaque>"),);
}

#[test]
fn printer_saved_weak_type_refines_to_registered_int_printer() {
    let vm = evaluate(
        "val saved = ref NONE; \
         fun render () = case !saved of \
           NONE => PolyML.PrettyString \"none\" \
         | SOME value => PolyML.prettyRepresentation (value, 8); \
         val hits = ref 0; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn (_: int) => \
             (hits := !hits + 1; PolyML.PrettyString \"int\")); \
         val _ = saved := SOME 1; val _ = render (); \
         val refined_hit = !hits = 1;",
    );
    assert!(boolean(&vm, "refined_hit"));
}
#[test]
fn printer_opaque_views_cover_records_references_and_native_partials() {
    let vm = evaluate(
        "structure A :> sig \
           type t val x: t \
           val callbacks: {run: t -> int} \
           val callback_ref: (t -> int) ref \
           val partial: t -> int \
         end = struct \
           datatype t = T val x = T \
           val callbacks = {run = fn (_: t) => 1} \
           val callback_ref = ref (fn (_: t) => 2) \
           val partial = (fn (_: t) => 3) o (fn value => value) \
         end; \
         val record_result = (#run A.callbacks) A.x; \
         val ref_result = (!A.callback_ref) A.x; \
         val partial_result = A.partial A.x; \
         val views_work = record_result = 1 andalso ref_result = 2 \
           andalso partial_result = 3;",
    );
    assert!(boolean(&vm, "views_work"));
}

#[test]
fn printer_option_map_forwards_compiler_certified_callback_type() {
    let vm = evaluate(
        "val mapped = Option.map PolyML.prettyRepresentation (SOME (1, 5)); \
         val option_map_worked = case mapped of \
           SOME (PolyML.PrettyString \"1\") => true | _ => false;",
    );
    assert!(boolean(&vm, "option_map_worked"));
}

#[test]
fn public_apply_rejects_polymorphic_reference_update_before_mutation() {
    let mut vm = evaluate(
        "val saved = ref 0; fun put reference value = reference := value; \
         val hits = ref 0; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn (_: int) => \
             (hits := !hits + 1; PolyML.PrettyString \"int\"));",
    );
    let put = vm.lookup_value("put").unwrap().unwrap().clone();
    let saved = vm.lookup_value("saved").unwrap().unwrap().clone();
    let error = vm.apply(&put, &[saved, Value::text("not-an-int")]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate(
        "polymorphic-host-result.sml",
        "val saved_unchanged = !saved = 0; \
         val _ = List.map PolyML.prettyRepresentation [(!saved, 8)]; \
         val one_legitimate_hit = !hits = 1;",
    )
    .unwrap();
    assert!(boolean(&vm, "saved_unchanged"));
    assert!(boolean(&vm, "one_legitimate_hit"));
}

#[test]
fn public_apply_polymorphic_native_update_rejects_before_array_mutation() {
    let mut vm = evaluate("val items = Array.array (1, 0);");
    let update = vm.lookup_value("Array.update").unwrap().unwrap().clone();
    let items = vm.lookup_value("items").unwrap().unwrap().clone();
    let input = Value::tuple(vec![items, Value::int(0), Value::text("not-an-int")]);
    let error = vm.apply(&update, &[input]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("native-array-check.sml", "val unchanged = Array.sub (items, 0) = 0;").unwrap();
    assert!(boolean(&vm, "unchanged"));
}

#[test]
fn public_apply_monomorphic_callback_mismatch_rejects_before_reference_mutation() {
    let mut vm = evaluate(
        "val saved = ref 0; \
         fun store_result (callback: unit -> int) = saved := callback (); \
         fun wrong () = \"not-an-int\";",
    );
    let store = vm.lookup_value("store_result").unwrap().unwrap().clone();
    let wrong = vm.lookup_value("wrong").unwrap().unwrap().clone();
    let error = vm.apply(&store, &[wrong]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("callback-check.sml", "val unchanged = !saved = 0;").unwrap();
    assert!(boolean(&vm, "unchanged"));
}

#[test]
fn printer_mutating_array_from_element_callback_returns_updated_value() {
    let vm = evaluate(
        "val items = Array.array (1, 1); val hits = ref 0; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn (_: int) => \
             (hits := !hits + 1; Array.update (items, 0, 2); \
              PolyML.PrettyString \"int\")); \
         val tree = PolyML.prettyRepresentation (items, 8); \
         val changed = Array.sub (items, 0) = 2 andalso !hits = 1;",
    );
    assert!(boolean(&vm, "changed"));
}

#[test]
fn public_apply_exception_wrong_payload_rejects_before_construction() {
    let mut vm = evaluate("exception E of int; fun consume (E x) = x | consume _ = 0;");
    let constructor = vm.lookup_value("E").unwrap().unwrap().clone();
    let error = vm.apply(&constructor, &[Value::text("wrong")]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    let valid = vm.apply(&constructor, &[Value::int(7)]).unwrap();
    let consume = vm.lookup_value("consume").unwrap().unwrap().clone();
    assert_eq!(vm.apply(&consume, &[valid]).unwrap().as_int(), Some(7));
}

#[test]
fn public_apply_exception_function_as_exception_rejects_before_effect() {
    let mut vm = evaluate(
        "exception E of int; val hits = ref 0; \
         fun consume (_: exn) = (hits := !hits + 1; ());",
    );
    let constructor = vm.lookup_value("E").unwrap().unwrap().clone();
    let consume = vm.lookup_value("consume").unwrap().unwrap().clone();
    let error = vm.apply(&consume, &[constructor]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("exception-effects.sml", "val unchanged = !hits = 0;").unwrap();
    assert!(boolean(&vm, "unchanged"));
}

#[test]
fn public_apply_datatype_wrong_payload_rejects_before_construction() {
    let mut vm = evaluate("datatype item = Item of int; fun consume (Item x) = x;");
    let constructor = vm.lookup_value("Item").unwrap().unwrap().clone();
    let error = vm.apply(&constructor, &[Value::text("wrong")]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    let valid = vm.apply(&constructor, &[Value::int(9)]).unwrap();
    let consume = vm.lookup_value("consume").unwrap().unwrap().clone();
    assert_eq!(vm.apply(&consume, &[valid]).unwrap().as_int(), Some(9));
}

#[test]
fn printer_resealed_record_preserves_old_alias_and_new_export() {
    let vm = evaluate(
        "structure A :> sig type t val x: t val callbacks: {run: t -> int} end = \
           struct type t = int val x = 1 val callbacks = {run = fn (_: t) => 7} end; \
         structure B :> sig type t val x: t val callbacks: {run: t -> int} end = \
           struct type t = A.t val x = A.x val callbacks = A.callbacks end; \
         val old_result = (#run A.callbacks) A.x; \
         val new_result = (#run B.callbacks) B.x;",
    );
    assert_eq!(vm.lookup_value("old_result").unwrap().and_then(Value::as_int), Some(7));
    assert_eq!(vm.lookup_value("new_result").unwrap().and_then(Value::as_int), Some(7));
}

#[test]
fn public_apply_foreign_ml_callable_revokes_before_type_lookup() {
    let first = evaluate(
        "val plain = fn (x: int) => x; \
         fun curried (x: int) (y: int) = x + y; \
         val partial = curried 1;",
    );
    for name in ["plain", "curried", "partial"] {
        let callable = first.lookup_value(name).unwrap().unwrap().clone();
        let mut second = Vm::new(DenyHost);
        let error = second.apply(&callable, &[Value::int(2)]).unwrap_err();
        assert_eq!(error.kind, MlErrorKind::HostFailure, "{name}: {error}");
        assert_eq!(second.check_stop().unwrap_err().kind, MlErrorKind::Stopped);
    }
}
