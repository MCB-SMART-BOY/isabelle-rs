use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("pretty-printer-contract.sml", source)
        .expect("pretty-printer program should evaluate");
    vm
}

fn text<'a>(vm: &'a Vm, name: &str) -> &'a str {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_text).expect("string binding")
}

fn boolean(vm: &Vm, name: &str) -> bool {
    vm.lookup_value(name).expect("active VM").and_then(Value::as_bool).expect("boolean binding")
}

#[test]
fn printer_opaque_and_same_shape_types_dispatch_by_generative_identity() {
    let vm = evaluate(
        r#"
        fun render value =
          let val output = ref ""
              val tree = PolyML.prettyRepresentation (value, 8)
              val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 76) tree
          in !output end;
        datatype raw = Raw of string;
        val _ = PolyML.addPrettyPrinter
          (fn _ => fn _ => fn Raw text => PolyML.PrettyString ("raw:" ^ text));
        signature TOKEN = sig type t val make: string -> t val render_inside: t -> string end;
        structure Token :> TOKEN = struct
          datatype t = Token of string;
          val _ = PolyML.addPrettyPrinter
            (fn _ => fn _ => fn Token text => PolyML.PrettyString ("token:" ^ text));
          val make = Token;
          val render_inside = render
        end;
        val raw_output = render (Raw "same");
        val token_output = render (Token.make "same");
        val hidden_output = Token.render_inside (Token.make "inside");
        "#,
    );
    assert_eq!(text(&vm, "raw_output"), "raw:same");
    assert_eq!(text(&vm, "token_output"), "token:same");
    assert_eq!(text(&vm, "hidden_output"), "token:inside");
}

#[test]
fn printer_functor_instances_and_aliases_keep_distinct_dispatch() {
    let vm = evaluate(
        r#"
        fun render value =
          let val output = ref ""
              val tree = PolyML.prettyRepresentation (value, 6)
              val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 76) tree
          in !output end;
        signature ARG = sig val label: string end;
        structure FirstArg = struct val label = "first" end;
        structure SecondArg = struct val label = "second" end;
        functor Make(X: ARG) = struct
          datatype t = Item;
          val item = Item;
          val _ = PolyML.addPrettyPrinter
            (fn _ => fn _ => fn Item => PolyML.PrettyString X.label)
        end;
        structure First = Make(FirstArg);
        structure Second = Make(SecondArg);
        val renamed_pp = PolyML.addPrettyPrinter;
        val renamed_representation = PolyML.prettyRepresentation;
        datatype alias_target = AliasTarget;
        val _ = renamed_pp
          (fn _ => fn _ => fn AliasTarget => PolyML.PrettyString "alias");
        fun render_alias value =
          let val output = ref ""
              val tree = renamed_representation (value, 4)
              val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 76) tree
          in !output end;
        val first_output = render First.item;
        val second_output = render Second.item;
        val alias_output = render_alias AliasTarget;
        "#,
    );
    assert_eq!(text(&vm, "first_output"), "first");
    assert_eq!(text(&vm, "second_output"), "second");
    assert_eq!(text(&vm, "alias_output"), "alias");
}

#[test]
fn printer_parameter_callback_uses_current_nested_printer_and_depth() {
    let vm = evaluate(
        r#"
        fun render value depth =
          let val output = ref ""
              val tree = PolyML.prettyRepresentation (value, depth)
              val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 76) tree
          in !output end;
        datatype 'a box = Box of 'a;
        val _ = PolyML.addPrettyPrinter
          (fn depth => fn pretty => fn Box value => pretty (value, depth - 1));
        val _ = PolyML.addPrettyPrinter
          (fn depth => fn _ => fn (_: int) => PolyML.PrettyString ("old:" ^ Int.toString depth));
        val before_replacement = render (Box 3) 7;
        val _ = PolyML.addPrettyPrinter
          (fn depth => fn _ => fn (_: int) => PolyML.PrettyString ("new:" ^ Int.toString depth));
        val after_replacement = render (Box 3) 7;
        val zero_depth = render (Box 3) 0;
        "#,
    );
    assert_eq!(text(&vm, "before_replacement"), "old:6");
    assert_eq!(text(&vm, "after_replacement"), "new:6");
    assert_eq!(text(&vm, "zero_depth"), "...");
}

#[test]
fn printer_multiple_parameter_callbacks_keep_types_and_depths_distinct() {
    let vm = evaluate(
        r#"
        fun render value =
          let val output = ref ""
              val tree = PolyML.prettyRepresentation (value, 9)
              val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 76) tree
          in !output end;
        datatype ('a, 'b) pair_box = PairBox of 'a * 'b;
        val _ = PolyML.addPrettyPrinter
          (fn depth => fn (pretty_left, pretty_right) => fn PairBox (left, right) =>
            PolyML.PrettyBlock
              (0, false, [],
               [pretty_left (left, depth - 1), PolyML.PrettyString "/",
                pretty_right (right, depth - 2)]));
        val _ = PolyML.addPrettyPrinter
          (fn depth => fn _ => fn (_: int) =>
            PolyML.PrettyString ("int:" ^ Int.toString depth));
        val _ = PolyML.addPrettyPrinter
          (fn depth => fn _ => fn (_: string) =>
            PolyML.PrettyString ("string:" ^ Int.toString depth));
        val pair_output = render (PairBox (3, "x"));
        "#,
    );
    assert_eq!(text(&vm, "pair_output"), "int:8/string:7");
}

#[test]
fn printer_nested_opaque_values_do_not_expose_representations() {
    let vm = evaluate(
        r#"
        fun render value =
          let val output = ref ""
              val tree = PolyML.prettyRepresentation (value, 8)
              val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 76) tree
          in !output end;
        structure Secret :> sig type t val item: t end =
        struct datatype t = Hidden of string val item = Hidden "private-marker" end;
        val hidden_list = render [Secret.item];
        val _ = PolyML.addPrettyPrinter
          (fn _ => fn _ => fn (_: Secret.t) => PolyML.PrettyString "<redacted>");
        val redacted_list = render [Secret.item];
        "#,
    );
    assert!(!text(&vm, "hidden_list").contains("private-marker"));
    assert!(text(&vm, "hidden_list").contains("<opaque>"));
    assert_eq!(text(&vm, "redacted_list"), "[<redacted>]");
}

#[test]
fn printer_opaque_exported_function_accepts_its_public_value() {
    let vm = evaluate(
        "structure A :> sig type t val x: t val f: t -> int end = \
         struct datatype t = T val x = T fun f (_: t) = 1 end; \
         val opaque_result = A.f A.x;",
    );
    assert_eq!(vm.lookup_value("opaque_result").unwrap().and_then(Value::as_int), Some(1),);
}

#[test]
fn printer_fallback_uses_certified_datatype_argument_types() {
    let vm = evaluate(
        "fun render value = \
           let val output = ref \"\" \
               val tree = PolyML.prettyRepresentation (value, 5) \
               val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 76) tree \
           in !output end; \
         datatype 'a wrapper = Wrap of 'a list; \
         val fallback_output = render (Wrap [1, 2]);",
    );
    assert_eq!(text(&vm, "fallback_output"), "Wrap [1, 2]");
}

#[test]
fn printer_scoped_datatype_uses_certified_argument_types() {
    let vm = evaluate(
        "fun render value = \
           let val output = ref \"\" \
               val tree = PolyML.prettyRepresentation (value, 5) \
               val _ = PolyML.prettyPrint (fn text => output := !output ^ text, 76) tree \
           in !output end; \
         structure W = struct datatype 'a wrapper = Wrap of 'a list end; \
         val module_output = render (W.Wrap [1, 2]); \
         val local_output = let datatype item = Item of int in render (Item 3) end;",
    );
    assert_eq!(text(&vm, "module_output"), "Wrap [1, 2]");
    assert_eq!(text(&vm, "local_output"), "Item 3");
}

#[test]
fn printer_escaping_closure_retains_captured_type_instantiation() {
    let vm = evaluate(
        "val hits = ref 0; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn (_: int) => \
             (hits := !hits + 1; PolyML.PrettyString \"int\")); \
         fun make x = fn () => PolyML.prettyRepresentation (x, 5); \
         val thunk = make 7; val _ = thunk (); val captured_hits = !hits;",
    );
    assert_eq!(vm.lookup_value("captured_hits").unwrap().and_then(Value::as_int), Some(1),);
}

#[test]
fn printer_basis_higher_order_callback_keeps_argument_evidence() {
    let vm = evaluate(
        "val trees = List.map PolyML.prettyRepresentation [(1, 5)]; \
         val mapped_count = List.length trees;",
    );
    assert_eq!(vm.lookup_value("mapped_count").unwrap().and_then(Value::as_int), Some(1),);
}
#[test]
fn printer_callbacks_preserve_side_effect_exception_and_gc_roots() {
    let mut vm = evaluate(
        r#"
        fun render value = PolyML.prettyRepresentation (value, 5);
        datatype event = Event;
        val calls = ref 0;
        val _ = PolyML.addPrettyPrinter
          (fn _ => fn _ => fn Event =>
            (calls := !calls + 1; PolyML.PrettyString "event"));
        val _ = render Event;
        val _ = render Event;
        val called_twice = !calls = 2;
        exception Printer_Failure;
        datatype failure = Failure;
        val _ = PolyML.addPrettyPrinter
          (fn _ => fn _ => fn Failure => raise Printer_Failure);
        val caught = (render Failure; false) handle Printer_Failure => true;
        datatype rooted = Rooted;
        val old_weak =
          let val token = ref 17
              val weak = Weak.weak (SOME token)
              val _ = PolyML.addPrettyPrinter
                (fn _ => fn _ => fn Rooted =>
                  PolyML.PrettyString (Int.toString (!token)))
          in weak end;
        "#,
    );
    assert!(boolean(&vm, "called_twice"));
    assert!(boolean(&vm, "caught"));
    vm.collect_garbage().expect("registered callback is an explicit VM root");
    vm.evaluate(
        "printer-root-live.sml",
        "val rooted_live = (case !old_weak of SOME (ref 17) => true | _ => false);",
    )
    .unwrap();
    assert!(boolean(&vm, "rooted_live"));
    vm.evaluate(
        "printer-replace.sml",
        "val _ = PolyML.addPrettyPrinter (fn _ => fn _ => fn Rooted => PolyML.PrettyString \"new\");",
    )
    .unwrap();
    vm.collect_garbage().expect("replaced callback should release its captured environment");
    vm.evaluate("printer-root-released.sml", "val rooted_released = !old_weak = NONE;").unwrap();
    assert!(boolean(&vm, "rooted_released"));
}

#[test]
fn printer_invalid_callback_shapes_reject_before_side_effects() {
    for source in [
        "val marker = ref 0; val _ = PolyML.addPrettyPrinter \
           (let val _ = marker := 1 in \
              fn _ => fn (flag: bool) => fn (_: int) => \
                if flag then PolyML.PrettyString \"yes\" else PolyML.PrettyString \"no\" \
            end);",
        "datatype ('a, 'b) duo = Duo of 'a * 'b; \
         val marker = ref 0; val _ = PolyML.addPrettyPrinter \
           (let val _ = marker := 1 in \
              fn _ => fn (_: ('a * int -> PolyML.pretty) * \
                               ('b * int -> PolyML.pretty) * bool) => \
                fn (_: ('a, 'b) duo) => PolyML.PrettyString \"bad\" \
            end);",
        "datatype ('a, 'b) duo = Duo of 'a * 'b; \
         val marker = ref 0; val _ = PolyML.addPrettyPrinter \
           (let val _ = marker := 1 in \
              fn _ => fn (_: ('a * int -> PolyML.pretty) * \
                               ('a * int -> PolyML.pretty)) => \
                fn (_: ('a, 'a) duo) => PolyML.PrettyString \"bad\" \
            end);",
        "val marker = ref 0; val _ = PolyML.addPrettyPrinter \
           (let val _ = marker := 1 in \
              fn _ => fn (_: int * int -> PolyML.pretty) => \
                fn (_: int list) => PolyML.PrettyString \"ints\" \
            end);",
    ] {
        let mut vm = Vm::new(DenyHost);
        let error = vm.evaluate("invalid-printer-shape.sml", source).unwrap_err();
        assert_eq!(error.kind, MlErrorKind::Type);
        vm.evaluate("invalid-printer-marker.sml", "val marker_untouched = !marker = 0;").unwrap();
        assert!(boolean(&vm, "marker_untouched"));
    }
}

#[test]
fn printer_public_wrapper_rejects_untyped_argument_before_callback() {
    let mut vm = evaluate(
        "val wrapper_hits = ref 0; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn _ => fn (_: int) => \
             (wrapper_hits := !wrapper_hits + 1; PolyML.PrettyString \"int\")); \
         fun render_int (value: int) = PolyML.prettyRepresentation (value, 8);",
    );
    let render = vm.lookup_value("render_int").unwrap().unwrap().clone();
    let error = vm.apply(&render, &[Value::text("not-an-int")]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("wrapper-hits.sml", "val wrapper_untouched = !wrapper_hits = 0;").unwrap();
    assert!(boolean(&vm, "wrapper_untouched"));
}

#[test]
fn printer_shared_dag_and_huge_break_are_bounded() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "pretty-dag-budget.sml",
            "val tree = ref (PolyML.PrettyString \"x\"); \
         val count = ref 0; \
         val _ = while !count < 40 do \
           (tree := PolyML.PrettyBlock (0, false, [], [!tree, !tree]); \
            count := !count + 1); \
         val _ = PolyML.prettyPrint (fn _ => (), 80) (!tree);",
        )
        .unwrap_err();
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));

    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "pretty-break-budget.sml",
            "val _ = PolyML.prettyPrint (fn _ => (), 1099511627776) \
           (PolyML.PrettyBreak (1099511627776, 0));",
        )
        .unwrap_err();
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
}

#[test]
fn printer_wrong_parameter_and_untyped_rust_invocation_fail_explicitly() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "pretty-wrong-parameter.sml",
            "datatype 'a box = Box of 'a; \
         val _ = PolyML.addPrettyPrinter \
           (fn _ => fn (pretty: string * int -> PolyML.pretty) => fn Box value => \
             pretty (Int.toString value, 1));",
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);

    let pretty = vm.lookup_value("PolyML.prettyRepresentation").unwrap().unwrap().clone();
    let error = vm.apply(&pretty, &[Value::tuple(vec![Value::int(1), Value::int(2)])]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
}

#[test]
fn printer_ambiguous_registration_rejects_before_argument_effects() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("pretty-marker.sml", "val printer_marker = ref 0;").unwrap();
    let error = vm
        .evaluate(
            "pretty-ambiguous.sml",
            "val _ = PolyML.addPrettyPrinter \
           (let val _ = printer_marker := 1 \
            in fn _ => fn _ => fn value => PolyML.PrettyString \"ambiguous\" end);",
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("pretty-marker-result.sml", "val marker_untouched = !printer_marker = 0;").unwrap();
    assert!(boolean(&vm, "marker_untouched"));
}

#[test]
fn printer_type_directed_native_rejects_cross_vm_invocation() {
    let first_vm = Vm::new(DenyHost);
    let pretty = first_vm.lookup_value("PolyML.prettyRepresentation").unwrap().unwrap().clone();
    let mut other_vm = Vm::new(DenyHost);
    let error =
        other_vm.apply(&pretty, &[Value::tuple(vec![Value::int(1), Value::int(2)])]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::HostFailure);
}
