use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

fn evaluate_integer(source: &str, name: &str) -> i64 {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("fixity.sml", source).unwrap();
    vm.lookup_value(name).unwrap().and_then(Value::as_int).unwrap()
}

#[test]
fn fixity_pipeline_and_composition_execute_original_basics_fragments() {
    let source = r#"
        infix 1 |> |-> |>> ||> ||>>
        infix 1 #> #-> #>> ##> ##>>
        signature OPS = sig
          val |> : 'a * ('a -> 'b) -> 'b
          val |-> : ('c * 'a) * ('c -> 'a -> 'b) -> 'b
          val #> : ('a -> 'b) * ('b -> 'c) -> 'a -> 'c
        end;
        structure Ops: OPS = struct
          fun x |> f = f x;
          fun (x, y) |-> f = f x y;
          fun (f #> g) x = x |> f |> g;
        end;
        open Ops;
        val result = ((fn x => x + 1) #> (fn x => x * 2)) 3;
        val qualified = op Ops.#> (fn x => x + 1, fn x => x * 2) 3;
        val routed = (2, 3) |-> (fn x => fn y => x + y);
        fun op + (x, y) = x - (0 - y);
        val rebound = op + (4, 5);
    "#;
    assert_eq!(evaluate_integer(source, "result"), 8);
    assert_eq!(evaluate_integer(source, "qualified"), 8);
    assert_eq!(evaluate_integer(source, "rebound"), 9);
    assert_eq!(evaluate_integer(source, "routed"), 5);
}
#[test]
fn fixity_basics_result_views_execute_original_fragments() {
    let source = "fun `f = fn x => (f x, x); \
        fun tap f = fn x => (f x; x); \
        val (result, original) = ` (fn x => x + 2) 3; \
        val touched = tap (fn x => x + 1) 4;";
    assert_eq!(evaluate_integer(source, "result"), 5);
    assert_eq!(evaluate_integer(source, "original"), 3);
    assert_eq!(evaluate_integer(source, "touched"), 4);
}

#[test]
fn fixity_symbol_tokens_preserve_comment_and_character_boundaries() {
    assert_eq!(
        evaluate_integer(
            r##"infix 1 |>; fun x |> f = f x;
           val letter = #"a";
           val result = 3|>(* outer (* nested *) comment *)(fn x => x + 2);"##,
            "result",
        ),
        5
    );
}

#[test]
fn fixity_levels_associativity_and_application_compute_values() {
    assert_eq!(
        evaluate_integer(
            "infix 0 %% ; infixr 9 ***; fun (x %% y) = x - y; \
         fun (x *** y) = x - y; fun twice x = x * 2; \
         val result = 20 %% 5 %% 2 + twice 3 *** 1;",
            "result",
        ),
        8
    );
    assert_eq!(
        evaluate_integer(
            "infixr 0 %% ; fun (x %% y) = x - y; val result = 20 %% 5 %% 2;",
            "result",
        ),
        17
    );
}
#[test]
fn fixity_default_level_and_boolean_connectives_respect_short_circuit() {
    assert_eq!(
        evaluate_integer(
            "infix %%; fun (x %% y) = x - y; \
         val result = if false andalso (1 div 0 = 0) orelse true \
           then (12 %% 3 %% 1) else 0;",
            "result",
        ),
        8
    );
}

#[test]
fn fixity_nonfix_op_and_symbolic_pattern_bind_values() {
    assert_eq!(
        evaluate_integer(
            "nonfix +; val + = fn (x, y) => x - y; \
         val pair = (op +, 4); val (op +, n) = pair; val result = op + (n, 1);",
            "result",
        ),
        3
    );
}

#[test]
fn fixity_scopes_export_only_local_body_and_persist_between_evaluations() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "first.sml",
        "infix 1 |>; fun x |> f = f x; \
        local infixr 0 %% in infixr 0 %%; fun (x %% y) = x - y end; \
        local nonfix |> in val isolated = 1 end; \
        structure Private = struct nonfix |>; val op |> = fn (x,y) => x - y end; \
        val internal = let nonfix |>; val op |> = fn (x,y) => x - y \
          in op |> (8, 3) end;",
    )
    .unwrap();
    vm.evaluate("second.sml", "val result = 12 %% 3 %% 1; val piped = 2 |> (fn x => x + 5);")
        .unwrap();
    assert_eq!(vm.lookup_value("result").unwrap().and_then(Value::as_int), Some(10));
    assert_eq!(vm.lookup_value("piped").unwrap().and_then(Value::as_int), Some(7));
    assert_eq!(vm.lookup_value("internal").unwrap().and_then(Value::as_int), Some(5));
}

#[test]
fn fixity_rejects_invalid_precedence_and_mixed_associativity() {
    let mut vm = Vm::new(DenyHost);
    for source in [
        "infix 10 %%",
        "infixr 11 %%",
        "infix ~1 %%",
        "infix ~0 %%",
        "infix 1 ++; infixr 1 **; val bad = 1 ++ 2 ** 3;",
        "infixr 1 ++; infix 1 **; val bad = 1 ++ 2 ** 3;",
    ] {
        let error = vm.evaluate("bad-fixity.sml", source).unwrap_err();
        assert_eq!(error.kind, MlErrorKind::Syntax, "{source}");
        assert_eq!(error.span.source_name, "bad-fixity.sml");
        assert!(error.span.end > error.span.start, "{source}");
    }
}

#[test]
fn fixity_failed_evaluation_does_not_commit_unexecuted_declarations() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("setup.sml", "exception Boom; infix 0 %%; fun (x %% y) = x - y;").unwrap();
    let error = vm.evaluate("failure.sml", "val _ = raise Boom; nonfix %%; ").unwrap_err();
    assert!(matches!(error.kind, MlErrorKind::Exception(_)));
    vm.evaluate("after.sml", "val answer = 4 %% 1;").unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(3));
}
