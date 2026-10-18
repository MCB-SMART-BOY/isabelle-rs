use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

#[test]
fn functor_repeated_nested_application_keeps_each_closure_type_identity() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "nested-functors.sml",
        "signature EMPTY = sig end;
         functor Make(X: EMPTY) = struct
           datatype t = Token of int;
           fun make n = Token n;
           fun read (Token n) = n;
         end;
         structure Both = struct
           structure A = Make(struct end);
           structure B = Make(struct end);
           val a = A.make 3;
           val b = B.make 4;
           val total = A.read a + B.read b;
         end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("Both.total").unwrap().and_then(Value::as_int), Some(7));
    let error =
        vm.evaluate("foreign-functor-value.sml", "val bad = Both.A.read Both.b;").unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
}
