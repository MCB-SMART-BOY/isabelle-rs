use isabelle_rs::ml::{DenyHost, MlErrorKind, Value, Vm};

fn assert_type_rejected(vm: &mut Vm, name: &str, source: &str) {
    let error = vm.evaluate(name, source).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type, "{error}");
}

#[test]
fn datatype_distinct_declarations_reject_cross_type_annotation() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "distinct.sml",
        "datatype first = First; datatype second = Second; val ok = (First : first);",
    )
    .unwrap();
    assert!(vm.lookup_value("ok").unwrap().is_some());
    assert_type_rejected(&mut vm, "distinct-bad.sml", "val bad = (First : second);");
}

#[test]
fn datatype_replication_preserves_type_and_constructor_identity() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "replicate.sml",
        "structure A = struct datatype t = T end;
        datatype u = datatype A.t;
        val ok = case (T : u) of T => 17;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("ok").unwrap().and_then(Value::as_int), Some(17));
}

#[test]
fn signature_abstract_types_seal_each_instance_without_leaking_constructor_status() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "sealed.sml",
        "signature TOKEN = sig type t; val Wrap : t end;
        structure One :> TOKEN = struct datatype t = Wrap end;
        structure Two :> TOKEN = struct datatype t = Wrap end;
        val ok = (One.Wrap : One.t);",
    )
    .unwrap();
    let one = vm.lookup_structure("One").unwrap().unwrap().lookup_type_stamp("t");
    let two = vm.lookup_structure("Two").unwrap().unwrap().lookup_type_stamp("t");
    assert_ne!(one, two);
    assert_type_rejected(&mut vm, "sealed-mix.sml", "val bad = (One.Wrap : Two.t);");
    assert_type_rejected(&mut vm, "sealed-status.sml", "val bad = case One.Wrap of One.Wrap => 1;");
}

#[test]
fn signature_datatype_spec_exposes_only_declared_constructors() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "datatype-spec.sml",
        "signature SHAPE = sig datatype t = Round end;
        structure Shape : SHAPE = struct datatype t = Round | Square end;
        val ok = case Shape.Round of Shape.Round => 23;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("ok").unwrap().and_then(Value::as_int), Some(23));
    assert_type_rejected(&mut vm, "datatype-spec-hidden.sml", "val bad = Shape.Square;");
}

#[test]
fn signature_include_and_where_type_enforce_manifest_equality() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "included.sml",
        "signature BASE = sig type t; val x : t end;
        signature EXT = sig include BASE; val n : int end where type t = int;
        structure Good : EXT = struct type t = int; val x = 7; val n = 4 end;
        val ok = (Good.x : int);",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("ok").unwrap().and_then(Value::as_int), Some(7));
    assert_type_rejected(
        &mut vm,
        "where-bad.sml",
        "structure Bad : EXT = struct datatype t = Other; val x = Other; val n = 4 end;",
    );
}

#[test]
fn signature_sharing_checks_actual_nominal_structure_members() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "sharing.sml",
        "signature CELL = sig type t; val make : t end;
        signature SHARED = sig structure L : CELL; structure R : CELL;
            sharing type L.t = R.t end;
        structure A = struct datatype t = A; val make = A end;
        structure B = struct datatype t = B; val make = B end;
        structure Good : SHARED = struct structure L = A; structure R = A end;
        structure Sealed :> SHARED = struct structure L = A; structure R = A end;
        structure AliasOne = struct type t = int list; val make = ([] : t) end;
        structure AliasTwo = struct type t = int list; val make = ([] : t) end;
        structure AliasGood : SHARED =
            struct structure L = AliasOne; structure R = AliasTwo end;
        val shared = (Sealed.L.make : Sealed.R.t);",
    )
    .unwrap();
    assert_type_rejected(
        &mut vm,
        "sharing-bad.sml",
        "structure Bad : SHARED = struct structure L = A; structure R = B end;",
    );
}

#[test]
fn functor_applications_generate_distinct_types_and_keep_definition_scope() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "generative.sml",
        "signature ARG = sig type t; val item : t end;
        structure Source = struct datatype t = Old; val item = Old end;
        functor Make(X:ARG) = struct datatype token = Tag of X.t;
            val saved = X.item end;
        structure Earlier = Make(Source);
        structure Source = struct datatype t = New; val item = New end;
        structure Later = Make(Source);
        val ok = (Earlier.Tag Earlier.saved : Earlier.token);",
    )
    .unwrap();
    let earlier = vm.lookup_structure("Earlier").unwrap().unwrap().lookup_type_stamp("token");
    let later = vm.lookup_structure("Later").unwrap().unwrap().lookup_type_stamp("token");
    assert_ne!(earlier, later);
    assert_type_rejected(
        &mut vm,
        "generative-bad.sml",
        "val bad = (Earlier.Tag Earlier.saved : Later.token);",
    );
    assert_type_rejected(&mut vm, "lexical-bad.sml", "val bad = (Earlier.saved : Source.t);");
}

#[test]
fn abstype_hides_private_constructor_but_retains_creator_identity() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "abstype.sml",
        "abstype token = Private of int with
        fun make n = Private n;
        fun read (Private n) = n
        end;
        val ok = read (make 19);",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("ok").unwrap().and_then(Value::as_int), Some(19));
    assert!(vm.lookup_value("Private").unwrap().is_none());
    assert_type_rejected(&mut vm, "abstype-hidden.sml", "val wrong = Private 1;");
}

#[test]
fn closure_preserves_old_structure_identity_after_rebinding() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "old-module.sml",
        "structure State = struct datatype t = Before end;
        val get_old = fn () => State.Before;
        structure State = struct datatype t = After end;
        val old = get_old ();",
    )
    .unwrap();
    assert_type_rejected(&mut vm, "old-module-bad.sml", "val bad = (old : State.t);");
}

#[test]
fn datatype_arity_and_non_equality_are_checked() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "arity.sml",
        "datatype 'a box = Box of 'a;
        datatype callable = Callback of int -> int;
        val ok = (Box 3 : int box);",
    )
    .unwrap();
    assert_type_rejected(&mut vm, "arity-bad.sml", "val bad = (Box 3 : (int, int) box);");
    assert_type_rejected(
        &mut vm,
        "equality-bad.sml",
        "val bad = Callback (fn n => n) = Callback (fn n => n);",
    );
}

#[test]
fn rebinding_constructor_with_same_name_does_not_match_old_value() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "constructor-rebind.sml",
        "datatype earlier = Tagged;
        val old = Tagged; datatype later = Tagged;
        val current = (Tagged : later);",
    )
    .unwrap();
    assert_type_rejected(
        &mut vm,
        "constructor-rebind-bad.sml",
        "val wrong = case old of Tagged => 1;",
    );
}

#[test]
fn builtin_reference_datatype_replication_preserves_constructor_pattern() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "reference-replication.sml",
        "signature REFERENCE = sig datatype ref = datatype ref end;
         structure Refs : REFERENCE = struct datatype ref = datatype ref end;
         val matched = case Refs.ref 31 of Refs.ref n => n;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("matched").unwrap().and_then(Value::as_int), Some(31));
}

#[test]
fn signature_mismatch_reports_source_location() {
    let mut vm = Vm::new(DenyHost);
    let error = vm
        .evaluate(
            "signature-location.sml",
            "signature N = sig val number : int end;
         structure Wrong : N = struct val number = true end;",
        )
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    assert_eq!(error.span.source_name, "signature-location.sml");
    assert!(error.span.start > 0, "{error}");
}

#[test]
fn functor_shorthand_argument_and_opaque_result_keep_type_private() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "functor-result.sml",
        "signature ITEM = sig type t; val item : t end;
        signature RESULT = sig type t; val item : t end;
        functor Build(X:ITEM):>RESULT = struct type t = X.t; val item = X.item end;
        structure Result = Build(type t = int; val item = 42);
        val ok = (Result.item : Result.t);",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("ok").unwrap().and_then(Value::as_int), Some(42));
    assert_type_rejected(&mut vm, "functor-result-bad.sml", "val exposed = (Result.item : int);");
}

#[test]
fn let_abstype_keeps_constructor_private_and_elaboration_consistent() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "let-abstype.sml",
        "val answer = let
        abstype t = Private of int with
          fun unwrap (Private n) = n;
          val create = Private
        end
        in unwrap (create 27) end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(27));
    assert!(vm.lookup_value("Private").unwrap().is_none());
}

#[test]
fn opaque_signature_preserves_only_declared_equality_status() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "equality-signatures.sml",
        "signature ABSTRACT = sig type t; val make : t end;
         signature EQUALITY = sig eqtype t; val make : t end;
         structure Hidden :> ABSTRACT = struct datatype t = K; val make = K end;
         structure Comparable :> EQUALITY = struct datatype t = K; val make = K end;
         val accepted = Comparable.make = Comparable.make;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("accepted").unwrap().and_then(Value::as_bool), Some(true));
    assert_type_rejected(
        &mut vm,
        "opaque-non-equality.sml",
        "val rejected = Hidden.make = Hidden.make;",
    );
}

#[test]
fn signature_unrestricted_value_rejects_equality_only_implementation_before_effects() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("marker.sml", "val marker = ref 0;").unwrap();
    assert_type_rejected(
        &mut vm,
        "bad-equality-signature.sml",
        "signature ANY_EQ = sig val equal : 'a * 'a -> bool end;
         structure Wrong : ANY_EQ = struct
           val _ = marker := 1;
           fun equal (x, y) = x = y
         end;",
    );
    vm.evaluate("marker-after.sml", "val marker_after = !marker;").unwrap();
    assert_eq!(vm.lookup_value("marker_after").unwrap().and_then(Value::as_int), Some(0));
    assert!(vm.lookup_structure("Wrong").unwrap().is_none());
}

#[test]
fn signature_equality_constrained_value_accepts_matching_implementation() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "matching-equality-signature.sml",
        "signature EQ = sig val equal : ''a * ''a -> bool end;
         structure Matching : EQ = struct fun equal (x, y) = x = y end;
         val answer = Matching.equal (3, 3);",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_bool), Some(true));
}

#[test]
fn functor_shared_parameter_types_are_equal_inside_definition() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "shared-parameter.sml",
        "signature CELL = sig type t; val make : t end;
         signature SHARED = sig structure L : CELL; structure R : CELL;
             sharing type L.t = R.t end;
         structure A = struct datatype t = K; val make = K end;
         structure Pair = struct structure L = A; structure R = A end;
         functor Use(X:SHARED) = struct val shared = (X.L.make : X.R.t) end;
         structure Result = Use(Pair);",
    )
    .unwrap();
    assert!(vm.lookup_structure("Result").unwrap().unwrap().lookup_value("shared").is_some());
}

#[test]
fn functor_shared_manifest_parameter_type_matches_abstract_member() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "shared-manifest.sml",
        "signature ABSTRACT = sig type t; val make : t end;
         signature MANIFEST = sig type t = int list; val make : t end;
         signature SHARED = sig structure L : ABSTRACT; structure R : MANIFEST;
             sharing type L.t = R.t end;
         structure A = struct type t = int list; val make = ([] : t) end;
         structure Pair = struct structure L = A; structure R = A end;
         functor Use(X:SHARED) = struct val shared = (X.L.make : X.R.t) end;
         structure Result = Use(Pair);",
    )
    .unwrap();
    assert!(vm.lookup_structure("Result").unwrap().unwrap().lookup_value("shared").is_some());
}

#[test]
fn transparent_signature_specializes_exported_polymorphic_value() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "transparent-signature.sml",
        "signature S = sig val f : int -> int end;
         structure A : S = struct fun f x = x end;",
    )
    .unwrap();
    assert_type_rejected(&mut vm, "transparent-wrong.sml", "val bad = A.f true;");
    vm.evaluate("transparent-valid.sml", "val good = A.f 3;").unwrap();
    assert_eq!(vm.lookup_value("good").unwrap().and_then(Value::as_int), Some(3));
}

#[test]
fn nested_functor_applications_keep_distinct_parameter_elaborations() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "nested-functor-parameters.sml",
        "signature ARG = sig type t; val x : t end;
         functor F(X:ARG) = struct
           val saved = X.x;
           signature EXACT = sig type t = X.t; val x : t end;
           structure Copy : EXACT = X
         end;
         structure Both = struct
           structure A = F(struct type t = int; val x = 1 end);
           structure B = F(struct type t = bool; val x = true end)
         end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("Both.A.Copy.x").unwrap().and_then(Value::as_int), Some(1));
    assert_eq!(vm.lookup_value("Both.B.Copy.x").unwrap().and_then(Value::as_bool), Some(true));
}
