use isabelle_rs::ml::{DenyHost, MlErrorKind, Vm};

fn evaluate_integer(source: &str) -> i64 {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("flexible-record.sml", source).expect("valid record constraints");
    vm.lookup_value("result").expect("active VM").unwrap().as_int().unwrap()
}

fn assert_type_error(source: &str) {
    let mut vm = Vm::new(DenyHost);
    let error = vm.evaluate("flexible-record.sml", source).expect_err("invalid record type");
    assert_eq!(error.kind, MlErrorKind::Type, "{error}");
}

#[test]
fn flexible_record_multiple_selectors_share_union_and_result_types() {
    assert_eq!(evaluate_integer("val result = (fn r => #a r + #b r) {a=2,b=3};"), 5);
}

#[test]
fn flexible_record_case_constructor_field_constraints_close_at_scrutinee() {
    assert_eq!(
        evaluate_integer("val result = case SOME {a=2,b=3} of SOME r => #a r + #b r | NONE => 0;"),
        5
    );
}

#[test]
fn flexible_record_let_alias_shares_constraints_until_application() {
    assert_eq!(
        evaluate_integer(
            "val result = (fn r => let val alias = r in #a alias + #b r end) {a=2,b=3};"
        ),
        5
    );
}

#[test]
fn flexible_record_closure_captures_shared_row_until_outer_application() {
    assert_eq!(
        evaluate_integer(
            "val result = (fn r => let val read = fn () => #a r in read () + #b r end) {a=2,b=3};"
        ),
        5
    );
}

#[test]
fn flexible_record_missing_selector_field_is_rejected() {
    assert_type_error("val result = (fn r => #a r + #b r) {a=2};");
}

#[test]
fn flexible_record_repeated_label_conflicting_types_are_rejected() {
    assert_type_error("val result = (fn r => if #a r then #a r + 1 else 0) {a=true};");
}

#[test]
fn flexible_record_selector_result_tracks_the_closed_field_type() {
    assert_type_error("val result = ((fn r => #a r) {a=true,b=3}) + 1;");
}

#[test]
fn flexible_record_closed_annotation_rejects_extra_and_missing_fields() {
    assert_type_error("val result = (fn (r : {a:int,b:int}) => #a r) {a=2,b=3,c=4};");
    assert_type_error("val result = (fn (r : {a:int,b:int}) => #a r) {a=2};");
}

#[test]
fn flexible_record_equality_constraints_propagate_to_field_types() {
    assert_eq!(
        evaluate_integer("val result = if (fn r => #a r = #b r) {a=2,b=2} then 5 else 0;"),
        5
    );
    assert_type_error("val bad = (fn r => #a r = #b r) {a=(fn x => x),b=(fn x => x)};");
}

#[test]
fn flexible_record_unresolved_selector_cannot_be_generalized() {
    assert_type_error("val select = fn r => #a r;");
}

#[test]
fn flexible_record_self_application_rejects_infinite_type() {
    assert_type_error("val result = fn r => #a r r;");
}

#[test]
fn flexible_record_empty_open_pattern_rejects_nonrecord_argument() {
    assert_type_error("val result = (fn {...} => 1) 0;");
}

#[test]
fn flexible_record_local_selector_closes_within_declaration() {
    assert_eq!(
        evaluate_integer("local val select = fn r => #a r in val result = select {a=1} end;"),
        1
    );
}

#[test]
fn flexible_record_invalid_local_rejects_before_reference_effect() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("setup.sml", "val marker = ref 0;").unwrap();
    let error = vm
        .evaluate("invalid-local.sml", "local val _ = marker := 1 in val bad = fn r => #a r end;")
        .unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("observe.sml", "val result = !marker;").unwrap();
    assert_eq!(vm.lookup_value("result").unwrap().unwrap().as_int(), Some(0));
}

#[test]
fn flexible_record_local_polymorphic_selector_instantiates_field_types() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "polymorphic-row.sml",
        "val result = let val g = #foo val _ = g {foo=13} in g {foo=\"yes\"} end;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("result").unwrap().unwrap().as_bytes(), Some(b"yes".as_slice()));
}
