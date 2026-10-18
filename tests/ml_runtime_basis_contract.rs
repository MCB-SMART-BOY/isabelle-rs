use isabelle_rs::ml::{DenyHost, HostBridge, HostFailure, Type, TypeScheme, Value, Vm};
use std::{cell::Cell, rc::Rc};

fn evaluate(source: &str) -> Vm {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate("runtime-basis.sml", source).expect("valid SML should evaluate");
    vm
}

fn integer(vm: &Vm, name: &str) -> i64 {
    vm.lookup_value(name).unwrap().and_then(Value::as_int).expect("integer result")
}

#[test]
fn structure_rebinding_uses_new_value_and_preserves_old_closure() {
    let vm = evaluate(
        "fun old_length xs = List.length xs; \
        structure List = struct fun length xs = 99 end; \
        val current = List.length [1]; val previous = old_length [1];",
    );
    assert_eq!(integer(&vm, "current"), 99);
    assert_eq!(integer(&vm, "previous"), 1);
}

#[test]
fn closure_let_preserves_definition_site_structure_types() {
    let vm = evaluate(
        "structure S = struct val x = 1 end; \
        fun f () = let val y = S.x + 1 in y end; \
        structure S = struct val x = true end; val result = f ();",
    );
    assert_eq!(integer(&vm, "result"), 2);
}

#[test]
fn closure_let_parameter_and_shadowed_structure_remain_lexical() {
    let vm = evaluate(
        "structure S = struct val x = 3 end; \
        fun f amount = let open S val y = x + amount in y end; \
        structure S = struct val x = true end; \
        val result = f 4;",
    );
    assert_eq!(integer(&vm, "result"), 7);
}

#[test]
fn closure_let_local_exception_and_reference_effects_survive() {
    let vm = evaluate(
        "val cell = ref 0; \
        fun f amount = let exception Local; val _ = cell := amount; \
            val result = (raise Local) handle Local => !cell \
            in result end; \
        val result = f 5;",
    );
    assert_eq!(integer(&vm, "result"), 5);
}

#[test]
fn nonexhaustive_case_raises_catchable_match_exception() {
    let vm = evaluate("val result = (case NONE of SOME _ => 0) handle Match => 9;");
    assert_eq!(integer(&vm, "result"), 9);
}

#[test]
fn nonexhaustive_function_raises_catchable_match_exception() {
    let vm = evaluate(
        "fun only_some (SOME _) = 1; \
        val result = (only_some NONE) handle Match => 9;",
    );
    assert_eq!(integer(&vm, "result"), 9);
}

#[test]
fn unmatched_handler_rethrows_original_match_exception() {
    let vm = evaluate(
        "val result = ((case NONE of SOME _ => 0) \
        handle Subscript => 1) handle Match => 2;",
    );
    assert_eq!(integer(&vm, "result"), 2);
}

#[test]
fn builtin_match_identity_survives_identifier_shadowing() {
    let vm = evaluate(
        "exception Alias = Match; exception Match; \
        val result = (case NONE of SOME _ => 0) handle Alias => 9 | Match => 1;",
    );
    assert_eq!(integer(&vm, "result"), 9);
}

#[test]
fn empty_closed_record_and_unit_match_in_both_directions() {
    let vm = evaluate(
        "val from_record = case {} of () => 1; \
        val from_unit = case () of {} => 2; \
        val annotated = ({} : unit);",
    );
    assert_eq!(integer(&vm, "from_record"), 1);
    assert_eq!(integer(&vm, "from_unit"), 2);
    assert!(vm.lookup_value("annotated").unwrap().unwrap().is_unit());
}

#[test]
fn open_empty_record_pattern_accepts_nonempty_record() {
    let vm = evaluate(
        "val result = case {field = 3} of {...} => 7; \
        val from_unit = case () of {...} => 8;",
    );
    assert_eq!(integer(&vm, "result"), 7);
    assert_eq!(integer(&vm, "from_unit"), 8);
}

#[test]
fn signature_value_hides_constructor_status_in_pattern() {
    let vm = evaluate(
        "signature S = sig val NONE : int option end; \
        structure A : S = Option; open A; \
        val result = case 7 of NONE => NONE + 1;",
    );
    assert_eq!(integer(&vm, "result"), 8);
}

#[test]
fn nested_signature_value_hides_constructor_status_in_pattern() {
    let vm = evaluate(
        "signature I = sig val NONE : int option end; \
        signature O = sig structure X : I end; \
        structure A : O = struct structure X = Option end; \
        open A.X; val result = case SOME 1 of NONE => 0 | _ => 1;",
    );
    assert_eq!(integer(&vm, "result"), 0);
}

#[test]
fn signature_exception_preserves_constructor_identity() {
    let vm = evaluate(
        "signature E = sig exception Boom end; \
        structure S : E = struct exception Boom end; \
        val result = (raise S.Boom) handle S.Boom => 4;",
    );
    assert_eq!(integer(&vm, "result"), 4);
}

#[test]
fn structure_alias_constructor_pattern_rejects_other_constructor() {
    let vm = evaluate(
        "structure O = Option; \
        val result = case SOME 1 of O.NONE => 0 | _ => 1;",
    );
    assert_eq!(integer(&vm, "result"), 1);
}

#[test]
fn unmatched_inner_handler_preserves_outer_exception_identity() {
    let vm = evaluate(
        "val result = ((Option.valOf NONE) handle Subscript => 0) \
        handle Option.Option => 1;",
    );
    assert_eq!(integer(&vm, "result"), 1);
}

#[test]
fn matched_handler_new_exception_propagates_without_original_replacement() {
    let vm = evaluate(
        "val result = ((Option.valOf NONE) \
        handle Option.Option => raise Subscript) handle Subscript => 7;",
    );
    assert_eq!(integer(&vm, "result"), 7);
}

#[test]
fn numeric_record_argument_and_tuple_pattern_are_equivalent() {
    let vm = evaluate(
        "val selected = List.nth {1 = [42], 2 = 0}; \
        val (first, second) = {2 = 5, 1 = 3}; val result = first + second;",
    );
    assert_eq!(integer(&vm, "selected"), 42);
    assert_eq!(integer(&vm, "result"), 8);
}

#[test]
fn numeric_record_pattern_matches_tuple_and_preserves_projection() {
    let vm = evaluate(
        "val {1 = first, 2 = second} = (3, 5); \
        val selected = #2 (7, 11); val result = first + second;",
    );
    assert_eq!(integer(&vm, "selected"), 11);
    assert_eq!(integer(&vm, "result"), 8);
}

struct DropProbe(Rc<Cell<usize>>);
impl Drop for DropProbe {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

struct ProbeHost(Rc<Cell<usize>>);
impl HostBridge for ProbeHost {
    fn invoke(&self, vm: &mut Vm, operation: &str, _: &[Value]) -> Result<Value, HostFailure> {
        vm.insert_host_object(Rc::new(DropProbe(Rc::clone(&self.0)))).map_err(|error| {
            HostFailure::Failed {
                operation: operation.to_owned(),
                resource: "GC drop probe".to_owned(),
                cause: error.to_string(),
            }
        })
    }
}

#[test]
fn cons_tail_cycle_collection_releases_host_value_without_dropping_vm() {
    let dropped = Rc::new(Cell::new(0));
    let mut vm = Vm::new(ProbeHost(Rc::clone(&dropped)));
    vm.register_host_effect(
        "Probe.create",
        TypeScheme::mono(Type::Function(
            Box::new(Type::Constructor("unit".to_owned(), vec![])),
            Box::new(Type::Constructor("probe".to_owned(), vec![])),
        )),
        "probe.create",
    )
    .unwrap();
    vm.evaluate(
        "cons-cycle.sml",
        "val _ = let \
        val probe = Probe.create (); val a = Array.array (1, fn x => x); \
        val _ :: tail = [a, a]; \
        val _ = Array.update (a, 0, fn x => (probe; Array.length (List.hd tail); x)) \
        in () end;",
    )
    .unwrap();
    assert_eq!(dropped.get(), 0);
    vm.collect_garbage().unwrap();
    assert_eq!(dropped.get(), 1);
}

#[test]
fn constructor_value_alias_pattern_binds_instead_of_testing_original_value() {
    let vm = evaluate("val k = NONE; val result = case SOME 1 of k => 7;");
    assert_eq!(integer(&vm, "result"), 7);
}

#[test]
fn lowercase_datatype_constructors_keep_distinct_identities() {
    let vm = evaluate(
        "datatype bit = off | on; \
        val result = case off of on => 1 | off => 0;",
    );
    assert_eq!(integer(&vm, "result"), 0);
}

#[test]
fn uppercase_value_binding_exports_from_structure_as_ordinary_value() {
    let vm = evaluate(
        "structure S = struct val K = NONE end; \
        val result = case SOME 1 of K => 7;",
    );
    assert!(vm.lookup_structure("S").unwrap().unwrap().lookup_value("K").is_some());
    assert_eq!(integer(&vm, "result"), 7);
}

#[test]
fn numeric_record_double_digit_labels_keep_tuple_field_order() {
    let vm = evaluate(
        "val (_, _, _, _, _, _, _, _, _, last) = \
        {1=1, 2=2, 3=3, 4=4, 5=5, 6=6, 7=7, 8=8, 9=9, 10=true}; \
        val result = if last then 10 else 0;",
    );
    assert_eq!(integer(&vm, "result"), 10);
}

#[test]
fn closure_nested_local_uses_elaborated_parameter_type() {
    let vm = evaluate(
        "fun f x = let local val y = x in val z = y end in z end; \
        val result = f 1;",
    );
    assert_eq!(integer(&vm, "result"), 1);
}
