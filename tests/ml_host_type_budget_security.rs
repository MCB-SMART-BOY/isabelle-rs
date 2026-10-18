use isabelle_rs::ml::{DenyHost, MlError, MlErrorKind, Type, TypeScheme, Value, Vm};
use std::collections::BTreeMap;

#[test]
fn public_apply_shared_dag_over_visit_budget_rejects_before_effect() {
    const DEPTH: usize = 32;
    const WIDTH: usize = 512;
    let mut vm = Vm::new(DenyHost);
    let input_type = format!("int{}", " list".repeat(DEPTH));
    vm.evaluate(
        "host-dag-budget.sml",
        &format!("val hits = ref 0; fun consume (_: {input_type}) = (hits := !hits + 1; 7);"),
    )
    .expect("well-typed consumer");
    let consume = vm.lookup_value("consume").unwrap().unwrap().clone();
    let mut input = Value::int(1);
    for _ in 0..DEPTH {
        input = Value::list(vec![input; WIDTH]);
    }

    let error = vm.apply(&consume, &[input]).expect_err("shared edges must consume the budget");
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("host-dag-budget-effect.sml", "val unchanged = !hits = 0;").unwrap();
    assert_eq!(vm.lookup_value("unchanged").unwrap().and_then(Value::as_bool), Some(true));
}

#[test]
fn public_apply_shared_value_under_distinct_types_rejects_before_effect() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "host-dag-distinct-types.sml",
        "val hits = ref 0; fun consume (_: int list * string list) = (hits := !hits + 1; 7);",
    )
    .expect("well-typed consumer");
    let consume = vm.lookup_value("consume").unwrap().unwrap().clone();
    let shared = Value::list(vec![Value::int(1)]);
    let input = Value::tuple(vec![shared.clone(), shared]);

    let error = vm.apply(&consume, &[input]).expect_err("distinct types must each be checked");
    assert_eq!(error.kind, MlErrorKind::Type);
    vm.evaluate("host-dag-distinct-types-effect.sml", "val unchanged = !hits = 0;").unwrap();
    assert_eq!(vm.lookup_value("unchanged").unwrap().and_then(Value::as_bool), Some(true));
}

fn return_seven(_vm: &mut Vm, _args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::int(7))
}

#[test]
fn public_apply_oversized_phantom_type_rejects_before_callback() {
    const FIELD_COUNT: usize = 128;
    const LIST_DEPTH: usize = 130;
    let mut fields = BTreeMap::new();
    for index in 0..FIELD_COUNT {
        let mut field = Type::Constructor("int".to_owned(), vec![]);
        for _ in 0..LIST_DEPTH {
            field = Type::Constructor("list".to_owned(), vec![field]);
        }
        fields.insert(format!("field{index}"), field);
    }
    let input = Type::Constructor("list".to_owned(), vec![Type::Record(fields, false)]);
    let signature = TypeScheme::mono(Type::Function(
        Box::new(input),
        Box::new(Type::Constructor("int".to_owned(), vec![])),
    ));
    let mut vm = Vm::new(DenyHost);
    vm.register_native("consume", signature, return_seven).unwrap();
    let consume = vm.lookup_value("consume").unwrap().unwrap().clone();

    let error = vm
        .apply(&consume, &[Value::list(vec![])])
        .expect_err("unchecked phantom type expansion must exhaust the budget");
    assert_eq!(error.kind, MlErrorKind::Type);
}
