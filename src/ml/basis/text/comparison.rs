use super::*;
use std::cmp::Ordering;

pub(super) fn install(vm: &mut Vm) {
    let string_callbacks =
        [string_less as NativeFunction, string_less_equal, string_greater, string_greater_equal];
    let char_callbacks =
        [char_less as NativeFunction, char_less_equal, char_greater, char_greater_equal];
    for (namespace, input, callbacks) in
        [("String", typ("string"), string_callbacks), ("Char", typ("char"), char_callbacks)]
    {
        for (operator, callback) in ["<", "<=", ">", ">="].into_iter().zip(callbacks) {
            vm.register_pure(
                &format!("{namespace}.{operator}"),
                &[],
                function(pair(input.clone(), input.clone()), typ("bool")),
                1,
                callback,
            );
        }
    }
}

pub(super) fn compare_strings(
    vm: &Vm,
    args: &[Value],
    operation: &str,
) -> Result<Ordering, MlError> {
    let pair = fields(vm, arg(vm, args, 0, operation)?, 2, operation)?;
    Ok(bytes(vm, &pair[0], operation)?.cmp(bytes(vm, &pair[1], operation)?))
}

pub(super) fn compare_characters(
    vm: &Vm,
    args: &[Value],
    operation: &str,
) -> Result<Ordering, MlError> {
    let pair = fields(vm, arg(vm, args, 0, operation)?, 2, operation)?;
    Ok(character(vm, &pair[0], operation)?.cmp(&character(vm, &pair[1], operation)?))
}

fn string_less(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_strings(vm, args, "String.<")?.is_lt()))
}
fn string_less_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_strings(vm, args, "String.<=")?.is_le()))
}
fn string_greater(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_strings(vm, args, "String.>")?.is_gt()))
}
fn string_greater_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_strings(vm, args, "String.>=")?.is_ge()))
}
fn char_less(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_characters(vm, args, "Char.<")?.is_lt()))
}
fn char_less_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_characters(vm, args, "Char.<=")?.is_le()))
}
fn char_greater(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_characters(vm, args, "Char.>")?.is_gt()))
}
fn char_greater_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_characters(vm, args, "Char.>=")?.is_ge()))
}
