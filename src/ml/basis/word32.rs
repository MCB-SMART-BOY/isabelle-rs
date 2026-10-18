//! Distinct fixed-width Word32 operations; literals are specialized by static elaboration.
use super::{MlError, MlErrorKind, Value, Vm};

fn value(vm: &Vm, argument: &Value, operation: &str) -> Result<u32, MlError> {
    argument
        .as_word32()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected Word32.word"))
}

fn pair(vm: &Vm, args: &[Value], operation: &str) -> Result<(u32, u32), MlError> {
    let Some([left, right]) = args.first().and_then(Value::as_tuple) else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected Word32.word pair"));
    };
    Ok((value(vm, left, operation)?, value(vm, right, operation)?))
}

fn shift_args(vm: &Vm, args: &[Value], operation: &str) -> Result<(u32, u32), MlError> {
    let Some([word, amount]) = args.first().and_then(Value::as_tuple) else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected Word32.word * word"));
    };
    let amount = amount
        .as_word()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected word shift"))?;
    Ok((value(vm, word, operation)?, u32::try_from(amount).unwrap_or(u32::MAX)))
}

pub(super) fn from_int(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let number = args
        .first()
        .and_then(Value::as_int)
        .ok_or_else(|| vm.error(MlErrorKind::Type, "Word32.fromInt", "expected int"))?;
    Ok(Value::word32(number as u32))
}

pub(super) fn to_int(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let argument =
        args.first().ok_or_else(|| vm.error(MlErrorKind::Type, "Word32.toInt", "missing word"))?;
    Ok(Value::int(i64::from(value(vm, argument, "Word32.toInt")?)))
}

pub(super) fn to_int_x(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let argument =
        args.first().ok_or_else(|| vm.error(MlErrorKind::Type, "Word32.toIntX", "missing word"))?;
    Ok(Value::int(i64::from(value(vm, argument, "Word32.toIntX")? as i32)))
}

pub(super) fn add(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = pair(vm, args, "Word32.+")?;
    Ok(Value::word32(left.wrapping_add(right)))
}

pub(super) fn andb(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = pair(vm, args, "Word32.andb")?;
    Ok(Value::word32(left & right))
}
pub(super) fn orb(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = pair(vm, args, "Word32.orb")?;
    Ok(Value::word32(left | right))
}
pub(super) fn xorb(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = pair(vm, args, "Word32.xorb")?;
    Ok(Value::word32(left ^ right))
}
pub(super) fn notb(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let argument =
        args.first().ok_or_else(|| vm.error(MlErrorKind::Type, "Word32.notb", "missing word"))?;
    Ok(Value::word32(!value(vm, argument, "Word32.notb")?))
}

pub(super) fn shift_left(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (word, amount) = shift_args(vm, args, "Word32.<<")?;
    Ok(Value::word32(word.checked_shl(amount).unwrap_or(0)))
}
pub(super) fn shift_right(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (word, amount) = shift_args(vm, args, "Word32.>>")?;
    Ok(Value::word32(word.checked_shr(amount).unwrap_or(0)))
}
pub(super) fn shift_arithmetic(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (word, amount) = shift_args(vm, args, "Word32.~>>")?;
    Ok(Value::word32(((word as i32) >> amount.min(u32::BITS - 1)) as u32))
}
