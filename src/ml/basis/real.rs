//! Native IEEE real formatting and conversion used by Pure bootstrap statistics.
use super::{MlError, MlErrorKind, Value, ValueData, Vm, function, typ};
use std::rc::Rc;

const DEFAULT_PRECISION: usize = 6;
const DEFAULT_SIGNIFICANT_DIGITS: usize = 12;
const MAX_FORMAT_PRECISION: usize = 1_024;

pub(super) fn install(vm: &mut Vm) {
    let integer = typ("int");
    let real = typ("real");
    let text = typ("string");
    let format_type = typ("StringCvt.realfmt");
    vm.type_environment.register_type("StringCvt.realfmt", 0, true);
    for name in ["GEN", "SCI", "FIX"] {
        let constructor = Value(Rc::new(ValueData::ConstructorFunction {
            stamp: vm.fresh_identity(),
            name: name.to_owned(),
        }));
        vm.register_value(
            &format!("StringCvt.{name}"),
            super::scheme(
                &[],
                function(super::container("option", integer.clone()), format_type.clone()),
            ),
            constructor,
        );
    }
    let exact_stamp = vm.fresh_identity();
    let exact = Value(Rc::new(ValueData::Constructor {
        stamp: exact_stamp,
        name: "EXACT".to_owned(),
        argument: None,
    }));
    vm.register_value("StringCvt.EXACT", super::TypeScheme::mono(format_type.clone()), exact);
    vm.register_pure(
        "Int.toString",
        &[],
        function(integer.clone(), text.clone()),
        1,
        int_to_string,
    );
    for (name, callback) in [("Int.max", int_max as super::NativeFunction), ("Int.min", int_min)] {
        vm.register_pure(
            name,
            &[],
            function(super::pair(integer.clone(), integer.clone()), integer.clone()),
            1,
            callback,
        );
    }
    vm.register_pure(
        "Real.fromInt",
        &[],
        function(integer.clone(), real.clone()),
        1,
        real_from_int,
    );
    vm.register_pure("real", &[], function(integer.clone(), real.clone()), 1, real_from_int);
    for (name, callback) in [
        ("floor", real_floor as super::NativeFunction),
        ("ceil", real_ceil),
        ("trunc", real_trunc),
        ("round", real_round),
    ] {
        vm.register_pure(name, &[], function(real.clone(), integer.clone()), 1, callback);
        vm.register_pure(
            &format!("Real.{name}"),
            &[],
            function(real.clone(), integer.clone()),
            1,
            callback,
        );
    }
    vm.register_pure(
        "Real.fmt",
        &[],
        function(format_type, function(real.clone(), text.clone())),
        2,
        real_format,
    );
    vm.register_pure("Real.toString", &[], function(real, text), 1, real_to_string);
}

fn expect_int(vm: &Vm, args: &[Value], operation: &str) -> Result<i64, MlError> {
    args.first()
        .and_then(Value::as_int)
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected int"))
}
fn int_to_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let value = expect_int(vm, args, "Int.toString")?;
    Ok(Value::text(value.to_string().replace('-', "~")))
}
fn int_extremum(
    vm: &Vm,
    args: &[Value],
    operation: &str,
    is_maximum: bool,
) -> Result<Value, MlError> {
    let [left, right] = super::fields(vm, &args[0], 2, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected pair"));
    };
    let (Some(left), Some(right)) = (left.as_int(), right.as_int()) else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected int pair"));
    };
    Ok(Value::int(if is_maximum { left.max(right) } else { left.min(right) }))
}
fn int_max(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    int_extremum(vm, args, "Int.max", true)
}
fn int_min(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    int_extremum(vm, args, "Int.min", false)
}
fn real_from_int(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::real(expect_int(vm, args, "Real.fromInt")? as f64))
}
fn real_integer(
    vm: &Vm,
    args: &[Value],
    operation: &str,
    convert: fn(f64) -> f64,
) -> Result<Value, MlError> {
    let real = args
        .first()
        .and_then(Value::as_real)
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected real"))?;
    let value = convert(real);
    if !value.is_finite() || value < i64::MIN as f64 || value >= i64::MAX as f64 {
        return Err(vm.raise_builtin("Overflow"));
    }
    Ok(Value::int(value as i64))
}
fn real_floor(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    real_integer(vm, args, "Real.floor", f64::floor)
}
fn real_ceil(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    real_integer(vm, args, "Real.ceil", f64::ceil)
}
fn real_trunc(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    real_integer(vm, args, "Real.trunc", f64::trunc)
}
fn real_round(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    real_integer(vm, args, "Real.round", f64::round_ties_even)
}

fn format_spec<'a>(vm: &Vm, value: &'a Value) -> Result<(&'a str, usize), MlError> {
    let ValueData::Constructor { name, argument, .. } = &*value.0 else {
        return Err(vm.error(MlErrorKind::Type, "Real.fmt", "expected StringCvt.realfmt"));
    };
    if name == "EXACT" && argument.is_none() {
        return Ok(("EXACT", 0));
    }
    if !matches!(name.as_str(), "GEN" | "SCI" | "FIX") {
        return Err(vm.error(MlErrorKind::Type, "Real.fmt", "unknown real format"));
    }
    let precision = match argument.as_ref().map(|argument| &*argument.0) {
        Some(ValueData::Constructor { name: optional, argument: None, .. })
            if optional == "NONE" =>
        {
            if name == "GEN" {
                DEFAULT_SIGNIFICANT_DIGITS
            } else {
                DEFAULT_PRECISION
            }
        },
        Some(ValueData::Constructor { name: optional, argument: Some(number), .. })
            if optional == "SOME" =>
        {
            let number = number
                .as_int()
                .ok_or_else(|| vm.error(MlErrorKind::Type, "Real.fmt", "expected int precision"))?;
            usize::try_from(number).map_err(|_| vm.raise_builtin("Size"))?
        },
        _ => {
            return Err(vm.error(
                MlErrorKind::Type,
                "Real.fmt",
                "expected real format precision option",
            ));
        },
    };
    if precision > MAX_FORMAT_PRECISION || name == "GEN" && precision == 0 {
        return Err(vm.raise_builtin("Size"));
    }
    Ok((name.as_str(), precision))
}
fn exact_decimal(value: f64) -> String {
    if value == 0.0 {
        return if value.is_sign_negative() { "~0.0" } else { "0.0" }.to_owned();
    }
    let bits = value.abs().to_bits();
    let raw_exponent = ((bits >> 52) & 0x7ff) as i32;
    let mantissa = (bits & ((1u64 << 52) - 1)) | if raw_exponent == 0 { 0 } else { 1u64 << 52 };
    let exponent = if raw_exponent == 0 { -1074 } else { raw_exponent - 1023 - 52 };
    let mut digits =
        mantissa.to_string().bytes().rev().map(|digit| digit - b'0').collect::<Vec<_>>();
    for _ in 0..exponent.unsigned_abs() {
        let multiplier = if exponent < 0 { 5 } else { 2 };
        let mut carry = 0u16;
        for digit in &mut digits {
            let number = u16::from(*digit) * multiplier + carry;
            *digit = (number % 10) as u8;
            carry = number / 10;
        }
        while carry > 0 {
            digits.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    let mut decimal = digits.iter().rev().map(|digit| char::from(b'0' + digit)).collect::<String>();
    if exponent < 0 {
        let places = exponent.unsigned_abs() as usize;
        if decimal.len() <= places {
            decimal.insert_str(0, &"0".repeat(places + 1 - decimal.len()));
        }
        decimal.insert(decimal.len() - places, '.');
        while decimal.ends_with('0') {
            decimal.pop();
        }
        if decimal.ends_with('.') {
            decimal.push('0');
        }
    }
    if value.is_sign_negative() {
        decimal.insert(0, '~');
    }
    decimal
}

fn format_real(value: f64, format: &str, precision: usize) -> String {
    if value.is_nan() {
        return "nan".to_owned();
    }
    if value.is_infinite() {
        return if value.is_sign_negative() { "~inf" } else { "inf" }.to_owned();
    }
    let formatted = match format {
        "SCI" => format!("{value:.precision$E}"),
        "FIX" => format!("{value:.precision$}"),
        "EXACT" => return exact_decimal(value),
        _ => {
            let exponent = if value == 0.0 { 0 } else { value.abs().log10().floor() as i32 };
            if exponent < -4 || exponent >= precision as i32 {
                format!("{value:.decimals$E}", decimals = precision.saturating_sub(1))
            } else {
                let decimals = (precision as i32 - exponent - 1).max(0) as usize;
                format!("{value:.decimals$}")
            }
        },
    };
    if format != "GEN" {
        return formatted.replace('-', "~");
    }
    let mut result = formatted;
    if let Some(exponent) = result.find('E') {
        if let Some(point) = result[..exponent].find('.') {
            let mut fraction_end = exponent;
            while fraction_end > point + 2 && result.as_bytes()[fraction_end - 1] == b'0' {
                fraction_end -= 1;
            }
            result.drain(fraction_end..exponent);
        }
    } else if let Some(point) = result.find('.') {
        while result.len() > point + 2 && result.ends_with('0') {
            result.pop();
        }
    }
    result.replace('-', "~")
}
fn real_format(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [format, value] = args else {
        return Err(vm.error(MlErrorKind::Type, "Real.fmt", "expected format and real"));
    };
    let (name, precision) = format_spec(vm, format)?;
    let real =
        value.as_real().ok_or_else(|| vm.error(MlErrorKind::Type, "Real.fmt", "expected real"))?;
    Ok(Value::text(format_real(real, name, precision)))
}
fn real_to_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let real = args
        .first()
        .and_then(Value::as_real)
        .ok_or_else(|| vm.error(MlErrorKind::Type, "Real.toString", "expected real"))?;
    Ok(Value::text(format_real(real, "GEN", DEFAULT_SIGNIFICANT_DIGITS)))
}
