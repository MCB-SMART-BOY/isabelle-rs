//! Machine-word Basis operations required by original Pure bitsets and thread flags.
use super::{MlError, MlErrorKind, NativeFunction, TypeScheme, Value, Vm, function, pair, typ};

pub(super) fn install(vm: &mut Vm) {
    let word = typ("word");
    vm.type_environment.register_alias("Word.word", vec![], word.clone());
    let namespace = vm.structures.entry("Word".to_owned()).or_default();
    namespace.type_environment.register_alias("word", vec![], word.clone());
    namespace.types.insert("word".to_owned(), 0);
    let int = typ("int");
    vm.register_value(
        "Word.wordSize",
        super::TypeScheme::mono(int.clone()),
        Value::int(i64::from(u64::BITS)),
    );
    vm.register_pure(
        "Int.compare",
        &[],
        function(pair(int.clone(), int.clone()), typ("order")),
        1,
        compare_int,
    );
    vm.register_pure("Word.fromInt", &[], function(int.clone(), word.clone()), 1, from_int);
    vm.register_pure("Word.toInt", &[], function(word.clone(), int.clone()), 1, to_int);
    vm.register_pure("Word.toIntX", &[], function(word.clone(), int), 1, to_int_x);
    let binary = function(pair(word.clone(), word.clone()), word.clone());
    for (name, callback) in [
        ("Word.andb", andb as NativeFunction),
        ("Word.orb", orb),
        ("Word.xorb", xorb),
        ("Word.<<", shift_left),
        ("Word.>>", shift_right),
        ("Word.~>>", shift_arithmetic),
    ] {
        vm.register_pure(name, &[], binary.clone(), 1, callback);
    }
    vm.register_pure("Word.notb", &[], function(word.clone(), word), 1, notb);
    install_word32(vm);
}
fn install_word32(vm: &mut Vm) {
    const WORD32_SIZE: u32 = u32::BITS;
    let qualified = "Word32.word";
    vm.type_environment.register_type(qualified, 0, true);
    let namespace = vm.structures.entry("Word32".to_owned()).or_default();
    namespace.type_environment.register_type(qualified, 0, true);
    namespace.type_environment.register_alias("word", vec![], typ(qualified));
    namespace.types.insert("word".to_owned(), 0);
    let word32 = typ(qualified);
    let word = typ("word");
    let int = typ("int");
    vm.register_value(
        "Word32.wordSize",
        TypeScheme::mono(int.clone()),
        Value::int(i64::from(WORD32_SIZE)),
    );
    vm.register_pure(
        "Word32.fromInt",
        &[],
        function(int.clone(), word32.clone()),
        1,
        super::word32::from_int,
    );
    vm.register_pure(
        "Word32.toInt",
        &[],
        function(word32.clone(), int.clone()),
        1,
        super::word32::to_int,
    );
    vm.register_pure(
        "Word32.toIntX",
        &[],
        function(word32.clone(), int),
        1,
        super::word32::to_int_x,
    );
    let binary = function(pair(word32.clone(), word32.clone()), word32.clone());
    for (name, callback) in [
        ("Word32.+", super::word32::add as NativeFunction),
        ("Word32.andb", super::word32::andb as NativeFunction),
        ("Word32.orb", super::word32::orb),
        ("Word32.xorb", super::word32::xorb),
    ] {
        vm.register_pure(name, &[], binary.clone(), 1, callback);
    }
    vm.register_pure(
        "Word32.notb",
        &[],
        function(word32.clone(), word32.clone()),
        1,
        super::word32::notb,
    );
    let shift = function(pair(word32.clone(), word), word32);
    for (name, callback) in [
        ("Word32.<<", super::word32::shift_left as NativeFunction),
        ("Word32.>>", super::word32::shift_right),
        ("Word32.~>>", super::word32::shift_arithmetic),
    ] {
        vm.register_pure(name, &[], shift.clone(), 1, callback);
    }
}

fn compare_int(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [left, right] = super::fields(vm, &args[0], 2, "Int.compare")? else {
        return Err(vm.error(MlErrorKind::Type, "Int.compare", "expected integer pair"));
    };
    let left = left
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "Int.compare", "expected integer"))?;
    let right = right
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "Int.compare", "expected integer"))?;
    let Some(orders) = &vm.basis_order else {
        return Err(vm.error(
            MlErrorKind::HostFailure,
            "Int.compare",
            "Basis order constructors missing",
        ));
    };
    let index = match left.cmp(&right) {
        std::cmp::Ordering::Less => 0,
        std::cmp::Ordering::Equal => 1,
        std::cmp::Ordering::Greater => 2,
    };
    Ok(orders[index].clone())
}

fn require_word(vm: &Vm, value: &Value, operation: &str) -> Result<u64, MlError> {
    value.as_word().ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected word"))
}

fn binary_words(vm: &Vm, args: &[Value], operation: &str) -> Result<(u64, u64), MlError> {
    let Some([left, right]) = args.first().and_then(Value::as_tuple) else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected word pair"));
    };
    Ok((require_word(vm, left, operation)?, require_word(vm, right, operation)?))
}

fn from_int(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(number) = args.first().and_then(Value::as_int) else {
        return Err(vm.error(MlErrorKind::Type, "Word.fromInt", "expected int"));
    };
    Ok(Value::word(number as u64))
}

fn to_int(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(number) = args.first().and_then(Value::as_word) else {
        return Err(vm.error(MlErrorKind::Type, "Word.toInt", "expected word"));
    };
    let number = i64::try_from(number).map_err(|_| {
        vm.raise_basis("Overflow", "Word.toInt", "word outside int range".to_owned())
    })?;
    Ok(Value::int(number))
}

fn to_int_x(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::int(require_word(
        vm,
        args.first()
            .ok_or_else(|| vm.error(MlErrorKind::Type, "Word.toIntX", "missing argument"))?,
        "Word.toIntX",
    )? as i64))
}

fn andb(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = binary_words(vm, args, "Word.andb")?;
    Ok(Value::word(left & right))
}
fn orb(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = binary_words(vm, args, "Word.orb")?;
    Ok(Value::word(left | right))
}
fn xorb(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = binary_words(vm, args, "Word.xorb")?;
    Ok(Value::word(left ^ right))
}
fn notb(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let word = require_word(
        vm,
        args.first().ok_or_else(|| vm.error(MlErrorKind::Type, "Word.notb", "missing argument"))?,
        "Word.notb",
    )?;
    Ok(Value::word(!word))
}
fn shift_left(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (word, amount) = binary_words(vm, args, "Word.<<")?;
    Ok(Value::word(
        u32::try_from(amount).ok().and_then(|amount| word.checked_shl(amount)).unwrap_or(0),
    ))
}
fn shift_right(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (word, amount) = binary_words(vm, args, "Word.>>")?;
    Ok(Value::word(
        u32::try_from(amount).ok().and_then(|amount| word.checked_shr(amount)).unwrap_or(0),
    ))
}
fn shift_arithmetic(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (word, amount) = binary_words(vm, args, "Word.~>>")?;
    let shift = u32::try_from(amount).unwrap_or(u32::MAX).min(u64::BITS - 1);
    Ok(Value::word(((word as i64) >> shift) as u64))
}
