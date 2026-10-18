//! Isabelle2025 Poly/ML's non-slice polymorphic VECTOR and ARRAY operations.
use super::{MlError, MlErrorKind, NativeFunction, Type, Value, ValueData, Vm};
use super::{arg, container, fields, function, index, pair, scheme, size, triple, typ, var};
use std::cell::RefCell;
use std::rc::Rc;
// Exclusive bound for element storage in a Rust Vec<Value>.
const MAX_LEN: usize = isize::MAX as usize / std::mem::size_of::<Value>();

fn record(fields: &[(&str, Type)]) -> Type {
    Type::Record(
        fields.iter().map(|(name, typ)| ((*name).to_owned(), typ.clone())).collect(),
        false,
    )
}

pub(super) fn install(vm: &mut Vm) {
    for (name, is_array) in [("Vector", false), ("Array", true)] {
        install_sequence(vm, name, is_array);
        install_iteration(vm, name, is_array);
    }
    install_vector(vm);
    install_array(vm);
}

fn install_sequence(vm: &mut Vm, name: &str, is_array: bool) {
    let item = var(1);
    vm.register_value(
        &format!("{name}.maxLen"),
        scheme(&[], typ("int")),
        Value::int(MAX_LEN as i64),
    );
    let seq = container(&name.to_lowercase(), item.clone());
    let functions: [(&str, NativeFunction, Type); 4] = if is_array {
        [
            ("fromList", array_from_list, function(container("list", item.clone()), seq.clone())),
            (
                "tabulate",
                array_tabulate,
                function(pair(typ("int"), function(typ("int"), item.clone())), seq.clone()),
            ),
            ("length", array_length, function(seq.clone(), typ("int"))),
            ("sub", array_sub, function(pair(seq.clone(), typ("int")), item.clone())),
        ]
    } else {
        [
            ("fromList", vector_from_list, function(container("list", item.clone()), seq.clone())),
            (
                "tabulate",
                vector_tabulate,
                function(pair(typ("int"), function(typ("int"), item.clone())), seq.clone()),
            ),
            ("length", vector_length, function(seq.clone(), typ("int"))),
            ("sub", vector_sub, function(pair(seq.clone(), typ("int")), item.clone())),
        ]
    };
    for (suffix, callback, signature) in functions {
        vm.register_pure(&format!("{name}.{suffix}"), &[1], signature, 1, callback);
    }
}

fn install_iteration(vm: &mut Vm, name: &str, is_array: bool) {
    let item = var(1);
    let seq = container(&name.to_lowercase(), item.clone());
    let callback = |is_indexed: bool, output: Type| {
        let input = if is_indexed { pair(typ("int"), item.clone()) } else { item.clone() };
        function(function(input, output.clone()), function(seq.clone(), output))
    };
    for (suffix, is_indexed) in [("app", false), ("appi", true)] {
        vm.register_pure(
            &format!("{name}.{suffix}"),
            &[1],
            callback(is_indexed, typ("unit")),
            2,
            select(is_array, suffix, vector_app),
        );
    }
    for (suffix, is_indexed, reverse) in [
        ("foldl", false, false),
        ("foldr", false, true),
        ("foldli", true, false),
        ("foldri", true, true),
    ] {
        let input = if is_indexed {
            triple(typ("int"), item.clone(), var(2))
        } else {
            pair(item.clone(), var(2))
        };
        let signature =
            function(function(input, var(2)), function(var(2), function(seq.clone(), var(2))));
        let fallback = if reverse { vector_foldr } else { vector_foldl };
        vm.register_pure(
            &format!("{name}.{suffix}"),
            &[1, 2],
            signature,
            3,
            select(is_array, suffix, fallback),
        );
    }
    for (suffix, is_indexed) in
        [("find", false), ("findi", true), ("exists", false), ("all", false)]
    {
        let input = if is_indexed { pair(typ("int"), item.clone()) } else { item.clone() };
        let output = if suffix.starts_with("find") {
            container("option", input.clone())
        } else {
            typ("bool")
        };
        vm.register_pure(
            &format!("{name}.{suffix}"),
            &[1],
            function(function(input, typ("bool")), function(seq.clone(), output)),
            2,
            select(is_array, suffix, vector_find),
        );
    }
    let compare = function(pair(item.clone(), item), typ("order"));
    vm.register_pure(
        &format!("{name}.collate"),
        &[1],
        function(compare, function(pair(seq.clone(), seq), typ("order"))),
        2,
        if is_array { array_collate } else { vector_collate },
    );
}

fn select(is_array: bool, name: &str, default: NativeFunction) -> NativeFunction {
    match (is_array, name) {
        (true, "app") => array_app,
        (true, "appi") => array_appi,
        (false, "appi") => vector_appi,
        (true, "foldl") => array_foldl,
        (true, "foldr") => array_foldr,
        (true, "foldli") => array_foldli,
        (true, "foldri") => array_foldri,
        (false, "foldli") => vector_foldli,
        (false, "foldri") => vector_foldri,
        (true, "find") => array_find,
        (true, "findi") => array_findi,
        (true, "exists") => array_exists,
        (true, "all") => array_all,
        (false, "findi") => vector_findi,
        (false, "exists") => vector_exists,
        (false, "all") => vector_all,
        _ => default,
    }
}

fn install_vector(vm: &mut Vm) {
    let item = var(1);
    let vector = container("vector", item.clone());
    vm.register_pure(
        "Vector.concat",
        &[1],
        function(container("list", vector.clone()), vector.clone()),
        1,
        vector_concat,
    );
    vm.register_pure(
        "Vector.update",
        &[1],
        function(triple(vector.clone(), typ("int"), item.clone()), vector.clone()),
        1,
        vector_update,
    );
    for (name, callback, is_indexed) in
        [("map", vector_map as NativeFunction, false), ("mapi", vector_mapi, true)]
    {
        let input = if is_indexed { pair(typ("int"), item.clone()) } else { item.clone() };
        vm.register_pure(
            &format!("Vector.{name}"),
            &[1, 2],
            function(
                function(input, var(2)),
                function(vector.clone(), container("vector", var(2))),
            ),
            2,
            callback,
        );
    }
}

fn install_array(vm: &mut Vm) {
    let item = var(1);
    let array = container("array", item.clone());
    let vector = container("vector", item.clone());
    vm.register_pure(
        "Array.array",
        &[1],
        function(pair(typ("int"), item.clone()), array.clone()),
        1,
        array_make,
    );
    vm.register_pure(
        "Array.vector",
        &[1],
        function(array.clone(), vector.clone()),
        1,
        array_vector,
    );
    vm.register_pure(
        "Array.update",
        &[1],
        function(triple(array.clone(), typ("int"), item.clone()), typ("unit")),
        1,
        array_update,
    );
    vm.register_pure(
        "Array.nth",
        &[1],
        function(array.clone(), function(typ("int"), item.clone())),
        2,
        array_nth,
    );
    vm.register_pure(
        "Array.upd",
        &[1],
        function(array.clone(), function(typ("int"), function(item.clone(), typ("unit")))),
        3,
        array_upd,
    );
    let destination =
        |source| record(&[("src", source), ("dst", array.clone()), ("di", typ("int"))]);
    vm.register_pure(
        "Array.copy",
        &[1],
        function(destination(array.clone()), typ("unit")),
        1,
        array_copy,
    );
    vm.register_pure(
        "Array.copyVec",
        &[1],
        function(destination(vector), typ("unit")),
        1,
        array_copy_vec,
    );
    for (name, callback, indexed) in
        [("modify", array_modify as NativeFunction, false), ("modifyi", array_modifyi, true)]
    {
        let input = if indexed { pair(typ("int"), item.clone()) } else { item.clone() };
        vm.register_pure(
            &format!("Array.{name}"),
            &[1],
            function(function(input, item.clone()), function(array.clone(), typ("unit"))),
            2,
            callback,
        );
    }
}

fn sequence_length(
    vm: &Vm,
    value: &Value,
    is_array: bool,
    operation: &str,
) -> Result<usize, MlError> {
    match (&*value.0, is_array) {
        (ValueData::Vector(values), false) => Ok(values.len()),
        (ValueData::Array(values), true) => Ok(values.borrow().len()),
        _ => Err(vm.error(MlErrorKind::Type, operation, "wrong container kind")),
    }
}
fn sequence_item(
    vm: &Vm,
    value: &Value,
    position: usize,
    operation: &str,
) -> Result<Value, MlError> {
    let item = match &*value.0 {
        ValueData::Vector(values) => values.get(position).cloned(),
        ValueData::Array(values) => values.borrow().get(position).cloned(),
        _ => return Err(vm.error(MlErrorKind::Type, operation, "wrong container kind")),
    };
    item.ok_or_else(|| {
        vm.raise_basis("Subscript", operation, format!("index {position} changed during traversal"))
    })
}
fn reserve(vm: &Vm, values: &mut Vec<Value>, count: usize, operation: &str) -> Result<(), MlError> {
    if count >= MAX_LEN {
        return Err(vm.raise_basis("Size", operation, format!("size {count}, maximum {MAX_LEN}")));
    }
    values
        .try_reserve_exact(count)
        .map_err(|cause| vm.raise_basis("Size", operation, format!("size {count}: {cause}")))
}
fn make_sequence(vm: &mut Vm, values: Vec<Value>, is_array: bool) -> Value {
    let data =
        if is_array { ValueData::Array(RefCell::new(values)) } else { ValueData::Vector(values) };
    vm.track_value(Value(Rc::new(data)))
}
fn from_list(
    vm: &mut Vm,
    args: &[Value],
    is_array: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let ValueData::List(values) = &*arg(vm, args, 0, operation)?.0 else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected list"));
    };
    let mut result = Vec::new();
    reserve(vm, &mut result, values.len(), operation)?;
    result.extend_from_slice(values);
    Ok(make_sequence(vm, result, is_array))
}
fn vector_from_list(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    from_list(vm, args, false, "Vector.fromList")
}
fn array_from_list(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    from_list(vm, args, true, "Array.fromList")
}
fn tabulate(
    vm: &mut Vm,
    args: &[Value],
    is_array: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let [count, callback] = fields(vm, arg(vm, args, 0, operation)?, 2, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected pair"));
    };
    let count = size(vm, count, operation)?;
    let mut values = Vec::new();
    reserve(vm, &mut values, count, operation)?;
    for i in 0..count {
        vm.check_stop()?;
        let callback_type = vm.native_argument_field_type(0, "2");
        values.push(super::text::apply_typed_callback(
            vm,
            callback,
            &[Value::int(i as i64)],
            callback_type,
        )?);
    }
    Ok(make_sequence(vm, values, is_array))
}
fn vector_tabulate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    tabulate(vm, args, false, "Vector.tabulate")
}
fn array_tabulate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    tabulate(vm, args, true, "Array.tabulate")
}
fn length(vm: &mut Vm, args: &[Value], is_array: bool, operation: &str) -> Result<Value, MlError> {
    Ok(Value::int(sequence_length(vm, arg(vm, args, 0, operation)?, is_array, operation)? as i64))
}
fn vector_length(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    length(vm, args, false, "Vector.length")
}
fn array_length(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    length(vm, args, true, "Array.length")
}
fn sub(vm: &mut Vm, args: &[Value], is_array: bool, operation: &str) -> Result<Value, MlError> {
    let [sequence, position] = fields(vm, arg(vm, args, 0, operation)?, 2, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected pair"));
    };
    let length = sequence_length(vm, sequence, is_array, operation)?;
    sequence_item(vm, sequence, index(vm, position, length, operation)?, operation)
}
fn vector_sub(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sub(vm, args, false, "Vector.sub")
}
fn array_sub(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sub(vm, args, true, "Array.sub")
}
fn array_nth(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let array = arg(vm, args, 0, "Array.nth")?;
    let length = sequence_length(vm, array, true, "Array.nth")?;
    sequence_item(
        vm,
        array,
        index(vm, arg(vm, args, 1, "Array.nth")?, length, "Array.nth")?,
        "Array.nth",
    )
}

fn array_make(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [count, value] = fields(vm, arg(vm, args, 0, "Array.array")?, 2, "Array.array")? else {
        return Err(vm.error(MlErrorKind::Type, "Array.array", "expected pair"));
    };
    let count = size(vm, count, "Array.array")?;
    let mut values = Vec::new();
    reserve(vm, &mut values, count, "Array.array")?;
    for _ in 0..count {
        vm.check_stop()?;
        values.push(value.clone());
    }
    Ok(make_sequence(vm, values, true))
}
fn array_update(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [array, position, value] =
        fields(vm, arg(vm, args, 0, "Array.update")?, 3, "Array.update")?
    else {
        return Err(vm.error(MlErrorKind::Type, "Array.update", "expected triple"));
    };
    let ValueData::Array(items) = &*array.0 else {
        return Err(vm.error(MlErrorKind::Type, "Array.update", "expected array"));
    };
    let position = index(vm, position, items.borrow().len(), "Array.update")?;
    items.borrow_mut()[position] = value.clone();
    Ok(Value::unit())
}
fn array_upd(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let ValueData::Array(items) = &*arg(vm, args, 0, "Array.upd")?.0 else {
        return Err(vm.error(MlErrorKind::Type, "Array.upd", "expected array"));
    };
    let position = index(vm, arg(vm, args, 1, "Array.upd")?, items.borrow().len(), "Array.upd")?;
    items.borrow_mut()[position] = arg(vm, args, 2, "Array.upd")?.clone();
    Ok(Value::unit())
}

fn vector_concat(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let ValueData::List(vectors) = &*arg(vm, args, 0, "Vector.concat")?.0 else {
        return Err(vm.error(MlErrorKind::Type, "Vector.concat", "expected list of vectors"));
    };
    if let [only] = vectors.as_slice() {
        sequence_length(vm, only, false, "Vector.concat")?;
        return Ok(only.clone());
    }
    let mut total = 0usize;
    for vector in vectors {
        vm.check_stop()?;
        total = total
            .checked_add(sequence_length(vm, vector, false, "Vector.concat")?)
            .filter(|length| *length < MAX_LEN)
            .ok_or_else(|| {
                vm.raise_basis("Size", "Vector.concat", "combined length overflow".to_owned())
            })?;
    }
    let mut result = Vec::new();
    reserve(vm, &mut result, total, "Vector.concat")?;
    for vector in vectors {
        vm.check_stop()?;
        let ValueData::Vector(values) = &*vector.0 else {
            return Err(vm.error(MlErrorKind::Type, "Vector.concat", "expected vector"));
        };
        result.extend_from_slice(values);
    }
    Ok(make_sequence(vm, result, false))
}
fn vector_update(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [vector, position, replacement] =
        fields(vm, arg(vm, args, 0, "Vector.update")?, 3, "Vector.update")?
    else {
        return Err(vm.error(MlErrorKind::Type, "Vector.update", "expected triple"));
    };
    let ValueData::Vector(values) = &*vector.0 else {
        return Err(vm.error(MlErrorKind::Type, "Vector.update", "expected vector"));
    };
    let position = index(vm, position, values.len(), "Vector.update")?;
    let mut result = Vec::new();
    reserve(vm, &mut result, values.len(), "Vector.update")?;
    result.extend_from_slice(values);
    result[position] = replacement.clone();
    Ok(make_sequence(vm, result, false))
}
fn array_vector(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let array = arg(vm, args, 0, "Array.vector")?;
    let ValueData::Array(values) = &*array.0 else {
        return Err(vm.error(MlErrorKind::Type, "Array.vector", "expected array"));
    };
    let values = values.borrow();
    let mut result = Vec::new();
    reserve(vm, &mut result, values.len(), "Array.vector")?;
    result.extend_from_slice(&values);
    Ok(make_sequence(vm, result, false))
}
fn destination<'a>(
    vm: &Vm,
    args: &'a [Value],
    operation: &str,
) -> Result<(&'a Value, &'a RefCell<Vec<Value>>, usize), MlError> {
    let record = arg(vm, args, 0, operation)?;
    if record.record_length() != Some(3) {
        return Err(vm.error(MlErrorKind::Type, operation, "expected {src, dst, di} record"));
    }
    let src = record
        .record_field("src")
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "missing src"))?;
    let dst = record
        .record_field("dst")
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "missing dst"))?;
    let di = record
        .record_field("di")
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "missing di"))?;
    let ValueData::Array(dst) = &*dst.0 else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected dst array"));
    };
    let di =
        di.as_int().ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected integer di"))?;
    let di = usize::try_from(di)
        .map_err(|_| vm.raise_basis("Subscript", operation, format!("destination index {di}")))?;
    Ok((src, dst, di))
}
fn check_copy_bounds(
    vm: &Vm,
    di: usize,
    source: usize,
    target: usize,
    operation: &str,
) -> Result<(), MlError> {
    if di > target || source > target - di {
        return Err(vm.raise_basis(
            "Subscript",
            operation,
            format!("destination index {di}, source length {source}, destination length {target}"),
        ));
    }
    Ok(())
}
fn array_copy(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (src, dst, di) = destination(vm, args, "Array.copy")?;
    let ValueData::Array(src) = &*src.0 else {
        return Err(vm.error(MlErrorKind::Type, "Array.copy", "expected src array"));
    };
    let source_length = src.borrow().len();
    check_copy_bounds(vm, di, source_length, dst.borrow().len(), "Array.copy")?;
    if std::ptr::eq(src, dst) && di == 0 {
        return Ok(Value::unit());
    }
    dst.borrow_mut()[di..di + source_length].clone_from_slice(&src.borrow());
    Ok(Value::unit())
}
fn array_copy_vec(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (src, dst, di) = destination(vm, args, "Array.copyVec")?;
    let ValueData::Vector(values) = &*src.0 else {
        return Err(vm.error(MlErrorKind::Type, "Array.copyVec", "expected src vector"));
    };
    check_copy_bounds(vm, di, values.len(), dst.borrow().len(), "Array.copyVec")?;
    dst.borrow_mut()[di..di + values.len()].clone_from_slice(values);
    Ok(Value::unit())
}

fn callback_item(
    vm: &mut Vm,
    callback: &Value,
    item: Value,
    position: usize,
    indexed: bool,
) -> Result<Value, MlError> {
    let argument = if indexed {
        vm.track_value(Value(Rc::new(ValueData::Tuple(vec![Value::int(position as i64), item]))))
    } else {
        item
    };
    super::text::apply_callback(vm, callback, &[argument])
}
fn walk(
    vm: &mut Vm,
    args: &[Value],
    is_array: bool,
    indexed: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let sequence = arg(vm, args, 1, operation)?;
    let length = sequence_length(vm, sequence, is_array, operation)?;
    for position in 0..length {
        vm.check_stop()?;
        callback_item(
            vm,
            &args[0],
            sequence_item(vm, sequence, position, operation)?,
            position,
            indexed,
        )?;
    }
    Ok(Value::unit())
}
fn vector_app(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    walk(vm, args, false, false, "Vector.app")
}
fn vector_appi(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    walk(vm, args, false, true, "Vector.appi")
}
fn array_app(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    walk(vm, args, true, false, "Array.app")
}
fn array_appi(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    walk(vm, args, true, true, "Array.appi")
}
fn sequence_fold(
    vm: &mut Vm,
    args: &[Value],
    is_array: bool,
    reverse: bool,
    indexed: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let sequence = arg(vm, args, 2, operation)?;
    let length = sequence_length(vm, sequence, is_array, operation)?;
    let mut accumulator = args[1].clone();
    for offset in 0..length {
        vm.check_stop()?;
        let position = if reverse { length - offset - 1 } else { offset };
        let item = sequence_item(vm, sequence, position, operation)?;
        let tuple = if indexed {
            vm.track_value(Value(Rc::new(ValueData::Tuple(vec![
                Value::int(position as i64),
                item,
                accumulator,
            ]))))
        } else {
            vm.track_value(Value(Rc::new(ValueData::Tuple(vec![item, accumulator]))))
        };
        accumulator = super::text::apply_callback(vm, &args[0], &[tuple])?;
    }
    Ok(accumulator)
}
fn vector_foldl(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sequence_fold(vm, args, false, false, false, "Vector.foldl")
}
fn vector_foldr(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sequence_fold(vm, args, false, true, false, "Vector.foldr")
}
fn vector_foldli(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sequence_fold(vm, args, false, false, true, "Vector.foldli")
}
fn vector_foldri(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sequence_fold(vm, args, false, true, true, "Vector.foldri")
}
fn array_foldl(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sequence_fold(vm, args, true, false, false, "Array.foldl")
}
fn array_foldr(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sequence_fold(vm, args, true, true, false, "Array.foldr")
}
fn array_foldli(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sequence_fold(vm, args, true, false, true, "Array.foldli")
}
fn array_foldri(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    sequence_fold(vm, args, true, true, true, "Array.foldri")
}
fn map(vm: &mut Vm, args: &[Value], indexed: bool, operation: &str) -> Result<Value, MlError> {
    let vector = arg(vm, args, 1, operation)?;
    let length = sequence_length(vm, vector, false, operation)?;
    let mut output = Vec::new();
    reserve(vm, &mut output, length, operation)?;
    for position in 0..length {
        vm.check_stop()?;
        let item = sequence_item(vm, vector, position, operation)?;
        output.push(callback_item(vm, &args[0], item, position, indexed)?);
    }
    Ok(make_sequence(vm, output, false))
}
fn vector_map(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    map(vm, args, false, "Vector.map")
}
fn vector_mapi(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    map(vm, args, true, "Vector.mapi")
}
fn modify(vm: &mut Vm, args: &[Value], indexed: bool, operation: &str) -> Result<Value, MlError> {
    let array = arg(vm, args, 1, operation)?;
    let ValueData::Array(values) = &*array.0 else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected array"));
    };
    let length = values.borrow().len();
    for position in 0..length {
        vm.check_stop()?;
        let original = sequence_item(vm, array, position, operation)?;
        let result = callback_item(vm, &args[0], original, position, indexed)?;
        values.borrow_mut()[position] = result;
    }
    Ok(Value::unit())
}
fn array_modify(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    modify(vm, args, false, "Array.modify")
}
fn array_modifyi(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    modify(vm, args, true, "Array.modifyi")
}
fn option(vm: &mut Vm, result: Option<Value>) -> Value {
    match result {
        Some(argument) => vm.track_value(Value(Rc::new(ValueData::Constructor {
            stamp: vm.option_some_stamp,
            name: "SOME".to_owned(),
            argument: Some(argument),
        }))),
        None => vm.track_value(Value(Rc::new(ValueData::Constructor {
            stamp: vm.option_none_stamp,
            name: "NONE".to_owned(),
            argument: None,
        }))),
    }
}
fn find(
    vm: &mut Vm,
    args: &[Value],
    is_array: bool,
    indexed: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let sequence = arg(vm, args, 1, operation)?;
    let length = sequence_length(vm, sequence, is_array, operation)?;
    for position in 0..length {
        vm.check_stop()?;
        let item = sequence_item(vm, sequence, position, operation)?;
        let answer =
            callback_item(vm, &args[0], item.clone(), position, indexed)?.as_bool().ok_or_else(
                || vm.error(MlErrorKind::Type, operation, "predicate did not return bool"),
            )?;
        if answer {
            let result = if indexed {
                vm.track_value(Value(Rc::new(ValueData::Tuple(vec![
                    Value::int(position as i64),
                    item,
                ]))))
            } else {
                item
            };
            return Ok(option(vm, Some(result)));
        }
    }
    Ok(option(vm, None))
}
fn vector_find(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    find(vm, args, false, false, "Vector.find")
}
fn vector_findi(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    find(vm, args, false, true, "Vector.findi")
}
fn array_find(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    find(vm, args, true, false, "Array.find")
}
fn array_findi(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    find(vm, args, true, true, "Array.findi")
}
fn predicate(
    vm: &mut Vm,
    args: &[Value],
    is_array: bool,
    all: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let sequence = arg(vm, args, 1, operation)?;
    let length = sequence_length(vm, sequence, is_array, operation)?;
    for position in 0..length {
        vm.check_stop()?;
        let item = sequence_item(vm, sequence, position, operation)?;
        let result =
            super::text::apply_callback(vm, &args[0], &[item])?.as_bool().ok_or_else(|| {
                vm.error(MlErrorKind::Type, operation, "predicate did not return bool")
            })?;
        if result != all {
            return Ok(Value::bool(!all));
        }
    }
    Ok(Value::bool(all))
}
fn vector_exists(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    predicate(vm, args, false, false, "Vector.exists")
}
fn vector_all(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    predicate(vm, args, false, true, "Vector.all")
}
fn array_exists(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    predicate(vm, args, true, false, "Array.exists")
}
fn array_all(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    predicate(vm, args, true, true, "Array.all")
}
fn collate(vm: &mut Vm, args: &[Value], is_array: bool, operation: &str) -> Result<Value, MlError> {
    let [left, right] = fields(vm, arg(vm, args, 1, operation)?, 2, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected pair"));
    };
    let left_length = sequence_length(vm, left, is_array, operation)?;
    let right_length = sequence_length(vm, right, is_array, operation)?;
    for position in 0..left_length.min(right_length) {
        vm.check_stop()?;
        let left_item = sequence_item(vm, left, position, operation)?;
        let right_item = sequence_item(vm, right, position, operation)?;
        let input = vm.track_value(Value(Rc::new(ValueData::Tuple(vec![left_item, right_item]))));
        let comparison = super::text::apply_callback(vm, &args[0], &[input])?;
        let order = super::text::parse_order(vm, &comparison, operation)?;
        if order != std::cmp::Ordering::Equal {
            return super::text::ordering(vm, order);
        }
    }
    super::text::ordering(vm, left_length.cmp(&right_length))
}
fn vector_collate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    collate(vm, args, false, "Vector.collate")
}
fn array_collate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    collate(vm, args, true, "Array.collate")
}
