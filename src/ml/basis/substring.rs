use super::text::{apply_callback, bounds, bytes, list, ordering, parse_order, tuple};
use super::*;

fn substring_type() -> Type {
    typ("substring")
}

pub(super) fn install(vm: &mut Vm) {
    let slice_type = substring_type();
    let string = typ("string");
    let integer = typ("int");
    let char_type = typ("char");
    let boolean = typ("bool");
    vm.type_environment.register_type("substring", 0, false);
    vm.register_exception("Span", &["Substring.Span", "General.Span"]);
    let empty = make_slice(vm, Value::bytes(Vec::new()), 0, 0);
    vm.register_value("Substring.empty", TypeScheme::mono(slice_type.clone()), empty);
    for name in ["Substring.full", "Substring.all"] {
        vm.register_pure(name, &[], function(string.clone(), slice_type.clone()), 1, full);
    }
    vm.register_pure(
        "Substring.base",
        &[],
        function(slice_type.clone(), triple(string.clone(), integer.clone(), integer.clone())),
        1,
        base,
    );
    vm.register_pure(
        "Substring.string",
        &[],
        function(slice_type.clone(), string.clone()),
        1,
        string_value,
    );
    vm.register_pure(
        "Substring.size",
        &[],
        function(slice_type.clone(), integer.clone()),
        1,
        size_value,
    );
    vm.register_pure(
        "Substring.isEmpty",
        &[],
        function(slice_type.clone(), boolean.clone()),
        1,
        is_empty,
    );
    vm.register_pure(
        "Substring.sub",
        &[],
        function(pair(slice_type.clone(), integer.clone()), char_type.clone()),
        1,
        sub,
    );
    vm.register_pure(
        "Substring.first",
        &[],
        function(slice_type.clone(), container("option", char_type.clone())),
        1,
        first,
    );
    vm.register_pure(
        "Substring.getc",
        &[],
        function(
            slice_type.clone(),
            container("option", pair(char_type.clone(), slice_type.clone())),
        ),
        1,
        getc,
    );
    vm.register_pure(
        "Substring.substring",
        &[],
        function(triple(string.clone(), integer.clone(), integer.clone()), slice_type.clone()),
        1,
        substring,
    );
    vm.register_pure(
        "Substring.extract",
        &[],
        function(
            triple(string.clone(), integer.clone(), container("option", integer.clone())),
            slice_type.clone(),
        ),
        1,
        extract,
    );
    vm.register_pure(
        "Substring.slice",
        &[],
        function(
            triple(slice_type.clone(), integer.clone(), container("option", integer.clone())),
            slice_type.clone(),
        ),
        1,
        slice,
    );
    register_trim(vm, "Substring.triml", trim_left, trim_left_start, LEFT_TRIM_INDEX);
    register_trim(vm, "Substring.trimr", trim_right, trim_right_start, RIGHT_TRIM_INDEX);
    vm.register_pure(
        "Substring.splitAt",
        &[],
        function(
            pair(slice_type.clone(), integer.clone()),
            pair(slice_type.clone(), slice_type.clone()),
        ),
        1,
        split_at,
    );
    for (name, callback) in [("splitl", split_left as NativeFunction), ("splitr", split_right)] {
        vm.register_pure(
            &format!("Substring.{name}"),
            &[],
            function(
                function(char_type.clone(), boolean.clone()),
                function(slice_type.clone(), pair(slice_type.clone(), slice_type.clone())),
            ),
            2,
            callback,
        );
    }
    for (name, callback) in [
        ("takel", take_left as NativeFunction),
        ("taker", take_right),
        ("dropl", drop_left),
        ("dropr", drop_right),
    ] {
        vm.register_pure(
            &format!("Substring.{name}"),
            &[],
            function(
                function(char_type.clone(), boolean.clone()),
                function(slice_type.clone(), slice_type.clone()),
            ),
            2,
            callback,
        );
    }
    for (name, callback) in [("tokens", tokens as NativeFunction), ("fields", split_fields)] {
        vm.register_pure(
            &format!("Substring.{name}"),
            &[],
            function(
                function(char_type.clone(), boolean.clone()),
                function(slice_type.clone(), container("list", slice_type.clone())),
            ),
            2,
            callback,
        );
    }
    vm.register_pure(
        "Substring.translate",
        &[],
        function(
            function(char_type.clone(), string.clone()),
            function(slice_type.clone(), string.clone()),
        ),
        2,
        translate,
    );
    vm.register_pure(
        "Substring.explode",
        &[],
        function(slice_type.clone(), container("list", char_type.clone())),
        1,
        explode,
    );
    vm.register_pure(
        "Substring.concat",
        &[],
        function(container("list", slice_type.clone()), string.clone()),
        1,
        concat,
    );
    vm.register_pure(
        "Substring.concatWith",
        &[],
        function(string.clone(), function(container("list", slice_type.clone()), string.clone())),
        2,
        concat_with,
    );
    vm.register_pure(
        "Substring.compare",
        &[],
        function(pair(slice_type.clone(), slice_type.clone()), typ("order")),
        1,
        compare,
    );
    vm.register_pure(
        "Substring.collate",
        &[],
        function(
            function(pair(char_type.clone(), char_type.clone()), typ("order")),
            function(pair(slice_type.clone(), slice_type.clone()), typ("order")),
        ),
        2,
        collate,
    );
    for (name, callback) in [
        ("isPrefix", is_prefix as NativeFunction),
        ("isSuffix", is_suffix),
        ("isSubstring", is_substring),
    ] {
        vm.register_pure(
            &format!("Substring.{name}"),
            &[],
            function(string.clone(), function(slice_type.clone(), boolean.clone())),
            2,
            callback,
        );
    }
    vm.register_pure(
        "Substring.position",
        &[],
        function(
            string.clone(),
            function(slice_type.clone(), pair(slice_type.clone(), slice_type.clone())),
        ),
        2,
        position,
    );
    install_iteration(vm, &slice_type, &char_type);
    vm.register_pure(
        "Substring.span",
        &[],
        function(pair(slice_type.clone(), slice_type.clone()), slice_type),
        1,
        span,
    );
}

fn install_iteration(vm: &mut Vm, slice: &Type, char_type: &Type) {
    let folder = function(pair(char_type.clone(), var(1)), var(1));
    for (name, callback) in [("foldl", fold_left as NativeFunction), ("foldr", fold_right)] {
        vm.register_pure(
            &format!("Substring.{name}"),
            &[1],
            function(folder.clone(), function(var(1), function(slice.clone(), var(1)))),
            3,
            callback,
        );
    }
    vm.register_pure(
        "Substring.app",
        &[],
        function(function(char_type.clone(), typ("unit")), function(slice.clone(), typ("unit"))),
        2,
        app,
    );
}

fn fold_slice(
    vm: &mut Vm,
    args: &[Value],
    reverse: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let source = input(vm, args, 2, operation)?;
    let mut result = args[1].clone();
    for position in 0..source.length {
        let byte = source.data()[if reverse { source.length - position - 1 } else { position }];
        vm.check_stop()?;
        let argument = tuple(vm, vec![Value::character(byte), result]);
        result = apply_callback(vm, &args[0], &[argument])?;
    }
    Ok(result)
}
fn fold_left(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    fold_slice(vm, args, false, "Substring.foldl")
}
fn fold_right(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    fold_slice(vm, args, true, "Substring.foldr")
}
fn app(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let source = input(vm, args, 1, "Substring.app")?;
    for &byte in source.data() {
        vm.check_stop()?;
        apply_callback(vm, &args[0], &[Value::character(byte)])?;
    }
    Ok(Value::unit())
}

struct Slice<'a> {
    source: &'a Value,
    offset: usize,
    length: usize,
    data: &'a [u8],
}
impl<'a> Slice<'a> {
    fn data(&self) -> &'a [u8] {
        self.data
    }
    fn part(&self, vm: &mut Vm, offset: usize, length: usize) -> Value {
        make_slice(vm, self.source.clone(), self.offset + offset, length)
    }
}
fn read_slice<'a>(vm: &Vm, value: &'a Value, operation: &str) -> Result<Slice<'a>, MlError> {
    let [source, offset, length] = fields(vm, value, 3, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "invalid substring storage"));
    };
    let data = bytes(vm, source, operation)?;
    let offset = offset.as_int().and_then(|n| usize::try_from(n).ok());
    let length = length.as_int().and_then(|n| usize::try_from(n).ok());
    match (offset, length) {
        (Some(offset), Some(length)) if offset <= data.len() && length <= data.len() - offset => {
            Ok(Slice { source, offset, length, data: &data[offset..offset + length] })
        },
        _ => Err(vm.error(MlErrorKind::Type, operation, "invalid substring offset or length")),
    }
}
fn make_slice(vm: &mut Vm, source: Value, offset: usize, length: usize) -> Value {
    tuple(vm, vec![source, Value::int(offset as i64), Value::int(length as i64)])
}
fn input<'a>(
    vm: &Vm,
    args: &'a [Value],
    index: usize,
    operation: &str,
) -> Result<Slice<'a>, MlError> {
    read_slice(vm, arg(vm, args, index, operation)?, operation)
}
fn full(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let source = arg(vm, args, 0, "Substring.full")?;
    let length = bytes(vm, source, "Substring.full")?.len();
    Ok(make_slice(vm, source.clone(), 0, length))
}
fn base(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let slice = input(vm, args, 0, "Substring.base")?;
    Ok(tuple(
        vm,
        vec![
            slice.source.clone(),
            Value::int(slice.offset as i64),
            Value::int(slice.length as i64),
        ],
    ))
}
fn string_value(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bytes(input(vm, args, 0, "Substring.string")?.data().to_vec()))
}
fn size_value(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::int(input(vm, args, 0, "Substring.size")?.length as i64))
}
fn is_empty(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(input(vm, args, 0, "Substring.isEmpty")?.length == 0))
}
fn sub(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 0, "Substring.sub")?, 2, "Substring.sub")?;
    let slice = read_slice(vm, &pair[0], "Substring.sub")?;
    let position = index(vm, &pair[1], slice.length, "Substring.sub")?;
    Ok(Value::character(slice.data()[position]))
}
fn first(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let slice = input(vm, args, 0, "Substring.first")?;
    Ok(text::option(vm, slice.data().first().copied().map(Value::character)))
}
fn getc(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let slice = input(vm, args, 0, "Substring.getc")?;
    let value = slice.data().first().copied().map(|byte| {
        let rest = slice.part(vm, 1, slice.length - 1);
        tuple(vm, vec![Value::character(byte), rest])
    });
    Ok(text::option(vm, value))
}
fn substring(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let triple = fields(vm, arg(vm, args, 0, "Substring.substring")?, 3, "Substring.substring")?;
    let total = bytes(vm, &triple[0], "Substring.substring")?.len();
    let (offset, length) = bounds(vm, &triple[1], Some(&triple[2]), total, "Substring.substring")?;
    Ok(make_slice(vm, triple[0].clone(), offset, length))
}
fn extract(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let triple = fields(vm, arg(vm, args, 0, "Substring.extract")?, 3, "Substring.extract")?;
    let total = bytes(vm, &triple[0], "Substring.extract")?.len();
    let length = option_argument(vm, &triple[2], "Substring.extract")?;
    let (offset, length) = bounds(vm, &triple[1], length, total, "Substring.extract")?;
    Ok(make_slice(vm, triple[0].clone(), offset, length))
}
fn slice(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let triple = fields(vm, arg(vm, args, 0, "Substring.slice")?, 3, "Substring.slice")?;
    let source = read_slice(vm, &triple[0], "Substring.slice")?;
    let length = option_argument(vm, &triple[2], "Substring.slice")?;
    let (offset, length) = bounds(vm, &triple[1], length, source.length, "Substring.slice")?;
    Ok(source.part(vm, offset, length))
}
const LEFT_TRIM_INDEX: usize = 0;
const RIGHT_TRIM_INDEX: usize = 1;

fn register_trim(
    vm: &mut Vm,
    name: &str,
    callback: NativeFunction,
    start: NativeFunction,
    index: usize,
) {
    let slice = substring_type();
    vm.register_pure(name, &[], function(typ("int"), function(slice.clone(), slice)), 1, start);
    let id = NativeFunctionId::new(vm.runtime_id, vm.generation, vm.native_functions.len());
    vm.native_functions.push((callback, 2));
    vm.substring_trim_ids[index] = Some(id);
}

fn start_trim(
    vm: &mut Vm,
    args: &[Value],
    operation: &str,
    index: usize,
) -> Result<Value, MlError> {
    let amount = arg(vm, args, 0, operation)?;
    read_trim_count(vm, amount, operation)?;
    let id = vm.substring_trim_ids[index].ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, operation, "trim operation is not registered")
    })?;
    let slice = substring_type();
    Ok(vm.track_value(Value(Rc::new(ValueData::NativePartial {
        id,
        arguments: RefCell::new(vec![amount.clone()]),
        argument_types: RefCell::new(vec![Some(typ("int"))]),
        result_type: RefCell::new(Some(function(slice.clone(), slice))),
    }))))
}

fn trim_left_start(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    start_trim(vm, args, "Substring.triml", LEFT_TRIM_INDEX)
}

fn trim_right_start(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    start_trim(vm, args, "Substring.trimr", RIGHT_TRIM_INDEX)
}
fn read_trim_count(vm: &Vm, argument: &Value, operation: &str) -> Result<i64, MlError> {
    let amount = argument
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected integer count"))?;
    if amount < 0 {
        return Err(vm.raise_basis("Subscript", operation, format!("negative trim {amount}")));
    }
    Ok(amount)
}
fn trim(vm: &mut Vm, args: &[Value], right: bool, operation: &str) -> Result<Value, MlError> {
    let amount = read_trim_count(vm, arg(vm, args, 0, operation)?, operation)?;
    let source = input(vm, args, 1, operation)?;
    let removed = usize::try_from(amount).unwrap_or(usize::MAX).min(source.length);
    let start = if right { 0 } else { removed };
    Ok(source.part(vm, start, source.length - removed))
}
fn trim_left(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    trim(vm, args, false, "Substring.triml")
}
fn trim_right(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    trim(vm, args, true, "Substring.trimr")
}
fn split_at(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 0, "Substring.splitAt")?, 2, "Substring.splitAt")?;
    let source = read_slice(vm, &pair[0], "Substring.splitAt")?;
    let (left, _) = bounds(vm, &pair[1], None, source.length, "Substring.splitAt")?;
    let first = source.part(vm, 0, left);
    let second = source.part(vm, left, source.length - left);
    Ok(tuple(vm, vec![first, second]))
}
fn split_while(
    vm: &mut Vm,
    args: &[Value],
    right: bool,
    operation: &str,
) -> Result<(Value, Value), MlError> {
    let source = input(vm, args, 1, operation)?;
    let mut count = 0;
    for position in 0..source.length {
        let byte = source.data()[if right { source.length - position - 1 } else { position }];
        vm.check_stop()?;
        let answer =
            apply_callback(vm, &args[0], &[Value::character(byte)])?.as_bool().ok_or_else(
                || vm.error(MlErrorKind::Type, operation, "predicate did not return bool"),
            )?;
        if !answer {
            break;
        }
        count += 1;
    }
    let pivot = if right { source.length - count } else { count };
    let first = source.part(vm, 0, pivot);
    let second = source.part(vm, pivot, source.length - pivot);
    Ok((first, second))
}
fn split_left(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = split_while(vm, args, false, "Substring.splitl")?;
    Ok(tuple(vm, vec![left, right]))
}
fn split_right(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = split_while(vm, args, true, "Substring.splitr")?;
    Ok(tuple(vm, vec![left, right]))
}
fn take_left(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(split_while(vm, args, false, "Substring.takel")?.0)
}
fn take_right(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(split_while(vm, args, true, "Substring.taker")?.1)
}
fn drop_left(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(split_while(vm, args, false, "Substring.dropl")?.1)
}
fn drop_right(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(split_while(vm, args, true, "Substring.dropr")?.0)
}
fn split_parts(
    vm: &mut Vm,
    args: &[Value],
    keep_empty: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let source = input(vm, args, 1, operation)?;
    let mut result = Vec::new();
    let mut start = 0;
    for (position, &byte) in source.data().iter().enumerate() {
        vm.check_stop()?;
        let answer =
            apply_callback(vm, &args[0], &[Value::character(byte)])?.as_bool().ok_or_else(
                || vm.error(MlErrorKind::Type, operation, "predicate did not return bool"),
            )?;
        if answer {
            if keep_empty || position > start {
                result.push(source.part(vm, start, position - start));
            }
            start = position + 1;
        }
    }
    if keep_empty || start < source.length {
        result.push(source.part(vm, start, source.length - start));
    }
    Ok(list(vm, result))
}
fn tokens(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    split_parts(vm, args, false, "Substring.tokens")
}
fn split_fields(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    split_parts(vm, args, true, "Substring.fields")
}
fn translate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let source = input(vm, args, 1, "Substring.translate")?;
    let mut result = Vec::new();
    for &byte in source.data() {
        vm.check_stop()?;
        let mapped = apply_callback(vm, &args[0], &[Value::character(byte)])?;
        result.extend_from_slice(bytes(vm, &mapped, "Substring.translate")?);
    }
    Ok(Value::bytes(result))
}
fn explode(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let source = input(vm, args, 0, "Substring.explode")?;
    let mut result = Vec::with_capacity(source.length);
    for &byte in source.data() {
        vm.check_stop()?;
        result.push(Value::character(byte));
    }
    Ok(list(vm, result))
}
fn concat(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = items(vm, arg(vm, args, 0, "Substring.concat")?, "Substring.concat")?;
    concatenate_slices(vm, values, &[], "Substring.concat")
}
fn concat_with(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let separator = bytes(vm, arg(vm, args, 0, "Substring.concatWith")?, "Substring.concatWith")?;
    let values = items(vm, arg(vm, args, 1, "Substring.concatWith")?, "Substring.concatWith")?;
    concatenate_slices(vm, values, separator, "Substring.concatWith")
}
fn concatenate_slices(
    vm: &Vm,
    values: &[Value],
    separator: &[u8],
    operation: &str,
) -> Result<Value, MlError> {
    if let [only] = values {
        let slice = read_slice(vm, only, operation)?;
        if slice.offset == 0
            && slice.source.as_bytes().is_some_and(|bytes| bytes.len() == slice.length)
        {
            return Ok(slice.source.clone());
        }
    }
    let length = compute_joined_length(vm, values, separator.len(), operation)?;
    let mut result = Vec::new();
    result.try_reserve_exact(length).map_err(|cause| {
        vm.raise_basis("Size", operation, format!("allocating {length} bytes: {cause}"))
    })?;
    for (index, value) in values.iter().enumerate() {
        vm.check_stop()?;
        if index != 0 {
            result.extend_from_slice(separator);
        }
        result.extend_from_slice(read_slice(vm, value, operation)?.data());
    }
    Ok(Value::bytes(result))
}
fn compute_joined_length(
    vm: &Vm,
    values: &[Value],
    separator_length: usize,
    operation: &str,
) -> Result<usize, MlError> {
    let size_error =
        || vm.raise_basis("Size", operation, "combined string length overflow".to_owned());
    let mut length = separator_length
        .checked_mul(values.len().saturating_sub(1))
        .filter(|length| *length <= text::MAX_STRING_LENGTH)
        .ok_or_else(size_error)?;
    for value in values {
        vm.check_stop()?;
        length = length
            .checked_add(read_slice(vm, value, operation)?.length)
            .filter(|length| *length <= text::MAX_STRING_LENGTH)
            .ok_or_else(size_error)?;
    }
    Ok(length)
}
fn compare(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 0, "Substring.compare")?, 2, "Substring.compare")?;
    let first = read_slice(vm, &pair[0], "Substring.compare")?;
    let second = read_slice(vm, &pair[1], "Substring.compare")?;
    ordering(vm, first.data().cmp(second.data()))
}
fn collate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 1, "Substring.collate")?, 2, "Substring.collate")?;
    let first = read_slice(vm, &pair[0], "Substring.collate")?;
    let second = read_slice(vm, &pair[1], "Substring.collate")?;
    for (&a, &b) in first.data().iter().zip(second.data()) {
        vm.check_stop()?;
        let pair = tuple(vm, vec![Value::character(a), Value::character(b)]);
        let answer = apply_callback(vm, &args[0], &[pair])?;
        let order = parse_order(vm, &answer, "Substring.collate")?;
        if order != std::cmp::Ordering::Equal {
            return ordering(vm, order);
        }
    }
    ordering(vm, first.length.cmp(&second.length))
}
fn affix(
    vm: &mut Vm,
    args: &[Value],
    operation: &str,
    test: impl FnOnce(&[u8], &[u8]) -> bool,
) -> Result<Value, MlError> {
    let needle = bytes(vm, &args[0], operation)?;
    let source = input(vm, args, 1, operation)?;
    Ok(Value::bool(test(source.data(), needle)))
}
fn is_prefix(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    affix(vm, args, "Substring.isPrefix", |s, n| s.starts_with(n))
}
fn is_suffix(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    affix(vm, args, "Substring.isSuffix", |s, n| s.ends_with(n))
}
fn is_substring(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let needle = bytes(vm, arg(vm, args, 0, "Substring.isSubstring")?, "Substring.isSubstring")?;
    let source = input(vm, args, 1, "Substring.isSubstring")?;
    Ok(Value::bool(text::find_bytes(vm, source.data(), needle)?.is_some()))
}
fn position(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let needle = bytes(vm, &args[0], "Substring.position")?;
    let source = input(vm, args, 1, "Substring.position")?;
    let offset = text::find_bytes(vm, source.data(), needle)?.unwrap_or(source.length);
    let first = source.part(vm, 0, offset);
    let second = source.part(vm, offset, source.length - offset);
    Ok(tuple(vm, vec![first, second]))
}
fn span(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 0, "Substring.span")?, 2, "Substring.span")?;
    let left = read_slice(vm, &pair[0], "Substring.span")?;
    let right = read_slice(vm, &pair[1], "Substring.span")?;
    let has_same_base = left.source.is_same_object(right.source)
        || left.source.as_bytes() == right.source.as_bytes();
    let right_end = right.offset + right.length;
    if !has_same_base || right_end < left.offset {
        return Err(vm.raise_basis(
            "Span",
            "Substring.span",
            "different bases or right end precedes left start".to_owned(),
        ));
    }
    Ok(make_slice(vm, left.source.clone(), left.offset, right_end - left.offset))
}
