use super::*;

#[path = "text/comparison.rs"]
mod comparison;
#[path = "text/escape.rs"]
mod escape;

pub(super) const MAX_STRING_LENGTH: usize = isize::MAX as usize;

pub(super) fn install(vm: &mut Vm) {
    let integer = typ("int");
    let char_type = typ("char");
    vm.type_environment.register_type("order", 0, true);
    let constructors = ["LESS", "EQUAL", "GREATER"].map(|name| {
        let value = Value(Rc::new(ValueData::Constructor {
            stamp: vm.fresh_identity(),
            name: name.to_owned(),
            argument: None,
        }));
        vm.register_value(name, TypeScheme::mono(typ("order")), value.clone());
        value
    });
    vm.basis_order = Some(constructors);
    vm.register_value(
        "String.maxSize",
        TypeScheme::mono(integer.clone()),
        Value::int(MAX_STRING_LENGTH as i64),
    );
    vm.register_value("Char.maxOrd", TypeScheme::mono(integer.clone()), Value::int(u8::MAX as i64));
    vm.register_value("Char.minChar", TypeScheme::mono(char_type.clone()), Value::character(0));
    vm.register_value("Char.maxChar", TypeScheme::mono(char_type.clone()), Value::character(255));
    install_string(vm);
    install_char(vm);
    escape::install(vm);
    comparison::install(vm);
}

fn install_string(vm: &mut Vm) {
    let string = typ("string");
    let char_type = typ("char");
    let boolean = typ("bool");
    let integer = typ("int");
    let string_list = container("list", string.clone());
    let char_list = container("list", char_type.clone());
    for name in ["^", "String.^"] {
        vm.register_pure(
            name,
            &[],
            function(pair(string.clone(), string.clone()), string.clone()),
            1,
            append,
        );
    }
    for (name, callback) in [("String.size", string_size as NativeFunction), ("size", string_size)]
    {
        vm.register_pure(name, &[], function(string.clone(), integer.clone()), 1, callback);
    }
    vm.register_pure(
        "String.sub",
        &[],
        function(pair(string.clone(), integer.clone()), char_type.clone()),
        1,
        string_sub,
    );
    vm.register_pure(
        "String.nth",
        &[],
        function(string.clone(), function(integer.clone(), char_type.clone())),
        2,
        string_nth,
    );
    vm.register_pure(
        "String.substring",
        &[],
        function(triple(string.clone(), integer.clone(), integer.clone()), string.clone()),
        1,
        string_substring,
    );
    vm.register_pure(
        "String.extract",
        &[],
        function(
            triple(string.clone(), integer.clone(), container("option", integer.clone())),
            string.clone(),
        ),
        1,
        string_extract,
    );
    vm.register_pure(
        "String.explode",
        &[],
        function(string.clone(), char_list.clone()),
        1,
        string_explode,
    );
    vm.register_pure("String.implode", &[], function(char_list, string.clone()), 1, string_implode);
    vm.register_pure(
        "String.concat",
        &[],
        function(string_list.clone(), string.clone()),
        1,
        string_concat,
    );
    vm.register_pure(
        "String.concatWith",
        &[],
        function(string.clone(), function(string_list, string.clone())),
        2,
        string_concat_with,
    );
    vm.register_pure("String.str", &[], function(char_type.clone(), string.clone()), 1, string_str);
    for (name, callback) in [
        ("String.isPrefix", is_prefix as NativeFunction),
        ("String.isSuffix", is_suffix),
        ("String.isSubstring", is_substring),
    ] {
        vm.register_pure(
            name,
            &[],
            function(string.clone(), function(string.clone(), boolean.clone())),
            2,
            callback,
        );
    }
    vm.register_pure(
        "String.compare",
        &[],
        function(pair(string.clone(), string.clone()), typ("order")),
        1,
        string_compare,
    );
    vm.register_pure(
        "String.collate",
        &[],
        function(
            function(pair(char_type.clone(), char_type.clone()), typ("order")),
            function(pair(string.clone(), string.clone()), typ("order")),
        ),
        2,
        string_collate,
    );
    for (name, callback) in
        [("String.tokens", string_tokens as NativeFunction), ("String.fields", string_fields)]
    {
        vm.register_pure(
            name,
            &[],
            function(
                function(char_type.clone(), boolean.clone()),
                function(string.clone(), container("list", string.clone())),
            ),
            2,
            callback,
        );
    }
    vm.register_pure(
        "String.translate",
        &[],
        function(
            function(char_type.clone(), string.clone()),
            function(string.clone(), string.clone()),
        ),
        2,
        string_translate,
    );
    vm.register_pure(
        "String.map",
        &[],
        function(
            function(char_type.clone(), char_type.clone()),
            function(string.clone(), string.clone()),
        ),
        2,
        string_map,
    );
    for (name, callback) in
        [("String.exists", string_exists as NativeFunction), ("String.forall", string_forall)]
    {
        vm.register_pure(
            name,
            &[],
            function(
                function(char_type.clone(), boolean.clone()),
                function(string.clone(), boolean.clone()),
            ),
            2,
            callback,
        );
    }
    vm.register_pure(
        "String.member",
        &[],
        function(string.clone(), function(char_type.clone(), boolean.clone())),
        2,
        string_member,
    );
    for (name, callback) in
        [("String.fold", string_fold as NativeFunction), ("String.fold_rev", string_fold_rev)]
    {
        vm.register_pure(
            name,
            &[1],
            function(
                function(char_type.clone(), function(var(1), var(1))),
                function(string.clone(), function(var(1), var(1))),
            ),
            3,
            callback,
        );
    }
}

fn install_char(vm: &mut Vm) {
    let char_type = typ("char");
    let integer = typ("int");
    let boolean = typ("bool");
    let string = typ("string");
    vm.register_pure("Char.ord", &[], function(char_type.clone(), integer.clone()), 1, char_ord);
    vm.register_pure("Char.chr", &[], function(integer.clone(), char_type.clone()), 1, char_chr);
    vm.register_pure(
        "Char.compare",
        &[],
        function(pair(char_type.clone(), char_type.clone()), typ("order")),
        1,
        char_compare,
    );
    for (name, callback) in [
        ("Char.isAscii", char_is_ascii as NativeFunction),
        ("Char.isAlpha", char_is_alpha),
        ("Char.isAlphaNum", char_is_alpha_num),
        ("Char.isDigit", char_is_digit),
        ("Char.isHexDigit", char_is_hex_digit),
        ("Char.isLower", char_is_lower),
        ("Char.isUpper", char_is_upper),
        ("Char.isSpace", char_is_space),
        ("Char.isPrint", char_is_print),
        ("Char.isGraph", char_is_graph),
        ("Char.isPunct", char_is_punct),
        ("Char.isCntrl", char_is_control),
    ] {
        vm.register_pure(name, &[], function(char_type.clone(), boolean.clone()), 1, callback);
    }
    for (name, callback) in
        [("Char.toLower", char_to_lower as NativeFunction), ("Char.toUpper", char_to_upper)]
    {
        vm.register_pure(name, &[], function(char_type.clone(), char_type.clone()), 1, callback);
    }
    for (name, callback) in [("Char.succ", char_succ as NativeFunction), ("Char.pred", char_pred)] {
        vm.register_pure(name, &[], function(char_type.clone(), char_type.clone()), 1, callback);
    }
    vm.register_pure(
        "Char.contains",
        &[],
        function(string.clone(), function(char_type.clone(), boolean.clone())),
        2,
        char_contains,
    );
    vm.register_pure(
        "Char.notContains",
        &[],
        function(string.clone(), function(char_type.clone(), boolean.clone())),
        2,
        char_not_contains,
    );
}

pub(super) fn bytes<'a>(vm: &Vm, value: &'a Value, operation: &str) -> Result<&'a [u8], MlError> {
    value.as_bytes().ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected string"))
}
pub(super) fn character(vm: &Vm, value: &Value, operation: &str) -> Result<u8, MlError> {
    match &*value.0 {
        ValueData::Character(c) => Ok(*c),
        _ => Err(vm.error(MlErrorKind::Type, operation, "expected char")),
    }
}
pub(super) fn tuple(vm: &mut Vm, values: Vec<Value>) -> Value {
    vm.track_value(Value(Rc::new(ValueData::Tuple(values))))
}
pub(super) fn list(vm: &mut Vm, values: Vec<Value>) -> Value {
    vm.track_value(Value(Rc::new(ValueData::List(values))))
}
pub(super) fn option(vm: &mut Vm, value: Option<Value>) -> Value {
    let (stamp, name) = if value.is_some() {
        (vm.option_some_stamp, "SOME")
    } else {
        (vm.option_none_stamp, "NONE")
    };
    vm.track_value(Value(Rc::new(ValueData::Constructor {
        stamp,
        name: name.to_owned(),
        argument: value,
    })))
}
pub(super) fn apply_callback(
    vm: &mut Vm,
    callback: &Value,
    arguments: &[Value],
) -> Result<Value, MlError> {
    let callback_type = vm.native_argument_type(0);
    apply_typed_callback(vm, callback, arguments, callback_type)
}

pub(super) fn apply_typed_callback(
    vm: &mut Vm,
    callback: &Value,
    arguments: &[Value],
    callback_type: Option<Type>,
) -> Result<Value, MlError> {
    let mut callback_type = callback_type.ok_or_else(|| {
        vm.error(
            MlErrorKind::HostFailure,
            "native higher-order callback",
            "missing compiler-certified callback type",
        )
    })?;
    let mut result = callback.clone();
    for argument in arguments {
        let Type::Function(input, output) = callback_type else {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "native higher-order callback",
                "compiler-certified callback type is not a function",
            ));
        };
        result = vm.apply_with_type(&result, argument, *input)?;
        callback_type = *output;
    }
    vm.check_stop()?;
    Ok(result)
}
pub(super) fn ordering(vm: &Vm, ordering: std::cmp::Ordering) -> Result<Value, MlError> {
    let [less, equal, greater] = vm.basis_order.as_ref().ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, "compare", "order Basis is not initialized")
    })?;
    Ok(match ordering {
        std::cmp::Ordering::Less => less,
        std::cmp::Ordering::Equal => equal,
        std::cmp::Ordering::Greater => greater,
    }
    .clone())
}
pub(super) fn parse_order(
    vm: &Vm,
    value: &Value,
    operation: &str,
) -> Result<std::cmp::Ordering, MlError> {
    let [less, equal, greater] = vm.basis_order.as_ref().ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, operation, "order Basis is not initialized")
    })?;
    for (expected, order) in [
        (less, std::cmp::Ordering::Less),
        (equal, std::cmp::Ordering::Equal),
        (greater, std::cmp::Ordering::Greater),
    ] {
        if let (
            ValueData::Constructor { stamp: actual, argument: None, .. },
            ValueData::Constructor { stamp: target, .. },
        ) = (&*value.0, &*expected.0)
            && actual == target
        {
            return Ok(order);
        }
    }
    Err(vm.error(MlErrorKind::Type, operation, "collator did not return an order"))
}
pub(super) fn bounds(
    vm: &Vm,
    start: &Value,
    length: Option<&Value>,
    total: usize,
    operation: &str,
) -> Result<(usize, usize), MlError> {
    let start_int = start
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected integer offset"))?;
    let start = usize::try_from(start_int).ok().filter(|&n| n <= total).ok_or_else(|| {
        vm.raise_basis("Subscript", operation, format!("offset {start_int}, length {total}"))
    })?;
    let count = if let Some(length) = length {
        let requested = length
            .as_int()
            .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected integer length"))?;
        usize::try_from(requested).ok().filter(|&n| n <= total - start).ok_or_else(|| {
            vm.raise_basis(
                "Subscript",
                operation,
                format!("offset {start_int}, count {requested}, length {total}"),
            )
        })?
    } else {
        total - start
    };
    Ok((start, count))
}
fn append(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 0, "^")?, 2, "^")?;
    let left = bytes(vm, &pair[0], "^")?;
    let right = bytes(vm, &pair[1], "^")?;
    let mut result = Vec::with_capacity(left.len() + right.len());
    result.extend_from_slice(left);
    result.extend_from_slice(right);
    Ok(Value::bytes(result))
}
fn string_size(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::int(bytes(vm, arg(vm, args, 0, "String.size")?, "String.size")?.len() as i64))
}
fn string_sub(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 0, "String.sub")?, 2, "String.sub")?;
    let text = bytes(vm, &pair[0], "String.sub")?;
    Ok(Value::character(text[index(vm, &pair[1], text.len(), "String.sub")?]))
}
fn string_nth(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 0, "String.nth")?, "String.nth")?;
    Ok(Value::character(
        text[index(vm, arg(vm, args, 1, "String.nth")?, text.len(), "String.nth")?],
    ))
}
fn string_substring(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = fields(vm, arg(vm, args, 0, "String.substring")?, 3, "String.substring")?;
    let text = bytes(vm, &values[0], "String.substring")?;
    let (start, length) = bounds(vm, &values[1], Some(&values[2]), text.len(), "String.substring")?;
    Ok(Value::bytes(text[start..start + length].to_vec()))
}
fn string_extract(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = fields(vm, arg(vm, args, 0, "String.extract")?, 3, "String.extract")?;
    let text = bytes(vm, &values[0], "String.extract")?;
    let count = option_argument(vm, &values[2], "String.extract")?;
    let (start, length) = bounds(vm, &values[1], count, text.len(), "String.extract")?;
    Ok(Value::bytes(text[start..start + length].to_vec()))
}
fn string_explode(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 0, "String.explode")?, "String.explode")?;
    let mut values = Vec::with_capacity(text.len());
    for &byte in text {
        vm.check_stop()?;
        values.push(Value::character(byte));
    }
    Ok(list(vm, values))
}
fn string_implode(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = items(vm, arg(vm, args, 0, "String.implode")?, "String.implode")?;
    let mut text = Vec::with_capacity(values.len());
    for value in values {
        vm.check_stop()?;
        text.push(character(vm, value, "String.implode")?);
    }
    Ok(Value::bytes(text))
}
fn string_concat(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = items(vm, arg(vm, args, 0, "String.concat")?, "String.concat")?;
    let mut result = Vec::new();
    for value in values {
        vm.check_stop()?;
        result.extend_from_slice(bytes(vm, value, "String.concat")?);
    }
    Ok(Value::bytes(result))
}
fn string_concat_with(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let separator = bytes(vm, arg(vm, args, 0, "String.concatWith")?, "String.concatWith")?;
    let values = items(vm, arg(vm, args, 1, "String.concatWith")?, "String.concatWith")?;
    let mut result = Vec::new();
    for (index, value) in values.iter().enumerate() {
        vm.check_stop()?;
        if index != 0 {
            result.extend_from_slice(separator);
        }
        result.extend_from_slice(bytes(vm, value, "String.concatWith")?);
    }
    Ok(Value::bytes(result))
}
fn string_str(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bytes(vec![character(vm, arg(vm, args, 0, "String.str")?, "String.str")?]))
}
fn is_prefix(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    test_affix(vm, args, "String.isPrefix", |haystack, needle| haystack.starts_with(needle))
}
fn is_suffix(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    test_affix(vm, args, "String.isSuffix", |haystack, needle| haystack.ends_with(needle))
}
fn is_substring(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let needle = bytes(vm, arg(vm, args, 0, "String.isSubstring")?, "String.isSubstring")?;
    let haystack = bytes(vm, arg(vm, args, 1, "String.isSubstring")?, "String.isSubstring")?;
    Ok(Value::bool(find_bytes(vm, haystack, needle)?.is_some()))
}
pub(super) fn find_bytes(
    vm: &Vm,
    haystack: &[u8],
    needle: &[u8],
) -> Result<Option<usize>, MlError> {
    if needle.len() > haystack.len() {
        return Ok(None);
    }
    for offset in 0..=haystack.len() - needle.len() {
        vm.check_stop()?;
        if &haystack[offset..offset + needle.len()] == needle {
            return Ok(Some(offset));
        }
    }
    Ok(None)
}
fn test_affix(
    vm: &mut Vm,
    args: &[Value],
    operation: &str,
    test: impl FnOnce(&[u8], &[u8]) -> bool,
) -> Result<Value, MlError> {
    let needle = bytes(vm, arg(vm, args, 0, operation)?, operation)?;
    let haystack = bytes(vm, arg(vm, args, 1, operation)?, operation)?;
    Ok(Value::bool(test(haystack, needle)))
}
fn string_compare(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    ordering(vm, comparison::compare_strings(vm, args, "String.compare")?)
}
fn string_collate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = fields(vm, arg(vm, args, 1, "String.collate")?, 2, "String.collate")?;
    let left = bytes(vm, &pair[0], "String.collate")?;
    let right = bytes(vm, &pair[1], "String.collate")?;
    for (&a, &b) in left.iter().zip(right) {
        vm.check_stop()?;
        let tuple = tuple(vm, vec![Value::character(a), Value::character(b)]);
        let answer = apply_callback(vm, &args[0], &[tuple])?;
        let order = parse_order(vm, &answer, "String.collate")?;
        if order != std::cmp::Ordering::Equal {
            return ordering(vm, order);
        }
    }
    ordering(vm, left.len().cmp(&right.len()))
}
fn split_string(
    vm: &mut Vm,
    args: &[Value],
    keep_empty: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 1, operation)?, operation)?;
    let mut result = Vec::new();
    let mut start = 0;
    for (position, &byte) in text.iter().enumerate() {
        vm.check_stop()?;
        let answer =
            apply_callback(vm, &args[0], &[Value::character(byte)])?.as_bool().ok_or_else(
                || vm.error(MlErrorKind::Type, operation, "predicate did not return bool"),
            )?;
        if answer {
            if keep_empty || position > start {
                result.push(Value::bytes(text[start..position].to_vec()));
            }
            start = position + 1;
        }
    }
    if keep_empty || start < text.len() {
        result.push(Value::bytes(text[start..].to_vec()));
    }
    Ok(list(vm, result))
}
fn string_tokens(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    split_string(vm, args, false, "String.tokens")
}
fn string_fields(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    split_string(vm, args, true, "String.fields")
}
fn string_translate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 1, "String.translate")?, "String.translate")?;
    let mut result = Vec::new();
    for &byte in text {
        vm.check_stop()?;
        let translated = apply_callback(vm, &args[0], &[Value::character(byte)])?;
        result.extend_from_slice(bytes(vm, &translated, "String.translate")?);
    }
    Ok(Value::bytes(result))
}
fn string_map(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 1, "String.map")?, "String.map")?;
    let mut result = Vec::with_capacity(text.len());
    for &byte in text {
        vm.check_stop()?;
        let mapped = apply_callback(vm, &args[0], &[Value::character(byte)])?;
        result.push(character(vm, &mapped, "String.map")?);
    }
    Ok(Value::bytes(result))
}
fn string_predicate(
    vm: &mut Vm,
    args: &[Value],
    all: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 1, operation)?, operation)?;
    for &byte in text {
        vm.check_stop()?;
        let answer =
            apply_callback(vm, &args[0], &[Value::character(byte)])?.as_bool().ok_or_else(
                || vm.error(MlErrorKind::Type, operation, "predicate did not return bool"),
            )?;
        if answer != all {
            return Ok(Value::bool(!all));
        }
    }
    Ok(Value::bool(all))
}
fn string_exists(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    string_predicate(vm, args, false, "String.exists")
}
fn string_forall(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    string_predicate(vm, args, true, "String.forall")
}
fn string_member(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 0, "String.member")?, "String.member")?;
    let needle = character(vm, arg(vm, args, 1, "String.member")?, "String.member")?;
    Ok(Value::bool(text.contains(&needle)))
}
fn fold_string(
    vm: &mut Vm,
    args: &[Value],
    reverse: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 1, operation)?, operation)?;
    let mut result = args[2].clone();
    if reverse {
        for &byte in text.iter().rev() {
            vm.check_stop()?;
            result = apply_callback(vm, &args[0], &[Value::character(byte), result])?;
        }
    } else {
        for &byte in text {
            vm.check_stop()?;
            result = apply_callback(vm, &args[0], &[Value::character(byte), result])?;
        }
    }
    Ok(result)
}
fn string_fold(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    fold_string(vm, args, false, "String.fold")
}
fn string_fold_rev(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    fold_string(vm, args, true, "String.fold_rev")
}
fn char_ord(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::int(character(vm, arg(vm, args, 0, "Char.ord")?, "Char.ord")? as i64))
}
fn char_chr(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let n = arg(vm, args, 0, "Char.chr")?
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "Char.chr", "expected integer"))?;
    let byte = u8::try_from(n)
        .map_err(|_| vm.raise_basis("Chr", "Char.chr", format!("character code {n}")))?;
    Ok(Value::character(byte))
}
fn char_compare(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    ordering(vm, comparison::compare_characters(vm, args, "Char.compare")?)
}
fn classify_char(
    vm: &mut Vm,
    args: &[Value],
    operation: &str,
    predicate: impl FnOnce(u8) -> bool,
) -> Result<Value, MlError> {
    Ok(Value::bool(predicate(character(vm, arg(vm, args, 0, operation)?, operation)?)))
}
fn is_print(byte: u8) -> bool {
    (b' '..=b'~').contains(&byte)
}
fn is_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | 11 | 12 | b'\r')
}
fn char_is_ascii(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isAscii", |c| c.is_ascii())
}
fn char_is_alpha(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isAlpha", |c| c.is_ascii_alphabetic())
}
fn char_is_alpha_num(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isAlphaNum", |c| c.is_ascii_alphanumeric())
}
fn char_is_digit(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isDigit", |c| c.is_ascii_digit())
}
fn char_is_hex_digit(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isHexDigit", |c| c.is_ascii_hexdigit())
}
fn char_is_lower(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isLower", |c| c.is_ascii_lowercase())
}
fn char_is_upper(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isUpper", |c| c.is_ascii_uppercase())
}
fn char_is_space(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isSpace", is_space)
}
fn char_is_print(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isPrint", is_print)
}
fn char_is_graph(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isGraph", |c| (b'!'..=b'~').contains(&c))
}
fn char_is_punct(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isPunct", |c| c.is_ascii_punctuation())
}
fn char_is_control(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    classify_char(vm, args, "Char.isCntrl", |c| c.is_ascii() && !is_print(c))
}
fn char_to_lower(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::character(
        character(vm, arg(vm, args, 0, "Char.toLower")?, "Char.toLower")?.to_ascii_lowercase(),
    ))
}
fn char_to_upper(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::character(
        character(vm, arg(vm, args, 0, "Char.toUpper")?, "Char.toUpper")?.to_ascii_uppercase(),
    ))
}
fn char_succ(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let byte = character(vm, arg(vm, args, 0, "Char.succ")?, "Char.succ")?;
    let next = byte
        .checked_add(1)
        .ok_or_else(|| vm.raise_basis("Chr", "Char.succ", "maxChar".to_owned()))?;
    Ok(Value::character(next))
}
fn char_pred(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let byte = character(vm, arg(vm, args, 0, "Char.pred")?, "Char.pred")?;
    let previous = byte
        .checked_sub(1)
        .ok_or_else(|| vm.raise_basis("Chr", "Char.pred", "minChar".to_owned()))?;
    Ok(Value::character(previous))
}
fn char_contains(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    contains_char(vm, args, false, "Char.contains")
}
fn char_not_contains(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    contains_char(vm, args, true, "Char.notContains")
}
fn contains_char(
    vm: &mut Vm,
    args: &[Value],
    negate: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let text = bytes(vm, arg(vm, args, 0, operation)?, operation)?;
    let byte = character(vm, arg(vm, args, 1, operation)?, operation)?;
    Ok(Value::bool(text.contains(&byte) != negate))
}
