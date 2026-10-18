use super::*;

pub(super) fn install(vm: &mut Vm) {
    let string = typ("string");
    let char_type = typ("char");
    let optional_string = container("option", string.clone());
    let optional_char = container("option", char_type.clone());
    for (name, callback) in [
        ("String.toString", string_to_string as NativeFunction),
        ("String.toCString", string_to_c_string),
    ] {
        vm.register_pure(name, &[], function(string.clone(), string.clone()), 1, callback);
    }
    for (name, callback) in [
        ("String.fromString", string_from_string as NativeFunction),
        ("String.fromCString", string_from_c_string),
    ] {
        vm.register_pure(name, &[], function(string.clone(), optional_string.clone()), 1, callback);
    }
    for (name, callback) in
        [("Char.toString", char_to_string as NativeFunction), ("Char.toCString", char_to_c_string)]
    {
        vm.register_pure(name, &[], function(char_type.clone(), string.clone()), 1, callback);
    }
    for (name, callback) in [
        ("Char.fromString", char_from_string as NativeFunction),
        ("Char.fromCString", char_from_c_string),
    ] {
        vm.register_pure(name, &[], function(string.clone(), optional_char.clone()), 1, callback);
    }
    let reader = function(var(1), container("option", pair(char_type.clone(), var(1))));
    vm.register_pure(
        "Char.scan",
        &[1],
        function(reader.clone(), function(var(1), container("option", pair(char_type, var(1))))),
        2,
        char_scan,
    );
    vm.register_pure(
        "String.scan",
        &[1],
        function(reader, function(var(1), container("option", pair(string, var(1))))),
        2,
        string_scan,
    );
}

fn write_escape(result: &mut Vec<u8>, byte: u8, c_style: bool) {
    let simple = match byte {
        7 => Some(b'a'),
        8 => Some(b'b'),
        9 => Some(b't'),
        10 => Some(b'n'),
        11 => Some(b'v'),
        12 => Some(b'f'),
        13 => Some(b'r'),
        b'\\' => Some(b'\\'),
        b'"' => Some(b'"'),
        _ => None,
    };
    if let Some(escape) = simple {
        result.extend_from_slice(&[b'\\', escape]);
        return;
    }
    if c_style && matches!(byte, b'?' | b'\'') {
        result.extend_from_slice(&[b'\\', byte]);
        return;
    }
    if (32..=126).contains(&byte) {
        result.push(byte);
        return;
    }
    if !c_style && byte < 32 {
        result.extend_from_slice(&[b'\\', b'^', byte + 64]);
        return;
    }
    result.push(b'\\');
    if c_style {
        result.extend_from_slice(&[
            b'0' + ((byte >> 6) & 7),
            b'0' + ((byte >> 3) & 7),
            b'0' + (byte & 7),
        ]);
    } else {
        result.extend_from_slice(&[b'0' + byte / 100, b'0' + (byte / 10) % 10, b'0' + byte % 10]);
    }
}
fn escape_string(
    vm: &mut Vm,
    args: &[Value],
    c_style: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let source = bytes(vm, arg(vm, args, 0, operation)?, operation)?;
    let mut result = Vec::with_capacity(source.len());
    for &byte in source {
        vm.check_stop()?;
        write_escape(&mut result, byte, c_style);
    }
    Ok(Value::bytes(result))
}
fn string_to_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    escape_string(vm, args, false, "String.toString")
}
fn string_to_c_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    escape_string(vm, args, true, "String.toCString")
}
fn escape_char(
    vm: &mut Vm,
    args: &[Value],
    c_style: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let byte = character(vm, arg(vm, args, 0, operation)?, operation)?;
    let mut result = Vec::new();
    write_escape(&mut result, byte, c_style);
    Ok(Value::bytes(result))
}
fn char_to_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    escape_char(vm, args, false, "Char.toString")
}
fn char_to_c_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    escape_char(vm, args, true, "Char.toCString")
}

fn is_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | 11 | 12)
}
fn decode_byte(source: &[u8], start: usize, c_style: bool) -> Option<(Option<u8>, usize)> {
    let byte = *source.get(start)?;
    if byte != b'\\' {
        return if (32..=126).contains(&byte) { Some((Some(byte), start + 1)) } else { None };
    }
    let next = *source.get(start + 1)?;
    let decoded = match next {
        b'a' => 7,
        b'b' => 8,
        b't' => 9,
        b'n' => 10,
        b'v' => 11,
        b'f' => 12,
        b'r' => 13,
        b'\\' => b'\\',
        b'"' => b'"',
        b'?' | b'\'' if c_style => next,
        b'^' => {
            let control = *source.get(start + 2)?;
            if !(64..=95).contains(&control) {
                return None;
            }
            return Some((Some(control - 64), start + 3));
        },
        b'u' if !c_style => return decode_four_hex(source, start + 2),
        b'0'..=b'7' => return decode_digits(source, start + 1, c_style),
        b'8'..=b'9' if !c_style => return decode_digits(source, start + 1, false),
        b'x' if c_style => return decode_hex(source, start + 2),
        byte if !c_style && is_space(byte) => {
            let mut position = start + 2;
            while source.get(position).is_some_and(|&c| is_space(c)) {
                position += 1;
            }
            if source.get(position) != Some(&b'\\') {
                return None;
            }
            return Some((None, position + 1));
        },
        _ => return None,
    };
    Some((Some(decoded), start + 2))
}
fn decode_digits(source: &[u8], start: usize, c_style: bool) -> Option<(Option<u8>, usize)> {
    let mut position = start;
    let mut value = 0u16;
    let radix = if c_style { 8 } else { 10 };
    while position < start + 3 {
        let Some(&digit) = source.get(position) else {
            break;
        };
        if digit < b'0' || digit >= b'0' + radix as u8 {
            break;
        }
        value = value * radix + u16::from(digit - b'0');
        position += 1;
    }
    if position == start || !c_style && position != start + 3 {
        return None;
    }
    u8::try_from(value).ok().map(|value| (Some(value), position))
}
fn decode_hex(source: &[u8], start: usize) -> Option<(Option<u8>, usize)> {
    let mut position = start;
    let mut value = 0u32;
    while let Some(digit) = source.get(position).and_then(|c| (*c as char).to_digit(16)) {
        value = value.checked_mul(16)?.checked_add(digit)?;
        position += 1;
    }
    if position == start {
        return None;
    }
    u8::try_from(value).ok().map(|value| (Some(value), position))
}
fn decode_four_hex(source: &[u8], start: usize) -> Option<(Option<u8>, usize)> {
    let digits = source.get(start..start.checked_add(4)?)?;
    let value = digits.iter().try_fold(0u16, |number, digit| {
        Some(number * 16 + u16::try_from((*digit as char).to_digit(16)?).ok()?)
    })?;
    u8::try_from(value).ok().map(|byte| (Some(byte), start + 4))
}
fn parse_string(
    vm: &Vm,
    source: &[u8],
    c_style: bool,
    first_only: bool,
) -> Result<Option<Vec<u8>>, MlError> {
    let mut result = Vec::new();
    let mut position = 0;
    let mut has_prefix = false;
    while position < source.len() {
        vm.check_stop()?;
        let Some((value, next)) = decode_byte(source, position, c_style) else {
            return Ok((!first_only && has_prefix).then_some(result));
        };
        position = next;
        has_prefix = true;
        if let Some(value) = value {
            result.push(value);
            if first_only {
                return Ok(Some(result));
            }
        }
    }
    Ok(if first_only && result.is_empty() { None } else { Some(result) })
}
fn from_string(
    vm: &mut Vm,
    args: &[Value],
    c_style: bool,
    first_only: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let source = bytes(vm, arg(vm, args, 0, operation)?, operation)?;
    let value = parse_string(vm, source, c_style, first_only)?
        .map(|result| if first_only { Value::character(result[0]) } else { Value::bytes(result) });
    Ok(option(vm, value))
}
fn string_from_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    from_string(vm, args, false, false, "String.fromString")
}
fn string_from_c_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    from_string(vm, args, true, false, "String.fromCString")
}
fn char_from_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    from_string(vm, args, false, true, "Char.fromString")
}
fn char_from_c_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    from_string(vm, args, true, true, "Char.fromCString")
}

struct Reader<'a> {
    callback: &'a Value,
    state: Value,
    lookahead: Option<Option<(u8, Value)>>,
}
impl Reader<'_> {
    fn peek(&mut self, vm: &mut Vm) -> Result<Option<u8>, MlError> {
        if self.lookahead.is_none() {
            vm.check_stop()?;
            let value = apply_callback(vm, self.callback, std::slice::from_ref(&self.state))?;
            let decoded = option_argument(vm, &value, "text scan reader")?
                .map(|pair| {
                    let pair = fields(vm, pair, 2, "text scan reader")?;
                    Ok::<_, MlError>((
                        character(vm, &pair[0], "text scan reader")?,
                        pair[1].clone(),
                    ))
                })
                .transpose()?;
            self.lookahead = Some(decoded);
        }
        Ok(self.lookahead.as_ref().and_then(|result| result.as_ref().map(|(byte, _)| *byte)))
    }
    fn take(&mut self, vm: &mut Vm) -> Result<Option<u8>, MlError> {
        self.peek(vm)?;
        match self.lookahead.take().flatten() {
            Some((byte, state)) => {
                self.state = state;
                Ok(Some(byte))
            },
            None => Ok(None),
        }
    }
}
fn read_decimal(vm: &mut Vm, reader: &mut Reader<'_>, first: u8) -> Result<Option<u8>, MlError> {
    let mut value = u16::from(first - b'0');
    for _ in 1..3 {
        let Some(digit) = reader.take(vm)? else {
            return Ok(None);
        };
        if !digit.is_ascii_digit() {
            return Ok(None);
        }
        value = value * 10 + u16::from(digit - b'0');
    }
    Ok(u8::try_from(value).ok())
}
fn read_four_hex(vm: &mut Vm, reader: &mut Reader<'_>) -> Result<Option<u8>, MlError> {
    let mut value = 0u16;
    for _ in 0..4 {
        let Some(digit) = reader.take(vm)?.and_then(|byte| (byte as char).to_digit(16)) else {
            return Ok(None);
        };
        value = value * 16 + digit as u16;
    }
    Ok(u8::try_from(value).ok())
}
fn read_escape(vm: &mut Vm, reader: &mut Reader<'_>) -> Result<Option<Option<u8>>, MlError> {
    let Some(next) = reader.take(vm)? else {
        return Ok(None);
    };
    let mapped = match next {
        b'a' => 7,
        b'b' => 8,
        b't' => 9,
        b'n' => 10,
        b'v' => 11,
        b'f' => 12,
        b'r' => 13,
        b'\\' => b'\\',
        b'"' => b'"',
        b'0'..=b'2' => return Ok(read_decimal(vm, reader, next)?.map(Some)),
        b'u' => return Ok(read_four_hex(vm, reader)?.map(Some)),
        b'^' => {
            let Some(control) = reader.take(vm)? else {
                return Ok(None);
            };
            if !(64..=95).contains(&control) {
                return Ok(None);
            }
            control - 64
        },
        byte if is_space(byte) => {
            while reader.peek(vm)?.is_some_and(is_space) {
                reader.take(vm)?;
            }
            return Ok(if reader.take(vm)? == Some(b'\\') { Some(None) } else { None });
        },
        _ => return Ok(None),
    };
    Ok(Some(Some(mapped)))
}
fn scan(vm: &mut Vm, args: &[Value], single: bool, operation: &str) -> Result<Value, MlError> {
    let mut reader = Reader {
        callback: arg(vm, args, 0, operation)?,
        state: arg(vm, args, 1, operation)?.clone(),
        lookahead: None,
    };
    let mut result = Vec::new();
    let mut has_prefix = false;
    loop {
        let candidate_start = reader.state.clone();
        let Some(byte) = reader.take(vm)? else {
            break;
        };
        let decoded = if byte == b'\\' {
            read_escape(vm, &mut reader)?
        } else if (32..=126).contains(&byte) {
            Some(Some(byte))
        } else {
            None
        };
        let Some(decoded) = decoded else {
            reader.state = candidate_start;
            if !single && has_prefix {
                break;
            }
            return Ok(option(vm, None));
        };
        has_prefix = true;
        if let Some(decoded) = decoded {
            result.push(decoded);
            if single {
                break;
            }
        }
    }
    if single && result.is_empty() {
        return Ok(option(vm, None));
    }
    let value = if single { Value::character(result[0]) } else { Value::bytes(result) };
    let state = reader.state;
    let pair = tuple(vm, vec![value, state]);
    Ok(option(vm, Some(pair)))
}
fn char_scan(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    scan(vm, args, true, "Char.scan")
}
fn string_scan(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    scan(vm, args, false, "String.scan")
}
