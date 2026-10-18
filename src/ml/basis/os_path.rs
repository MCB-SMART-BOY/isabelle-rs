//! Syntactic Unix OS.Path operations needed by Isabelle's unmodified ML bootstrap.
use super::{MlError, MlErrorKind, Type, Value, ValueData, Vm, arg, fields, function, pair, typ};
use std::collections::BTreeMap;
use std::rc::Rc;

pub(super) fn install(vm: &mut Vm) {
    let string = typ("string");
    let arcs = Type::Constructor("list".to_owned(), vec![string.clone()]);
    let parts = Type::Record(
        BTreeMap::from([
            ("isAbs".to_owned(), typ("bool")),
            ("vol".to_owned(), string.clone()),
            ("arcs".to_owned(), arcs),
        ]),
        false,
    );
    vm.register_exception("OS.Path.Path", &["OS.Path.Path"]);
    vm.register_pure("OS.Path.fromString", &[], function(string.clone(), parts), 1, from_string);
    vm.register_pure(
        "OS.Path.concat",
        &[],
        function(pair(string.clone(), string.clone()), string),
        1,
        concat,
    );
}

fn from_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let path = arg(vm, args, 0, "OS.Path.fromString")?
        .as_bytes()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "OS.Path.fromString", "expected string"))?;
    let (is_abs, rest) = match path.strip_prefix(b"/") {
        Some(rest) => (true, rest),
        None => (false, path),
    };
    vm.check_stop()?;
    let mut arcs = Vec::new();
    if !path.is_empty() {
        for arc in rest.split(|&byte| byte == b'/') {
            vm.check_stop()?;
            arcs.push(Value::bytes(arc.to_vec()));
        }
    }
    Ok(Value(Rc::new(ValueData::Record(BTreeMap::from([
        ("isAbs".to_owned(), Value::bool(is_abs)),
        ("vol".to_owned(), Value::bytes(Vec::new())),
        ("arcs".to_owned(), Value::list(arcs)),
    ])))))
}

fn concat(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [first, second] = fields(vm, arg(vm, args, 0, "OS.Path.concat")?, 2, "OS.Path.concat")?
    else {
        return Err(vm.error(MlErrorKind::Type, "OS.Path.concat", "expected pair"));
    };
    let first = first.as_bytes().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "OS.Path.concat", "expected first path string")
    })?;
    let second = second.as_bytes().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "OS.Path.concat", "expected second path string")
    })?;
    if second.starts_with(b"/") {
        return Err(vm.raise_basis(
            "OS.Path.Path",
            "OS.Path.concat",
            "second path is absolute".to_owned(),
        ));
    }
    if second.is_empty() {
        return Ok(Value::bytes(if first.len() > 1 && first.ends_with(b"/") {
            first[..first.len() - 1].to_vec()
        } else {
            first.to_vec()
        }));
    }
    let separator = usize::from(!first.is_empty() && !first.ends_with(b"/"));
    let mut result = Vec::with_capacity(first.len() + separator + second.len());
    result.extend_from_slice(first);
    if separator != 0 {
        result.push(b'/');
    }
    result.extend_from_slice(second);
    Ok(Value::bytes(result))
}
