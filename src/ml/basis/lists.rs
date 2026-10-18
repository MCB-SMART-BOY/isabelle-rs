//! Missing Poly/ML List and Option Basis operations.
use super::text::{list as make_list, option as make_option};
use super::{MlError, MlErrorKind, NativeFunction, Type, Value, ValueData, Vm};
use super::{
    arg, container, fields, function, option_argument as option_value, pair, size, typ, var,
};

const MAX_LIST_LEN: usize = isize::MAX as usize / std::mem::size_of::<Value>();

pub(super) fn install(vm: &mut Vm) {
    install_list(vm);
    install_option(vm);
}

fn install_list(vm: &mut Vm) {
    let item = var(1);
    let list = container("list", item.clone());
    let optional = container("option", item.clone());
    for (name, callback, output) in [
        ("last", list_last as NativeFunction, item.clone()),
        ("getItem", list_get_item, container("option", pair(item.clone(), list.clone()))),
    ] {
        vm.register_pure(
            &format!("List.{name}"),
            &[1],
            function(list.clone(), output),
            1,
            callback,
        );
    }
    vm.register_pure(
        "List.@",
        &[1],
        function(pair(list.clone(), list.clone()), list.clone()),
        1,
        super::list_append,
    );
    for (name, callback) in [("take", list_take as NativeFunction), ("drop", list_drop)] {
        vm.register_pure(
            &format!("List.{name}"),
            &[1],
            function(pair(list.clone(), typ("int")), list.clone()),
            1,
            callback,
        );
    }
    for (name, callback) in
        [("concat", list_concat as NativeFunction), ("revAppend", list_rev_append)]
    {
        let input = if name == "concat" {
            container("list", list.clone())
        } else {
            pair(list.clone(), list.clone())
        };
        vm.register_pure(&format!("List.{name}"), &[1], function(input, list.clone()), 1, callback);
    }
    vm.register_pure(
        "List.tabulate",
        &[1],
        function(pair(typ("int"), function(typ("int"), item.clone())), list.clone()),
        1,
        list_tabulate,
    );
    vm.register_pure(
        "List.mapPartial",
        &[1, 2],
        function(
            function(item.clone(), container("option", var(2))),
            function(list.clone(), container("list", var(2))),
        ),
        2,
        list_map_partial,
    );
    vm.register_pure(
        "List.find",
        &[1],
        function(function(item.clone(), typ("bool")), function(list.clone(), optional)),
        2,
        list_find,
    );
    for (name, callback, output) in [
        ("filter", list_filter as NativeFunction, list.clone()),
        ("partition", list_partition, pair(list.clone(), list.clone())),
    ] {
        vm.register_pure(
            &format!("List.{name}"),
            &[1],
            function(function(item.clone(), typ("bool")), function(list.clone(), output)),
            2,
            callback,
        );
    }
    vm.register_pure(
        "List.collate",
        &[1],
        function(
            function(pair(item.clone(), item), typ("order")),
            function(pair(list.clone(), list), typ("order")),
        ),
        2,
        list_collate,
    );
}

fn install_option(vm: &mut Vm) {
    let item = var(1);
    let optional = container("option", item.clone());
    vm.register_pure(
        "Option.join",
        &[1],
        function(container("option", optional.clone()), optional.clone()),
        1,
        option_join,
    );
    vm.register_pure(
        "Option.filter",
        &[1],
        function(function(item.clone(), typ("bool")), function(item.clone(), optional.clone())),
        2,
        option_filter,
    );
    vm.register_pure(
        "Option.app",
        &[1],
        function(function(item.clone(), typ("unit")), function(optional.clone(), typ("unit"))),
        2,
        option_app,
    );
    vm.register_pure(
        "Option.map",
        &[1, 2],
        function(
            function(item.clone(), var(2)),
            function(optional.clone(), container("option", var(2))),
        ),
        2,
        option_map,
    );
    vm.register_pure(
        "Option.mapPartial",
        &[1, 2],
        function(
            function(item.clone(), container("option", var(2))),
            function(optional, container("option", var(2))),
        ),
        2,
        option_map_partial,
    );
    for (name, callback, is_partial) in [
        ("compose", option_compose as NativeFunction, false),
        ("composePartial", option_compose_partial, true),
    ] {
        let output = container("option", var(2));
        let first_output = if is_partial { output.clone() } else { var(2) };
        let pair_type =
            pair(function(var(1), first_output), function(var(3), container("option", var(1))));
        vm.register_pure(
            &format!("Option.{name}"),
            &[1, 2, 3],
            function(pair_type, function(var(3), output)),
            2,
            callback,
        );
    }
}

fn list_items<'a>(vm: &Vm, value: &'a Value, operation: &str) -> Result<&'a [Value], MlError> {
    let ValueData::List(values) = &*value.0 else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected list"));
    };
    Ok(values)
}

fn invoke(
    vm: &mut Vm,
    callback: &Value,
    argument: &Value,
    callback_type: &Type,
) -> Result<Value, MlError> {
    let Type::Function(input, _) = callback_type else {
        return Err(vm.error(
            MlErrorKind::HostFailure,
            "native higher-order callback",
            "compiler-certified callback type is not a function",
        ));
    };
    vm.apply_with_type(callback, argument, input.as_ref().clone())
}

fn native_callback_type(vm: &Vm, index: usize, operation: &str) -> Result<Type, MlError> {
    vm.native_argument_type(index).ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, operation, "missing compiler-certified callback type")
    })
}

fn tuple_callback_type(
    vm: &Vm,
    argument_index: usize,
    field: &str,
    operation: &str,
) -> Result<Type, MlError> {
    let Type::Record(fields, false) = native_callback_type(vm, argument_index, operation)? else {
        return Err(vm.error(
            MlErrorKind::HostFailure,
            operation,
            "callback tuple type is not fixed",
        ));
    };
    fields.get(field).cloned().ok_or_else(|| {
        vm.error(
            MlErrorKind::HostFailure,
            operation,
            "callback tuple field has no compiler-certified type",
        )
    })
}

fn test_predicate(
    vm: &mut Vm,
    callback: &Value,
    value: &Value,
    callback_type: &Type,
    operation: &str,
) -> Result<bool, MlError> {
    invoke(vm, callback, value, callback_type)?
        .as_bool()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "predicate did not return bool"))
}

fn list_last(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    list_items(vm, arg(vm, args, 0, "List.last")?, "List.last")?
        .last()
        .cloned()
        .ok_or_else(|| vm.raise_basis("Empty", "List.last", "empty list".to_owned()))
}

fn list_get_item(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let values = list_items(vm, arg(vm, args, 0, "List.getItem")?, "List.getItem")?;
    let Some((head, tail)) = values.split_first() else {
        return Ok(make_option(vm, None));
    };
    let rest = make_list(vm, tail.to_vec());
    let pair = super::text::tuple(vm, vec![head.clone(), rest]);
    Ok(make_option(vm, Some(pair)))
}

fn list_slice(vm: &mut Vm, args: &[Value], take: bool, operation: &str) -> Result<Value, MlError> {
    let [source, requested] = fields(vm, arg(vm, args, 0, operation)?, 2, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected pair"));
    };
    let values = list_items(vm, source, operation)?;
    let count = requested
        .as_int()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected integer count"))?;
    let count =
        usize::try_from(count).ok().filter(|&count| count <= values.len()).ok_or_else(|| {
            vm.raise_basis(
                "Subscript",
                operation,
                format!("count {count}, length {}", values.len()),
            )
        })?;
    let selection = if take { &values[..count] } else { &values[count..] };
    Ok(make_list(vm, selection.to_vec()))
}
fn list_take(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    list_slice(vm, args, true, "List.take")
}
fn list_drop(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    list_slice(vm, args, false, "List.drop")
}

fn list_concat(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let outer = list_items(vm, arg(vm, args, 0, "List.concat")?, "List.concat")?;
    let mut result = Vec::new();
    for inner in outer {
        vm.check_stop()?;
        let values = list_items(vm, inner, "List.concat")?;
        let length =
            result.len().checked_add(values.len()).filter(|&n| n < MAX_LIST_LEN).ok_or_else(
                || vm.raise_basis("Size", "List.concat", "combined length overflow".to_owned()),
            )?;
        result.try_reserve(length - result.len()).map_err(|cause| {
            vm.raise_basis("Size", "List.concat", format!("combined length {length}: {cause}"))
        })?;
        result.extend_from_slice(values);
    }
    Ok(make_list(vm, result))
}

fn list_rev_append(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [source, suffix] = fields(vm, arg(vm, args, 0, "List.revAppend")?, 2, "List.revAppend")?
    else {
        return Err(vm.error(MlErrorKind::Type, "List.revAppend", "expected pair"));
    };
    let left = list_items(vm, source, "List.revAppend")?;
    let right = list_items(vm, suffix, "List.revAppend")?;
    let mut result = Vec::with_capacity(left.len() + right.len());
    for item in left.iter().rev() {
        vm.check_stop()?;
        result.push(item.clone());
    }
    result.extend_from_slice(right);
    Ok(make_list(vm, result))
}

fn list_tabulate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = tuple_callback_type(vm, 0, "2", "List.tabulate")?;
    let [count, callback] = fields(vm, arg(vm, args, 0, "List.tabulate")?, 2, "List.tabulate")?
    else {
        return Err(vm.error(MlErrorKind::Type, "List.tabulate", "expected pair"));
    };
    let count = size(vm, count, "List.tabulate")?;
    if count >= MAX_LIST_LEN {
        return Err(vm.raise_basis("Size", "List.tabulate", format!("size {count}")));
    }
    let mut result = Vec::new();
    result.try_reserve_exact(count).map_err(|cause| {
        vm.raise_basis("Size", "List.tabulate", format!("size {count}: {cause}"))
    })?;
    for position in 0..count {
        vm.check_stop()?;
        result.push(invoke(vm, callback, &Value::int(position as i64), &callback_type)?);
    }
    Ok(make_list(vm, result))
}

fn list_map_partial(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "List.mapPartial")?;
    let values = list_items(vm, arg(vm, args, 1, "List.mapPartial")?, "List.mapPartial")?;
    let mut result = Vec::with_capacity(values.len());
    for value in values {
        vm.check_stop()?;
        let answer = invoke(vm, &args[0], value, &callback_type)?;
        if let Some(item) = option_value(vm, &answer, "List.mapPartial")? {
            result.push(item.clone());
        }
    }
    Ok(make_list(vm, result))
}

fn list_find(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "List.find")?;
    let values = list_items(vm, arg(vm, args, 1, "List.find")?, "List.find")?;
    for value in values {
        vm.check_stop()?;
        if test_predicate(vm, &args[0], value, &callback_type, "List.find")? {
            return Ok(make_option(vm, Some(value.clone())));
        }
    }
    Ok(make_option(vm, None))
}

fn list_filter(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "List.filter")?;
    let values = list_items(vm, arg(vm, args, 1, "List.filter")?, "List.filter")?;
    let mut result = Vec::new();
    for value in values {
        vm.check_stop()?;
        if test_predicate(vm, &args[0], value, &callback_type, "List.filter")? {
            result.push(value.clone());
        }
    }
    Ok(make_list(vm, result))
}

fn list_partition(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "List.partition")?;
    let values = list_items(vm, arg(vm, args, 1, "List.partition")?, "List.partition")?;
    let (mut matching, mut other) = (Vec::new(), Vec::new());
    for value in values {
        vm.check_stop()?;
        if test_predicate(vm, &args[0], value, &callback_type, "List.partition")? {
            matching.push(value.clone());
        } else {
            other.push(value.clone());
        }
    }
    let matching = make_list(vm, matching);
    let other = make_list(vm, other);
    Ok(super::text::tuple(vm, vec![matching, other]))
}

fn list_collate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "List.collate")?;
    let [left, right] = fields(vm, arg(vm, args, 1, "List.collate")?, 2, "List.collate")? else {
        return Err(vm.error(MlErrorKind::Type, "List.collate", "expected pair"));
    };
    let left = list_items(vm, left, "List.collate")?;
    let right = list_items(vm, right, "List.collate")?;
    for (a, b) in left.iter().zip(right) {
        vm.check_stop()?;
        let input = super::text::tuple(vm, vec![a.clone(), b.clone()]);
        let answer = invoke(vm, &args[0], &input, &callback_type)?;
        let comparison = super::text::parse_order(vm, &answer, "List.collate")?;
        if comparison != std::cmp::Ordering::Equal {
            return super::text::ordering(vm, comparison);
        }
    }
    super::text::ordering(vm, left.len().cmp(&right.len()))
}

fn option_join(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let outer = arg(vm, args, 0, "Option.join")?;
    match option_value(vm, outer, "Option.join")? {
        Some(inner) => {
            option_value(vm, inner, "Option.join")?;
            Ok(inner.clone())
        },
        None => Ok(make_option(vm, None)),
    }
}

fn option_filter(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "Option.filter")?;
    let item = arg(vm, args, 1, "Option.filter")?;
    let answer = test_predicate(vm, &args[0], item, &callback_type, "Option.filter")?;
    Ok(make_option(vm, answer.then(|| item.clone())))
}

fn option_app(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "Option.app")?;
    if let Some(item) = option_value(vm, arg(vm, args, 1, "Option.app")?, "Option.app")? {
        invoke(vm, &args[0], item, &callback_type)?;
    }
    Ok(Value::unit())
}

fn option_map(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "Option.map")?;
    let value = option_value(vm, arg(vm, args, 1, "Option.map")?, "Option.map")?;
    let Some(item) = value else {
        return Ok(make_option(vm, None));
    };
    let mapped = invoke(vm, &args[0], item, &callback_type)?;
    Ok(make_option(vm, Some(mapped)))
}

fn option_map_partial(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let callback_type = native_callback_type(vm, 0, "Option.mapPartial")?;
    let value = option_value(vm, arg(vm, args, 1, "Option.mapPartial")?, "Option.mapPartial")?;
    let Some(item) = value else {
        return Ok(make_option(vm, None));
    };
    let answer = invoke(vm, &args[0], item, &callback_type)?;
    option_value(vm, &answer, "Option.mapPartial")?;
    Ok(answer)
}

fn compose_option(
    vm: &mut Vm,
    args: &[Value],
    is_partial: bool,
    operation: &str,
) -> Result<Value, MlError> {
    let first_type = tuple_callback_type(vm, 0, "1", operation)?;
    let second_type = tuple_callback_type(vm, 0, "2", operation)?;
    let [first, second] = fields(vm, arg(vm, args, 0, operation)?, 2, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected pair of functions"));
    };
    let intermediate = invoke(vm, second, arg(vm, args, 1, operation)?, &second_type)?;
    let Some(item) = option_value(vm, &intermediate, operation)? else {
        return Ok(make_option(vm, None));
    };
    let answer = invoke(vm, first, item, &first_type)?;
    if is_partial {
        option_value(vm, &answer, operation)?;
        Ok(answer)
    } else {
        Ok(make_option(vm, Some(answer)))
    }
}
fn option_compose(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    compose_option(vm, args, false, "Option.compose")
}
fn option_compose_partial(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    compose_option(vm, args, true, "Option.composePartial")
}
