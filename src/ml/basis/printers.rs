//! VM-local, type-directed Poly/ML pretty-printer registry.
use super::{
    MlError, MlErrorKind, Type, TypeScheme, Value, ValueData, Vm, function, pair, typ, var,
};
use crate::ml::value::NativeFunctionId;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

const MAX_PRETTY_NODES: usize = 100_000;
const MAX_PRETTY_BYTES: usize = 1_048_576;
const MAX_PRETTY_DEPTH: usize = 256;

pub(in crate::ml) struct PrinterBudget {
    remaining_nodes: usize,
    remaining_bytes: usize,
    format_depth: usize,
    active_values: BTreeSet<usize>,
}

impl Default for PrinterBudget {
    fn default() -> Self {
        Self {
            remaining_nodes: MAX_PRETTY_NODES,
            remaining_bytes: MAX_PRETTY_BYTES,
            format_depth: 0,
            active_values: BTreeSet::new(),
        }
    }
}

#[derive(Clone)]
pub(in crate::ml) enum TypeDirectedNative {
    AddPrettyPrinter,
    PrettyRepresentation,
    ParameterPrinter(Type),
}

#[derive(Clone)]
pub(in crate::ml) struct PrinterRegistration {
    pub(super) target: Type,
    callback: Value,
    callback_type: Type,
}

#[derive(Clone, Default)]
pub(in crate::ml) struct PrettyConstructors {
    stamps: BTreeMap<&'static str, u128>,
}

impl PrettyConstructors {
    fn insert(&mut self, name: &'static str, stamp: u128) {
        self.stamps.insert(name, stamp);
    }

    fn stamp(&self, name: &'static str) -> Option<u128> {
        self.stamps.get(name).copied()
    }

    pub(super) fn recognizes(&self, name: &str, stamp: u128) -> bool {
        self.stamps.get(name).is_some_and(|expected| *expected == stamp)
    }
}

pub(super) fn install(vm: &mut Vm) {
    install_pretty_types(vm);
    let pretty = typ("PolyML.pretty");
    let callback = function(typ("int"), function(var(2), function(var(1), pretty.clone())));
    register_type_directed(
        vm,
        "PolyML.addPrettyPrinter",
        TypeScheme::polymorphic(vec![1, 2], function(callback, typ("unit"))),
        TypeDirectedNative::AddPrettyPrinter,
    );
    register_type_directed(
        vm,
        "PolyML.prettyRepresentation",
        TypeScheme::polymorphic(vec![1], function(pair(var(1), typ("int")), pretty)),
        TypeDirectedNative::PrettyRepresentation,
    );
}

fn install_pretty_types(vm: &mut Vm) {
    // VM construction installs this module exactly once after a fresh TypeEnvironment.
    vm.register_host_type("PolyML.context", 0, false).expect("fresh pretty context type");
    vm.register_host_type("PolyML.pretty", 0, false).expect("fresh pretty type");
    let context = typ("PolyML.context");
    let pretty = typ("PolyML.pretty");
    let pair_of_string = pair(typ("string"), typ("string"));
    let entries = [
        ("PolyML.ContextLocation", Some(typ("PolyML.location")), context.clone()),
        ("PolyML.ContextProperty", Some(pair_of_string), context.clone()),
        (
            "PolyML.PrettyBlock",
            Some(Type::Record(
                BTreeMap::from([
                    ("1".to_owned(), typ("int")),
                    ("2".to_owned(), typ("bool")),
                    ("3".to_owned(), super::container("list", context)),
                    ("4".to_owned(), super::container("list", pretty.clone())),
                ]),
                false,
            )),
            pretty.clone(),
        ),
        ("PolyML.PrettyBreak", Some(pair(typ("int"), typ("int"))), pretty.clone()),
        ("PolyML.PrettyLineBreak", None, pretty.clone()),
        ("PolyML.PrettyString", Some(typ("string")), pretty.clone()),
        ("PolyML.PrettyStringWithWidth", Some(pair(typ("string"), typ("int"))), pretty.clone()),
    ];
    for (name, argument, result) in entries {
        let stamp = vm.fresh_identity();
        vm.pretty_constructors.insert(name, stamp);
        let is_constructor = argument.is_some();
        let signature = if let Some(input) = argument { function(input, result) } else { result };
        let value = if is_constructor {
            Value(Rc::new(ValueData::ConstructorFunction { stamp, name: name.to_owned() }))
        } else {
            Value(Rc::new(ValueData::Constructor { stamp, name: name.to_owned(), argument: None }))
        };
        vm.register_value(name, TypeScheme::mono(signature), value);
    }
    let output = function(typ("string"), typ("unit"));
    vm.register_pure(
        "PolyML.prettyPrint",
        &[],
        function(pair(output, typ("int")), function(pretty, typ("unit"))),
        2,
        pretty_print,
    );
}

fn register_type_directed(
    vm: &mut Vm,
    name: &str,
    scheme: TypeScheme,
    intrinsic: TypeDirectedNative,
) -> NativeFunctionId {
    let id = NativeFunctionId::new(vm.runtime_id, vm.generation, vm.native_functions.len());
    vm.native_functions.push((invalid_direct_dispatch, 1));
    vm.type_directed_natives.insert(id, intrinsic);
    vm.register_value(name, scheme, Value::native(id));
    id
}

fn invalid_direct_dispatch(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    Err(vm.error(
        MlErrorKind::HostFailure,
        "type-directed primitive",
        "type-directed dispatch bypassed compiler evidence",
    ))
}

pub(super) fn invoke(
    vm: &mut Vm,
    intrinsic: TypeDirectedNative,
    args: &[Value],
    certified_argument: &Type,
) -> Result<Value, MlError> {
    match intrinsic {
        TypeDirectedNative::AddPrettyPrinter => add_pretty_printer(vm, args, certified_argument),
        TypeDirectedNative::PrettyRepresentation => {
            pretty_representation(vm, args, certified_argument)
        },
        TypeDirectedNative::ParameterPrinter(parameter) => {
            parameter_printer(vm, args, certified_argument, &parameter)
        },
    }
}

fn registered_callback_weak_variables(vm: &Vm, callback: &Value) -> Option<BTreeSet<u64>> {
    match &*callback.0 {
        ValueData::Closure { runtime, .. } | ValueData::CurriedClosure { runtime, .. }
            if *runtime == vm.runtime_id =>
        {
            vm.closure_weak_variables.get(&(Rc::as_ptr(&callback.0) as usize)).cloned()
        },
        _ => None,
    }
}

fn add_pretty_printer(vm: &mut Vm, args: &[Value], callback_type: &Type) -> Result<Value, MlError> {
    let callback = args.first().ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, "PolyML.addPrettyPrinter", "missing callback argument")
    })?;
    let weak_variables = registered_callback_weak_variables(vm, callback);
    let (identity, target) =
        validate_registration_type(vm, callback_type, weak_variables.as_ref())?;
    let registration = PrinterRegistration {
        target,
        callback: callback.clone(),
        callback_type: callback_type.clone(),
    };
    if let Some(scope) = vm.module_printer_scopes.last_mut() {
        scope.insert(identity.clone());
    }
    vm.printer_registry.insert(identity, registration);
    Ok(Value::unit())
}

pub(in crate::ml) fn preflight(
    vm: &Vm,
    intrinsic: &TypeDirectedNative,
    certified_argument: &Type,
    weak_variables: &BTreeSet<u64>,
) -> Result<(), MlError> {
    if matches!(intrinsic, TypeDirectedNative::AddPrettyPrinter) {
        validate_registration_type(vm, certified_argument, Some(weak_variables))?;
    }
    Ok(())
}

fn validate_registration_type(
    vm: &Vm,
    callback_type: &Type,
    weak_variables: Option<&BTreeSet<u64>>,
) -> Result<(String, Type), MlError> {
    let (_, rest) = as_function(callback_type).ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.addPrettyPrinter", "printer must accept a depth")
    })?;
    let (argument_printers, rest) = as_function(rest).ok_or_else(|| {
        vm.error(
            MlErrorKind::Type,
            "PolyML.addPrettyPrinter",
            "printer must accept argument printers",
        )
    })?;
    let (target, output) = as_function(rest).ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.addPrettyPrinter", "printer must accept a target value")
    })?;
    require_pretty_type(vm, output, "PolyML.addPrettyPrinter")?;
    let Type::Constructor(identity, parameters) = target else {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML.addPrettyPrinter",
            "printer target must resolve to a concrete type constructor",
        ));
    };
    if !parameters.is_empty() && weak_variables.is_none() {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML.addPrettyPrinter",
            "generic printer callback has no compiler-certified generalization evidence",
        ));
    }
    let weak_variables = weak_variables.into_iter().flatten().copied().collect::<BTreeSet<_>>();
    let mut variables = BTreeSet::new();
    for parameter in parameters {
        let Type::Variable(id) = parameter else {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.addPrettyPrinter",
                "printer target parameters must be generic type variables",
            ));
        };
        if weak_variables.contains(id) {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.addPrettyPrinter",
                "printer target parameter is a weak type variable",
            ));
        }
        if !variables.insert(*id) {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.addPrettyPrinter",
                "printer target parameters must be distinct",
            ));
        }
    }
    validate_argument_printers(vm, argument_printers, parameters)?;
    Ok((identity.clone(), target.clone()))
}

fn validate_argument_printers(
    vm: &Vm,
    argument_printers: &Type,
    parameters: &[Type],
) -> Result<(), MlError> {
    if parameters.is_empty() {
        if argument_printers == &typ("unit") || matches!(argument_printers, Type::Variable(_)) {
            return Ok(());
        }
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML.addPrettyPrinter",
            "monomorphic printer argument must be unit",
        ));
    }
    let supplied = if parameters.len() == 1 {
        vec![argument_printers]
    } else {
        let Type::Record(fields, false) = argument_printers else {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.addPrettyPrinter",
                "printer arguments must be a fixed tuple",
            ));
        };
        if fields.len() != parameters.len() {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.addPrettyPrinter",
                "printer argument tuple has the wrong arity",
            ));
        }
        (1..=parameters.len())
            .map(|index| fields.get(&index.to_string()))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                vm.error(
                    MlErrorKind::Type,
                    "PolyML.addPrettyPrinter",
                    "printer argument tuple has the wrong arity",
                )
            })?
    };
    for (printer, parameter) in supplied.into_iter().zip(parameters) {
        let (input, output) = as_function(printer).ok_or_else(|| {
            vm.error(
                MlErrorKind::Type,
                "PolyML.addPrettyPrinter",
                "type argument printer is not a function",
            )
        })?;
        let expected = pair(parameter.clone(), typ("int"));
        if input != &expected {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.addPrettyPrinter",
                "type argument printer has the wrong input type",
            ));
        }
        require_pretty_type(vm, output, "PolyML.addPrettyPrinter")?;
    }
    Ok(())
}

fn pretty_representation(vm: &mut Vm, args: &[Value], input_type: &Type) -> Result<Value, MlError> {
    let value_and_depth = args
        .first()
        .and_then(Value::as_tuple)
        .filter(|parts| parts.len() == 2)
        .ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.prettyRepresentation", "expected value and depth")
    })?;
    let depth = value_and_depth[1].as_int().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.prettyRepresentation", "depth is not an integer")
    })?;
    let value_type = pair_first(input_type).ok_or_else(|| {
        vm.error(
            MlErrorKind::HostFailure,
            "PolyML.prettyRepresentation",
            "compiler evidence is not a pair type",
        )
    })?;
    format_typed(vm, &value_and_depth[0], value_type, depth)
}

fn parameter_printer(
    vm: &mut Vm,
    args: &[Value],
    input_type: &Type,
    parameter_type: &Type,
) -> Result<Value, MlError> {
    let value_and_depth =
        args.first().and_then(Value::as_tuple).filter(|parts| parts.len() == 2).ok_or_else(
            || vm.error(MlErrorKind::Type, "PolyML argument printer", "expected value and depth"),
        )?;
    let actual_type = pair_first(input_type).ok_or_else(|| {
        vm.error(
            MlErrorKind::HostFailure,
            "PolyML argument printer",
            "compiler evidence is not a pair type",
        )
    })?;
    if actual_type != parameter_type {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML argument printer",
            "argument does not have the certified parameter type",
        ));
    }
    let depth = value_and_depth[1].as_int().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML argument printer", "depth is not an integer")
    })?;
    format_typed(vm, &value_and_depth[0], parameter_type, depth)
}

fn with_printer_budget<T>(
    vm: &mut Vm,
    run: impl FnOnce(&mut Vm) -> Result<T, MlError>,
) -> Result<T, MlError> {
    if vm.printer_budget.is_some() {
        return run(vm);
    }
    vm.printer_budget = Some(PrinterBudget::default());
    let result = run(vm);
    vm.printer_budget = None;
    result
}

fn consume_pretty_node(vm: &mut Vm, operation: &str) -> Result<(), MlError> {
    vm.check_stop()?;
    let Some(remaining) = vm.printer_budget.as_ref().map(|budget| budget.remaining_nodes) else {
        return Err(vm.error(MlErrorKind::HostFailure, operation, "missing pretty-printer budget"));
    };
    if remaining == 0 {
        return Err(vm.raise_builtin("Size"));
    }
    if let Some(budget) = vm.printer_budget.as_mut() {
        budget.remaining_nodes -= 1;
    }
    Ok(())
}

fn reserve_pretty_bytes(vm: &mut Vm, bytes: usize, operation: &str) -> Result<(), MlError> {
    let Some(remaining) = vm.printer_budget.as_ref().map(|budget| budget.remaining_bytes) else {
        return Err(vm.error(MlErrorKind::HostFailure, operation, "missing pretty-printer budget"));
    };
    if bytes > remaining {
        return Err(vm.raise_builtin("Size"));
    }
    if let Some(budget) = vm.printer_budget.as_mut() {
        budget.remaining_bytes -= bytes;
    }
    Ok(())
}

fn ensure_pretty_items(vm: &mut Vm, count: usize, operation: &str) -> Result<(), MlError> {
    vm.check_stop()?;
    let remaining = vm.printer_budget.as_ref().map_or(0, |budget| budget.remaining_nodes);
    if count > remaining {
        return Err(vm.raise_builtin("Size"));
    }
    if count > MAX_PRETTY_NODES {
        return Err(vm.error(MlErrorKind::Type, operation, "invalid pretty collection size"));
    }
    Ok(())
}

fn ensure_pretty_bytes(vm: &mut Vm, bytes: usize) -> Result<(), MlError> {
    let remaining = vm.printer_budget.as_ref().map_or(0, |budget| budget.remaining_bytes);
    if bytes > remaining {
        return Err(vm.raise_builtin("Size"));
    }
    Ok(())
}

fn enter_format_value(vm: &mut Vm, value: &Value) -> Result<bool, MlError> {
    consume_pretty_node(vm, "PolyML.prettyRepresentation")?;
    let pointer = Rc::as_ptr(&value.0) as usize;
    let Some(depth) = vm.printer_budget.as_ref().map(|budget| budget.format_depth) else {
        return Err(vm.error(
            MlErrorKind::HostFailure,
            "PolyML.prettyRepresentation",
            "missing pretty-printer budget",
        ));
    };
    if depth >= MAX_PRETTY_DEPTH {
        return Err(vm.raise_builtin("Size"));
    }
    let Some(budget) = vm.printer_budget.as_mut() else {
        return Err(vm.error(
            MlErrorKind::HostFailure,
            "PolyML.prettyRepresentation",
            "missing pretty-printer budget",
        ));
    };
    budget.format_depth += 1;
    Ok(budget.active_values.insert(pointer))
}

fn leave_format_value(vm: &mut Vm, value: &Value, was_inserted: bool) {
    if let Some(budget) = vm.printer_budget.as_mut() {
        budget.format_depth -= 1;
        if was_inserted {
            budget.active_values.remove(&(Rc::as_ptr(&value.0) as usize));
        }
    }
}

fn format_typed(vm: &mut Vm, value: &Value, typ: &Type, depth: i64) -> Result<Value, MlError> {
    with_printer_budget(vm, |vm| format_typed_inner(vm, value, typ, depth))
}

fn format_typed_inner(
    vm: &mut Vm,
    value: &Value,
    typ: &Type,
    depth: i64,
) -> Result<Value, MlError> {
    let is_fresh = enter_format_value(vm, value)?;
    if !is_fresh {
        leave_format_value(vm, value, false);
        return pretty_string(vm, "<cycle>");
    }
    let result = (|| {
        if depth <= 0 {
            return pretty_string(vm, "...");
        }
        if matches!(typ, Type::Variable(_)) {
            return pretty_string(vm, "<opaque>");
        }
        if let Type::Constructor(identity, arguments) = typ {
            if let Some((dispatch_identity, registration)) = find_registered_printer(vm, identity)?
            {
                return invoke_registered_printer(
                    vm,
                    value,
                    arguments,
                    depth,
                    &dispatch_identity,
                    registration,
                );
            }
            if vm.opaque_type_identities.contains(identity) {
                return pretty_string(vm, "<opaque>");
            }
        }
        default_pretty(vm, value, typ, depth)
    })();
    leave_format_value(vm, value, true);
    result
}

fn invoke_registered_printer(
    vm: &mut Vm,
    value: &Value,
    arguments: &[Type],
    depth: i64,
    identity: &str,
    registration: PrinterRegistration,
) -> Result<Value, MlError> {
    let dispatch_type = Type::Constructor(identity.to_owned(), arguments.to_vec());
    let substitutions = match_types(vm, &registration.target, &dispatch_type)?;
    let parameter_printers = make_parameter_printers(vm, arguments)?;
    vm.with_type_substitutions(substitutions.clone(), |vm| {
        let callback_type = registration.callback_type.substitute(&substitutions);
        let Type::Function(depth_type, second) = callback_type else {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "PolyML.addPrettyPrinter",
                "missing callback depth type",
            ));
        };
        let Type::Function(parameter_type, _) = *second else {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "PolyML.addPrettyPrinter",
                "missing callback parameter type",
            ));
        };
        let callback =
            vm.apply_with_type(&registration.callback, &Value::int(depth), *depth_type)?;
        let callback = vm.apply_with_type(&callback, &parameter_printers, *parameter_type)?;
        let pretty = vm.apply_with_type(&callback, value, dispatch_type)?;
        validate_pretty(vm, &pretty)?;
        Ok(pretty)
    })
}

fn find_registered_printer(
    vm: &Vm,
    identity: &str,
) -> Result<Option<(String, PrinterRegistration)>, MlError> {
    if let Some(registration) = vm.printer_registry.get(identity) {
        return Ok(Some((identity.to_owned(), registration.clone())));
    }
    if let Some(snapshot) = resolve_sealed_printer(vm, identity)? {
        return Ok(Some(snapshot));
    }
    if vm.opaque_type_identities.contains(identity) {
        return Ok(None);
    }
    let resolved = resolve_printer_identity(vm, identity)?;
    Ok(resolved.and_then(|name| {
        vm.printer_registry.get(&name).map(|registration| (name, registration.clone()))
    }))
}

fn resolve_sealed_printer(
    vm: &Vm,
    identity: &str,
) -> Result<Option<(String, PrinterRegistration)>, MlError> {
    let mut current = identity;
    let mut visited = BTreeSet::new();
    loop {
        if let Some(snapshot) = vm.sealed_printers.get(current) {
            return Ok(Some(snapshot.clone()));
        }
        if !visited.insert(current) {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "PolyML.prettyRepresentation",
                "cyclic generative printer identity mapping",
            ));
        }
        let Some(source) = vm.printer_aliases.get(current) else { return Ok(None) };
        current = source;
    }
}

pub(in crate::ml) fn freeze_sealed_printer(
    vm: &mut Vm,
    from: &str,
    to: &str,
) -> Result<(), MlError> {
    let registered = vm
        .printer_registry
        .get(from)
        .filter(|_| vm.module_printer_scopes.last().is_some_and(|scope| scope.contains(from)))
        .map(|registration| (from.to_owned(), registration.clone()));
    let inherited = resolve_sealed_printer(vm, from)?;
    let fresh = if registered.is_none() && inherited.is_none() {
        resolve_printer_identity(vm, from)?.and_then(|name| {
            vm.module_printer_scopes
                .last()
                .is_some_and(|scope| scope.contains(&name))
                .then(|| {
                    vm.printer_registry.get(&name).map(|registration| (name, registration.clone()))
                })
                .flatten()
        })
    } else {
        None
    };
    if let Some(snapshot) = registered.or(inherited).or(fresh) {
        vm.sealed_printers.insert(to.to_owned(), snapshot);
    }
    Ok(())
}

fn resolve_printer_identity(vm: &Vm, identity: &str) -> Result<Option<String>, MlError> {
    if vm.printer_registry.contains_key(identity) {
        return Ok(Some(identity.to_owned()));
    }
    let mut current = identity;
    let mut visited = BTreeSet::new();
    while let Some(source) = vm.printer_aliases.get(current) {
        if !visited.insert(current.to_owned()) {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "PolyML.prettyRepresentation",
                "cyclic generative printer identity mapping",
            ));
        }
        if vm.printer_registry.contains_key(source) {
            return Ok(Some(source.clone()));
        }
        current = source;
    }
    Ok(None)
}

fn make_parameter_printers(vm: &mut Vm, parameters: &[Type]) -> Result<Value, MlError> {
    if parameters.is_empty() {
        return Ok(Value::unit());
    }
    let mut printers = Vec::with_capacity(parameters.len());
    for parameter in parameters {
        let id = register_parameter_printer(vm, parameter.clone());
        printers.push(Value::native(id));
    }
    if printers.len() == 1 {
        Ok(printers.remove(0))
    } else {
        Ok(vm.track_value(Value::tuple(printers)))
    }
}

fn register_parameter_printer(vm: &mut Vm, parameter: Type) -> NativeFunctionId {
    if let Some(id) = vm.parameter_printer_ids.get(&parameter) {
        return *id;
    }
    let id = NativeFunctionId::new(vm.runtime_id, vm.generation, vm.native_functions.len());
    vm.native_functions.push((invalid_direct_dispatch, 1));
    vm.type_directed_natives.insert(id, TypeDirectedNative::ParameterPrinter(parameter.clone()));
    vm.parameter_printer_ids.insert(parameter, id);
    id
}

fn match_types(vm: &Vm, template: &Type, actual: &Type) -> Result<BTreeMap<u64, Type>, MlError> {
    fn collect(template: &Type, actual: &Type, output: &mut BTreeMap<u64, Type>) -> bool {
        match (template, actual) {
            (Type::Variable(id), actual) => {
                if let Some(previous) = output.get(id) {
                    previous == actual
                } else {
                    output.insert(*id, actual.clone());
                    true
                }
            },
            (Type::Constructor(a, aa), Type::Constructor(b, ba))
                if a == b && aa.len() == ba.len() =>
            {
                aa.iter().zip(ba).all(|(a, b)| collect(a, b, output))
            },
            (Type::Function(a, b), Type::Function(c, d)) => {
                collect(a, c, output) && collect(b, d, output)
            },
            (Type::Record(a, open_a), Type::Record(b, open_b))
                if open_a == open_b && a.len() == b.len() =>
            {
                a.iter().all(|(name, value)| {
                    b.get(name).is_some_and(|other| collect(value, other, output))
                })
            },
            _ => template == actual,
        }
    }
    let mut substitutions = BTreeMap::new();
    if collect(template, actual, &mut substitutions) {
        Ok(substitutions)
    } else {
        Err(vm.error(
            MlErrorKind::HostFailure,
            "PolyML.prettyRepresentation",
            "registered printer type does not match dispatch type",
        ))
    }
}

fn default_pretty(vm: &mut Vm, value: &Value, typ: &Type, depth: i64) -> Result<Value, MlError> {
    match &*value.0 {
        ValueData::Unit => pretty_string(vm, "()"),
        ValueData::Int(number) => pretty_string(vm, number.to_string()),
        ValueData::Real(number) => pretty_string(vm, number.to_string()),
        ValueData::Word(number) => pretty_string(vm, format!("0wx{number:x}")),
        ValueData::Word32(number) => pretty_string(vm, format!("0wx{number:x}")),
        ValueData::Bool(value) => pretty_string(vm, value.to_string()),
        ValueData::Text(bytes) => {
            ensure_pretty_bytes(vm, bytes.len().saturating_add(2))?;
            pretty_string(vm, format!("\"{}\"", String::from_utf8_lossy(bytes)))
        },
        ValueData::Character(value) => pretty_string(vm, format!("#\"{}\"", char::from(*value))),
        ValueData::Tuple(values) => format_record_values(vm, values, typ, depth),
        ValueData::Record(fields) => format_named_record(vm, fields, typ, depth),
        ValueData::List(values) => {
            format_container(vm, values, typ, depth, "list", ("[", ", ", "]"))
        },
        ValueData::Vector(values) => {
            format_container(vm, values, typ, depth, "vector", ("#[", ", ", "]"))
        },
        ValueData::Array(values) => {
            let snapshot = {
                let borrowed = values.borrow();
                ensure_pretty_items(vm, borrowed.len(), "PolyML.prettyRepresentation")?;
                borrowed.to_vec()
            };
            format_container(vm, &snapshot, typ, depth, "array", ("#[|", ", ", "|]"))
        },
        ValueData::Constructor { stamp, name, argument } => {
            format_constructor(vm, *stamp, name, argument.as_ref(), typ, depth)
        },
        ValueData::Exception { name, argument, .. } => {
            format_constructor(vm, 0, name, argument.as_ref(), typ, depth)
        },
        ValueData::ExceptionFunction { name, .. } => {
            pretty_string(vm, format!("<exception {name}>"))
        },
        ValueData::Reference(value) => {
            let Some(item_type) = trusted_container_parameter(typ, "ref").cloned() else {
                return pretty_string(vm, "<opaque>");
            };
            let value = value.borrow().clone();
            let child = format_typed(vm, &value, &item_type, depth - 1)?;
            pretty_sequence(vm, "ref ", "", "", vec![child])
        },
        ValueData::WeakReference(_) => pretty_string(vm, "<weak>"),
        ValueData::Closure { .. }
        | ValueData::CurriedClosure { .. }
        | ValueData::Native(_)
        | ValueData::NativePartial { .. }
        | ValueData::HostFunction { .. }
        | ValueData::ConstructorFunction { .. } => pretty_string(vm, "fn"),
        ValueData::Host { .. } => pretty_string(vm, "<opaque>"),
    }
}

fn format_container(
    vm: &mut Vm,
    values: &[Value],
    typ: &Type,
    depth: i64,
    identity: &str,
    delimiters: (&str, &str, &str),
) -> Result<Value, MlError> {
    let Some(item_type) = trusted_container_parameter(typ, identity).cloned() else {
        return pretty_string(vm, "<opaque>");
    };
    ensure_pretty_items(vm, values.len(), "PolyML.prettyRepresentation")?;
    let mut children = Vec::with_capacity(values.len());
    for value in values {
        children.push(format_typed(vm, value, &item_type, depth - 1)?);
    }
    pretty_sequence(vm, delimiters.0, delimiters.1, delimiters.2, children)
}

fn trusted_container_parameter<'a>(typ: &'a Type, identity: &str) -> Option<&'a Type> {
    match typ {
        Type::Constructor(actual, arguments) if actual == identity && arguments.len() == 1 => {
            arguments.first()
        },
        _ => None,
    }
}

fn format_record_values(
    vm: &mut Vm,
    values: &[Value],
    typ: &Type,
    depth: i64,
) -> Result<Value, MlError> {
    let Type::Record(types, false) = typ else {
        return pretty_string(vm, "<opaque>");
    };
    if types.len() != values.len() {
        return pretty_string(vm, "<opaque>");
    }
    ensure_pretty_items(vm, values.len(), "PolyML.prettyRepresentation")?;
    let mut children = Vec::with_capacity(values.len());
    for (index, value) in values.iter().enumerate() {
        let Some(field_type) = types.get(&(index + 1).to_string()) else {
            return pretty_string(vm, "<opaque>");
        };
        children.push(format_typed(vm, value, field_type, depth - 1)?);
    }
    pretty_sequence(vm, "(", ", ", ")", children)
}

fn format_named_record(
    vm: &mut Vm,
    fields: &BTreeMap<String, Value>,
    typ: &Type,
    depth: i64,
) -> Result<Value, MlError> {
    let Type::Record(types, false) = typ else {
        return pretty_string(vm, "<opaque>");
    };
    if types.len() != fields.len() {
        return pretty_string(vm, "<opaque>");
    }
    ensure_pretty_items(vm, fields.len(), "PolyML.prettyRepresentation")?;
    let mut children = Vec::with_capacity(fields.len());
    for (name, value) in fields {
        let Some(field_type) = types.get(name) else {
            return pretty_string(vm, "<opaque>");
        };
        let value = format_typed(vm, value, field_type, depth - 1)?;
        children.push(pretty_sequence(vm, &format!("{name}="), "", "", vec![value])?);
    }
    pretty_sequence(vm, "{", ", ", "}", children)
}

fn format_constructor(
    vm: &mut Vm,
    stamp: u128,
    name: &str,
    argument: Option<&Value>,
    target_type: &Type,
    depth: i64,
) -> Result<Value, MlError> {
    let Some(argument) = argument else {
        return pretty_string(vm, name);
    };
    let Some(argument_type) = constructor_argument_type(vm, stamp, target_type)? else {
        let name = pretty_string(vm, name)?;
        let hidden = pretty_string(vm, " <opaque>")?;
        return pretty_sequence(vm, "", "", "", vec![name, hidden]);
    };
    let child = format_typed(vm, argument, &argument_type, depth - 1)?;
    pretty_sequence(vm, &format!("{name} "), "", "", vec![child])
}

fn constructor_argument_type(
    vm: &Vm,
    stamp: u128,
    target_type: &Type,
) -> Result<Option<Type>, MlError> {
    let Some(scheme) = vm.constructor_types.get(&stamp) else {
        return Ok(None);
    };
    let Type::Function(input, result) = scheme.body() else {
        return Ok(None);
    };
    let runtime_type = normalize_outer_constructor(vm, target_type)?;
    let substitutions = match_types(vm, result.as_ref(), &runtime_type)?;
    Ok(Some(input.substitute(&substitutions)))
}

fn normalize_outer_constructor(vm: &Vm, typ: &Type) -> Result<Type, MlError> {
    let mut runtime_type = typ.clone();
    let Type::Constructor(identity, _) = &mut runtime_type else {
        return Ok(runtime_type);
    };
    let mut active = BTreeSet::new();
    while let Some(internal) = vm.printer_aliases.get(identity).cloned() {
        if !active.insert(identity.clone()) {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "PolyML.prettyRepresentation",
                "cyclic compiler type identity mapping",
            ));
        }
        *identity = internal;
    }
    Ok(runtime_type)
}

fn pretty_sequence(
    vm: &mut Vm,
    open: &str,
    separator: &str,
    close: &str,
    children: Vec<Value>,
) -> Result<Value, MlError> {
    ensure_pretty_items(vm, children.len(), "PolyML.prettyRepresentation")?;
    let mut body = Vec::with_capacity(children.len().saturating_mul(2).saturating_add(2));
    if !open.is_empty() {
        body.push(pretty_string(vm, open)?);
    }
    for (index, child) in children.into_iter().enumerate() {
        if index > 0 && !separator.is_empty() {
            body.push(pretty_string(vm, separator)?);
        }
        body.push(child);
    }
    if !close.is_empty() {
        body.push(pretty_string(vm, close)?);
    }
    pretty_block(vm, body)
}

fn pretty_block(vm: &mut Vm, body: Vec<Value>) -> Result<Value, MlError> {
    let stamp = vm.pretty_constructors.stamp("PolyML.PrettyBlock").ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, "pretty", "PrettyBlock constructor is not installed")
    })?;
    let payload = Value::tuple(vec![
        Value::int(0),
        Value::bool(false),
        Value::list(Vec::new()),
        Value::list(body),
    ]);
    Ok(vm.track_value(Value(Rc::new(ValueData::Constructor {
        stamp,
        name: "PolyML.PrettyBlock".to_owned(),
        argument: Some(payload),
    }))))
}

fn pretty_string(vm: &mut Vm, text: impl Into<String>) -> Result<Value, MlError> {
    let text = text.into();
    reserve_pretty_bytes(vm, text.len(), "PolyML.prettyRepresentation")?;
    let stamp = vm.pretty_constructors.stamp("PolyML.PrettyString").ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, "pretty", "PrettyString constructor is not installed")
    })?;
    Ok(vm.track_value(Value(Rc::new(ValueData::Constructor {
        stamp,
        name: "PolyML.PrettyString".to_owned(),
        argument: Some(Value::text(text)),
    }))))
}

fn validate_pretty(vm: &mut Vm, value: &Value) -> Result<(), MlError> {
    let mut stack = vec![(value.clone(), 0_usize, false)];
    let mut active = BTreeSet::new();
    let mut validated = BTreeSet::new();
    while let Some((value, depth, is_exit)) = stack.pop() {
        vm.check_stop()?;
        let pointer = Rc::as_ptr(&value.0) as usize;
        if is_exit {
            active.remove(&pointer);
            validated.insert(pointer);
            continue;
        }
        consume_pretty_node(vm, "PolyML pretty printer")?;
        if validated.contains(&pointer) {
            continue;
        }
        if depth >= MAX_PRETTY_DEPTH {
            return Err(vm.raise_builtin("Size"));
        }
        if !active.insert(pointer) {
            return Err(vm.error(MlErrorKind::Type, "PolyML pretty printer", "cyclic pretty tree"));
        }
        let children = validate_pretty_node(vm, &value)?;
        stack.push((value, depth, true));
        stack.extend(children.into_iter().rev().map(|child| (child, depth + 1, false)));
    }
    Ok(())
}

fn validate_pretty_node(vm: &mut Vm, value: &Value) -> Result<Vec<Value>, MlError> {
    let ValueData::Constructor { name, stamp, argument } = &*value.0 else {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML pretty printer",
            "callback did not return PolyML.pretty",
        ));
    };
    if !vm.pretty_constructors.recognizes(name, *stamp) {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML pretty printer",
            "foreign pretty constructor identity",
        ));
    }
    match (name.as_str(), argument) {
        ("PolyML.PrettyString", Some(value)) => {
            let text = value.as_text().ok_or_else(|| {
                vm.error(MlErrorKind::Type, "PolyML pretty printer", "malformed pretty string")
            })?;
            reserve_pretty_bytes(vm, text.len(), "PolyML pretty printer")?;
            Ok(Vec::new())
        },
        ("PolyML.PrettyStringWithWidth", Some(value)) => {
            let text = value.record_field("1").and_then(Value::as_text).ok_or_else(|| {
                vm.error(MlErrorKind::Type, "PolyML pretty printer", "malformed width string")
            })?;
            if value.record_field("2").and_then(Value::as_int).is_none() {
                return Err(vm.error(
                    MlErrorKind::Type,
                    "PolyML pretty printer",
                    "malformed string width",
                ));
            }
            reserve_pretty_bytes(vm, text.len(), "PolyML pretty printer")?;
            Ok(Vec::new())
        },
        ("PolyML.PrettyBreak", Some(value))
            if value.record_field("1").and_then(Value::as_int).is_some()
                && value.record_field("2").and_then(Value::as_int).is_some() =>
        {
            Ok(Vec::new())
        },
        ("PolyML.PrettyLineBreak", None) => Ok(Vec::new()),
        ("PolyML.PrettyBlock", Some(value)) => validate_pretty_block(vm, value),
        _ => Err(vm.error(
            MlErrorKind::Type,
            "PolyML pretty printer",
            "malformed PolyML.pretty constructor payload",
        )),
    }
}

fn validate_pretty_block(vm: &mut Vm, value: &Value) -> Result<Vec<Value>, MlError> {
    let is_header_valid = value.record_field("1").and_then(Value::as_int).is_some()
        && value.record_field("2").and_then(Value::as_bool).is_some();
    let contexts = value.record_field("3").and_then(Value::as_list);
    let body = value.record_field("4").and_then(Value::as_list);
    let (true, Some(contexts), Some(body)) = (is_header_valid, contexts, body) else {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML pretty printer",
            "PrettyBlock has malformed fields",
        ));
    };
    ensure_pretty_items(vm, contexts.len().saturating_add(body.len()), "PolyML pretty printer")?;
    for context in contexts {
        validate_pretty_context(vm, context)?;
    }
    Ok(body.to_vec())
}

fn validate_pretty_context(vm: &mut Vm, value: &Value) -> Result<(), MlError> {
    consume_pretty_node(vm, "PolyML pretty printer context")?;
    let ValueData::Constructor { name, stamp, argument: Some(argument) } = &*value.0 else {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML pretty printer",
            "PrettyBlock has malformed context",
        ));
    };
    if !vm.pretty_constructors.recognizes(name, *stamp) {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML pretty printer",
            "PrettyBlock has foreign context identity",
        ));
    }
    let is_valid = match name.as_str() {
        "PolyML.ContextLocation" => argument.record_length() == Some(5),
        "PolyML.ContextProperty" => {
            argument.record_field("1").and_then(Value::as_text).is_some()
                && argument.record_field("2").and_then(Value::as_text).is_some()
        },
        _ => false,
    };
    if !is_valid {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML pretty printer",
            "PrettyBlock has malformed context payload",
        ));
    }
    Ok(())
}

fn pretty_print(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let output =
        args.first().and_then(Value::as_tuple).filter(|parts| parts.len() == 2).ok_or_else(
            || vm.error(MlErrorKind::Type, "PolyML.prettyPrint", "expected output and margin"),
        )?;
    let margin = output[1].as_int().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.prettyPrint", "expected integer margin")
    })?;
    if margin < 0 {
        return Err(vm.raise_builtin("Size"));
    }
    let output_function = output[0].clone();
    let tree = args[1].clone();
    with_printer_budget(vm, |vm| {
        validate_pretty(vm, &tree)?;
        let mut result = String::new();
        append_pretty(vm, &tree, &mut result, usize::try_from(margin).unwrap_or(usize::MAX))?;
        let Some(Type::Function(input, _)) = vm.native_argument_field_type(0, "1") else {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "PolyML.prettyPrint",
                "missing certified output callback type",
            ));
        };
        vm.apply_with_type(&output_function, &Value::text(result), *input)?;
        Ok(Value::unit())
    })
}

fn append_pretty(
    vm: &mut Vm,
    value: &Value,
    out: &mut String,
    margin: usize,
) -> Result<(), MlError> {
    let mut stack = vec![(value.clone(), 0_usize)];
    while let Some((value, depth)) = stack.pop() {
        consume_pretty_node(vm, "PolyML.prettyPrint")?;
        if depth >= MAX_PRETTY_DEPTH {
            return Err(vm.raise_builtin("Size"));
        }
        let ValueData::Constructor { name, argument, .. } = &*value.0 else {
            return Err(vm.error(MlErrorKind::Type, "PolyML.prettyPrint", "expected pretty tree"));
        };
        match (name.as_str(), argument) {
            ("PolyML.PrettyString", Some(value)) => {
                let text = value.as_text().ok_or_else(|| {
                    vm.error(MlErrorKind::Type, "PolyML.prettyPrint", "expected pretty string")
                })?;
                append_bounded(vm, out, text)?;
            },
            ("PolyML.PrettyStringWithWidth", Some(value)) => {
                let text = value.record_field("1").and_then(Value::as_text).ok_or_else(|| {
                    vm.error(
                        MlErrorKind::Type,
                        "PolyML.prettyPrint",
                        "expected pretty string and width",
                    )
                })?;
                append_bounded(vm, out, text)?;
            },
            ("PolyML.PrettyLineBreak", None) => append_bounded(vm, out, "\n")?,
            ("PolyML.PrettyBreak", Some(value)) => {
                let width = value.record_field("1").and_then(Value::as_int).ok_or_else(|| {
                    vm.error(MlErrorKind::Type, "PolyML.prettyPrint", "expected break width")
                })?;
                if width > 0 {
                    let width = usize::try_from(width).unwrap_or(usize::MAX).min(margin);
                    reserve_pretty_bytes(vm, width, "PolyML.prettyPrint")?;
                    out.extend(std::iter::repeat_n(' ', width));
                }
            },
            ("PolyML.PrettyBlock", Some(value)) => {
                let body = value.record_field("4").and_then(Value::as_list).ok_or_else(|| {
                    vm.error(MlErrorKind::Type, "PolyML.prettyPrint", "expected pretty block")
                })?;
                ensure_pretty_items(vm, body.len(), "PolyML.prettyPrint")?;
                stack.extend(body.iter().rev().map(|item| (item.clone(), depth + 1)));
            },
            _ => {
                return Err(vm.error(
                    MlErrorKind::Type,
                    "PolyML.prettyPrint",
                    "invalid pretty constructor",
                ));
            },
        }
    }
    Ok(())
}

fn append_bounded(vm: &mut Vm, output: &mut String, text: &str) -> Result<(), MlError> {
    reserve_pretty_bytes(vm, text.len(), "PolyML.prettyPrint")?;
    output.push_str(text);
    Ok(())
}

fn as_function(typ: &Type) -> Option<(&Type, &Type)> {
    match typ {
        Type::Function(input, output) => Some((input, output)),
        _ => None,
    }
}

fn pair_first(typ: &Type) -> Option<&Type> {
    let Type::Record(fields, false) = typ else { return None };
    (fields.len() == 2).then(|| fields.get("1")).flatten()
}

fn require_pretty_type(vm: &Vm, typ: &Type, operation: &str) -> Result<(), MlError> {
    match typ {
        Type::Constructor(name, arguments) if name == "PolyML.pretty" && arguments.is_empty() => {
            Ok(())
        },
        _ => Err(vm.error(MlErrorKind::Type, operation, "printer result is not PolyML.pretty")),
    }
}
