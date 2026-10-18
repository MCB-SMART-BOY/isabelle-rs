//! The original Poly/ML compiler API, backed by the same native SML parser and evaluator.
use super::{
    MlError, MlErrorKind, Type, TypeScheme, Value, ValueData, Vm, container, function, pair, typ,
};
use crate::ml::parser;
use crate::ml::types::Infer;
use crate::ml::value::NativeFunctionId;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

struct CompiledTopdec {
    file: String,
    source: Vec<u8>,
    declarations: Vec<crate::ml::Declaration>,
    namespace: Option<Value>,
}

struct CompilerOptions {
    file: String,
    reporter: Option<Value>,
    namespace: Option<Value>,
}

const MAX_COMPILER_SOURCE_BYTES: usize = crate::ml::host::files::MAX_FILE_BYTES;

pub(super) fn install(vm: &mut Vm) {
    super::printers::install(vm);
    let parameters = "PolyML.Compiler.compilerParameters";
    vm.register_host_type(parameters, 0, false).expect("fresh compiler parameter type");
    let string = typ("string");
    let unit = typ("unit");
    let pretty = typ("PolyML.pretty");
    let location = typ("PolyML.location");
    let callback = function(string.clone(), unit.clone());
    let error_message = Type::Record(
        BTreeMap::from([
            ("message".to_owned(), pretty.clone()),
            ("hard".to_owned(), typ("bool")),
            ("location".to_owned(), location),
            ("context".to_owned(), container("option", pretty)),
        ]),
        false,
    );
    let entries = [
        ("CPOutStream", callback.clone()),
        (
            "CPNameSpace",
            vm.type_environment
                .type_shape("PolyML.NameSpace.nameSpace")
                .expect("namespace type installed before compiler parameters"),
        ),
        ("CPErrorMessageProc", function(error_message, unit.clone())),
        ("CPLineNo", function(unit.clone(), typ("int"))),
        ("CPFileName", string),
        ("CPPrintInAlphabeticalOrder", typ("bool")),
        ("CPDebug", typ("bool")),
        ("CPPrintDepth", function(unit.clone(), typ("int"))),
    ];
    for (name, payload) in entries {
        let qualified = format!("PolyML.Compiler.{name}");
        let stamp = vm.fresh_identity();
        vm.register_value(
            &qualified,
            TypeScheme::mono(function(payload, typ(parameters))),
            Value(Rc::new(ValueData::ConstructorFunction { stamp, name: name.to_owned() })),
        );
    }
    for (name, initial) in [
        ("reportUnreferencedIds", Value::bool(true)),
        ("reportExhaustiveHandlers", Value::bool(true)),
        ("printInAlphabeticalOrder", Value::bool(false)),
        ("maxInlineSize", Value::int(80)),
    ] {
        let base = if name == "maxInlineSize" { typ("int") } else { typ("bool") };
        vm.register_value(
            &format!("PolyML.Compiler.{name}"),
            TypeScheme::mono(container("ref", base)),
            Value::reference(initial),
        );
    }
    let get = function(unit.clone(), container("option", typ("char")));
    let compiler =
        function(pair(get, container("list", typ(parameters))), function(unit.clone(), unit));
    vm.register_pure("PolyML.compiler", &[], compiler, 1, compile_topdec);
}

fn compile_topdec(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let input =
        args.first().and_then(Value::as_tuple).filter(|pair| pair.len() == 2).ok_or_else(|| {
            vm.error(
                MlErrorKind::Type,
                "PolyML.compiler",
                "expected input callback and compiler options",
            )
        })?;
    let options = compiler_options(vm, &input[1])?;
    let mut program = read_topdec(vm, &input[0], &options.file, options.reporter.as_ref())?;
    program.namespace = options.namespace;
    let object = vm.insert_host_object(Rc::new(program))?;
    let id = NativeFunctionId::new(vm.runtime_id, vm.generation, vm.native_functions.len());
    vm.native_functions.push((execute_topdec, 2));
    Ok(vm.track_value(Value(Rc::new(ValueData::NativePartial {
        id,
        arguments: RefCell::new(vec![object]),
        argument_types: RefCell::new(vec![None]),
        result_type: RefCell::new(None),
    }))))
}

fn compiler_options(vm: &Vm, values: &Value) -> Result<CompilerOptions, MlError> {
    let entries = values.as_list().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.compiler", "compiler parameters must be a list")
    })?;
    let mut options = CompilerOptions { file: String::new(), reporter: None, namespace: None };
    for entry in entries {
        let ValueData::Constructor { name, stamp, argument: Some(argument) } = &*entry.0 else {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.compiler",
                "malformed compiler parameter",
            ));
        };
        let qualified = format!("PolyML.Compiler.{name}");
        let registered = vm.values.get(&qualified).ok_or_else(|| {
            vm.error(MlErrorKind::Type, "PolyML.compiler", "unknown compiler parameter")
        })?;
        if !matches!(&*registered.0, ValueData::ConstructorFunction { stamp: registered_stamp, .. }
            if registered_stamp == stamp)
        {
            return Err(vm.error(
                MlErrorKind::Type,
                "PolyML.compiler",
                "foreign compiler parameter identity",
            ));
        }
        match name.as_str() {
            "CPFileName" => {
                options.file = argument
                    .as_text()
                    .ok_or_else(|| {
                        vm.error(MlErrorKind::Type, "PolyML.compiler", "CPFileName is not a string")
                    })?
                    .to_owned();
            },
            "CPErrorMessageProc" => options.reporter = Some(argument.clone()),
            "CPNameSpace" => options.namespace = Some(argument.clone()),
            "CPOutStream"
            | "CPLineNo"
            | "CPPrintInAlphabeticalOrder"
            | "CPDebug"
            | "CPPrintDepth" => {},
            other => {
                return Err(vm.error(
                    MlErrorKind::Type,
                    "PolyML.compiler",
                    format!("compiler option {other} has no native semantics"),
                ));
            },
        }
    }
    if let Some(namespace) = &options.namespace {
        let global = vm.values.get("PolyML.globalNameSpace").ok_or_else(|| {
            vm.error(MlErrorKind::HostFailure, "PolyML.compiler", "missing global namespace")
        })?;
        if namespace != global {
            super::poly_namespace::check_wrapped_global(vm, namespace, global)?;
        } else {
            options.namespace = None;
        }
    }
    Ok(options)
}

fn read_topdec(
    vm: &mut Vm,
    get: &Value,
    file: &str,
    reporter: Option<&Value>,
) -> Result<CompiledTopdec, MlError> {
    let mut source = Vec::new();
    loop {
        vm.check_stop()?;
        let callback_type = vm.native_argument_field_type(0, "1");
        let value = super::text::apply_typed_callback(vm, get, &[Value::unit()], callback_type)?;
        let next = match &*value.0 {
            ValueData::Constructor { stamp, argument: None, .. }
                if *stamp == vm.option_none_stamp =>
            {
                None
            },
            ValueData::Constructor { stamp, argument: Some(value), .. }
                if *stamp == vm.option_some_stamp =>
            {
                let ValueData::Character(character) = &*value.0 else {
                    return Err(vm.error(
                        MlErrorKind::Type,
                        "PolyML.compiler",
                        "input callback returned non-character",
                    ));
                };
                Some(*character)
            },
            _ => {
                return Err(vm.error(
                    MlErrorKind::Type,
                    "PolyML.compiler",
                    "input callback returned non-option",
                ));
            },
        };
        let Some(character) = next else { break };
        if source.len() == MAX_COMPILER_SOURCE_BYTES {
            return Err(vm.raise_builtin("Size"));
        }
        source.push(character);
        if character != b';' {
            continue;
        }
        let Ok(text) = std::str::from_utf8(&source) else { continue };
        if let Ok(declarations) = parser::parse(file, text, &vm.fixities, &vm.stop.0.requested) {
            return check_topdec(vm, file, declarations, source, reporter);
        }
    }
    let text = std::str::from_utf8(&source).map_err(|cause| {
        vm.raise_named_exception(
            "Fail",
            Some(Value::text(cause.to_string())),
            "PolyML.compiler",
            format!("decode SML source {file}: {cause}"),
        )
    })?;
    let declarations = parser::parse(file, text, &vm.fixities, &vm.stop.0.requested)
        .map_err(|error| compiler_error(vm, file, reporter, error))?;
    check_topdec(vm, file, declarations, source, reporter)
}

fn check_topdec(
    vm: &mut Vm,
    file: &str,
    declarations: Vec<crate::ml::Declaration>,
    source: Vec<u8>,
    reporter: Option<&Value>,
) -> Result<CompiledTopdec, MlError> {
    let mut types = vm.type_environment.clone();
    for declaration in &declarations {
        let mut infer = Infer::new(types, declaration.span());
        infer.modules = crate::ml::static_module::StaticModules::from_runtime(
            &vm.structures,
            &vm.signatures,
            &vm.functors,
        );
        infer
            .declaration(declaration)
            .map_err(|error| compiler_error(vm, file, reporter, error))?;
        infer
            .check_flexible_records()
            .map_err(|error| compiler_error(vm, file, reporter, error))?;
        types = infer.finish().0;
    }
    Ok(CompiledTopdec { file: file.to_owned(), source, declarations, namespace: None })
}

fn compiler_error(vm: &mut Vm, file: &str, reporter: Option<&Value>, error: MlError) -> MlError {
    if matches!(
        error.kind,
        MlErrorKind::Stopped | MlErrorKind::HostPermission | MlErrorKind::HostFailure
    ) {
        return error;
    }
    if let Some(report) = reporter {
        let location = Value(Rc::new(ValueData::Record(BTreeMap::from([
            ("file".to_owned(), Value::text(file)),
            ("startLine".to_owned(), Value::int(1)),
            ("endLine".to_owned(), Value::int(1)),
            ("startPosition".to_owned(), Value::int(error.span.start as i64)),
            ("endPosition".to_owned(), Value::int(error.span.end as i64)),
        ]))));
        let Some(pretty) = vm.values.get("PolyML.PrettyString").cloned() else {
            return vm.error(
                MlErrorKind::HostFailure,
                "PolyML.compiler",
                "missing pretty constructor",
            );
        };
        let message = match vm.apply_with_type(&pretty, &Value::text(&error.cause), typ("string")) {
            Ok(message) => message,
            Err(error) => return error,
        };
        let context = match vm.make_option(None) {
            Ok(context) => context,
            Err(error) => return error,
        };
        let report_value = Value(Rc::new(ValueData::Record(BTreeMap::from([
            ("message".to_owned(), message),
            ("hard".to_owned(), Value::bool(true)),
            ("location".to_owned(), location),
            ("context".to_owned(), context),
        ]))));
        let reporter_type =
            vm.type_environment.lookup("PolyML.Compiler.CPErrorMessageProc").map(TypeScheme::body);
        let Some(Type::Function(callback, _)) = reporter_type else {
            return vm.error(
                MlErrorKind::HostFailure,
                "PolyML.compiler",
                "missing registered reporter type",
            );
        };
        let Type::Function(input, _) = &**callback else {
            return vm.error(
                MlErrorKind::HostFailure,
                "PolyML.compiler",
                "invalid registered reporter type",
            );
        };
        let report_type = (**input).clone();
        if let Err(callback_error) = vm.apply_with_type(report, &report_value, report_type) {
            return callback_error;
        }
    }
    vm.raise_named_exception(
        "Fail",
        Some(Value::text(&error.cause)),
        "PolyML.compiler",
        format!("compile {file}: {}: {}", error.operation, error.cause),
    )
}

fn execute_topdec(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    if !args.get(1).is_some_and(Value::is_unit) {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML.compiler",
            "compiled function expects unit",
        ));
    }
    let id = args[0]
        .as_host_object()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "PolyML.compiler", "missing compiled topdec"))?;
    let program = vm.get_host_object(id)?.downcast::<CompiledTopdec>().map_err(|_| {
        vm.request_stop();
        vm.error(MlErrorKind::HostFailure, "PolyML.compiler", "compiled topdec has wrong host kind")
    })?;
    let previous_name = std::mem::replace(&mut vm.source_name, program.file.clone());
    let evaluate = |vm: &mut Vm| {
        for declaration in &program.declarations {
            vm.evaluate_declaration(declaration)?;
            vm.apply_fixity_declaration(declaration);
        }
        Ok(())
    };
    let result = if let Some(namespace) = &program.namespace {
        super::poly_namespace::execute_wrapped_global(vm, namespace, evaluate)
    } else {
        evaluate(vm)
    };
    vm.source_name = previous_name;
    result?;
    vm.record_root_compilation(&program.file, &program.source)?;
    Ok(Value::unit())
}
