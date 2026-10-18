//! Source-backed ML exception packets and the exception-only Poly/ML Basis surface.
use super::{arg, container, function, pair, scheme, typ, var};
use crate::ml::types::Type;
use crate::ml::value::ValueData;
use crate::ml::{ExceptionOrigin, MlError, MlErrorKind, SourceLocation, Span, Value, Vm};
use std::collections::BTreeMap;
use std::rc::Rc;
use std::sync::OnceLock;

pub(super) fn install(vm: &mut Vm) {
    let location_fields = BTreeMap::from([
        ("file".to_owned(), typ("string")),
        ("startLine".to_owned(), typ("int")),
        ("startPosition".to_owned(), typ("int")),
        ("endLine".to_owned(), typ("int")),
        ("endPosition".to_owned(), typ("int")),
    ]);
    let location = Type::Record(location_fields, false);
    vm.type_environment.register_alias("PolyML.location", vec![], location.clone());
    let polyml = vm.structures.entry("PolyML".to_owned()).or_default();
    polyml.type_environment.register_alias("location", vec![], location.clone());
    polyml.types.insert("location".to_owned(), 0);
    vm.register_pure(
        "PolyML.Exception.exceptionLocation",
        &[],
        function(typ("exn"), container("option", location)),
        1,
        exception_location,
    );
    vm.register_pure("PolyML.Exception.reraise", &[1], function(typ("exn"), var(1)), 1, reraise);
    vm.register_pure(
        "PolyML.error_depth",
        &[],
        function(typ("int"), typ("unit")),
        1,
        set_error_depth,
    );
    vm.register_pure(
        "PolyML.Exception.traceException",
        &[1],
        function(
            pair(
                function(typ("unit"), var(1)),
                function(pair(container("list", typ("string")), typ("exn")), var(1)),
            ),
            var(1),
        ),
        1,
        trace_exception,
    );
    let fail_identity = vm.fresh_identity();
    vm.register_value(
        "Fail",
        scheme(&[], function(typ("string"), typ("exn"))),
        Value(Rc::new(ValueData::ExceptionFunction {
            identity: fail_identity,
            name: "Fail".to_owned(),
        })),
    );
    let io_identity = vm.fresh_identity();
    vm.register_value(
        "IO.Io",
        scheme(
            &[],
            function(
                Type::Record(
                    BTreeMap::from([
                        ("name".to_owned(), typ("string")),
                        ("function".to_owned(), typ("string")),
                        ("cause".to_owned(), typ("exn")),
                    ]),
                    false,
                ),
                typ("exn"),
            ),
        ),
        Value(Rc::new(ValueData::ExceptionFunction {
            identity: io_identity,
            name: "Io".to_owned(),
        })),
    );
    let interrupt = Value(Rc::new(ValueData::Exception {
        identity: vm.fresh_identity(),
        name: "Interrupt".to_owned(),
        argument: None,
    }));
    vm.register_value("Thread.Thread.Interrupt", scheme(&[], typ("exn")), interrupt);
}

impl Vm {
    pub(crate) fn raise_exception(
        &mut self,
        exception: &Value,
        location: Option<&SourceLocation>,
        preserve: bool,
    ) -> Result<MlError, MlError> {
        self.check_stop()?;
        let ValueData::Exception { identity, name, argument } = &*exception.0 else {
            return Err(self.error(MlErrorKind::Type, "raise", "argument is not exception"));
        };
        if (*identity >> 64) != u128::from(self.runtime_id) {
            self.request_stop();
            return Err(self.error(MlErrorKind::HostFailure, "raise", "foreign runtime exception"));
        }
        let packet = if preserve {
            exception.clone()
        } else {
            self.track_value(Value(Rc::new(ValueData::Exception {
                identity: *identity,
                name: name.clone(),
                argument: argument.clone(),
            })))
        };
        let mut error = self.error(MlErrorKind::Exception(*identity), "raise", name);
        error.exception = Some(packet.clone());
        if preserve {
            if let Some(origin) = self.exception_origin(&packet) {
                error.span = Box::new(origin.location.span.clone());
                error.trace = origin.trace.clone();
            }
        } else if let Some(location) = location {
            error.span = Box::new(location.span.clone());
            error.trace.push(location.describe("raise"));
            self.remember_exception_origin(&packet, location.clone(), error.trace.clone());
        }
        Ok(error)
    }

    /// Reject malformed or foreign errors before an ML handler can inspect the packet.
    pub(crate) fn validate_exception_error(
        &self,
        error: &MlError,
        operation: &str,
    ) -> Result<(), MlError> {
        let Some(packet) = error.exception.as_ref() else {
            return Err(self.invalid_exception_error(error, operation));
        };
        let ValueData::Exception { identity, .. } = &*packet.0 else {
            return Err(self.invalid_exception_error(error, operation));
        };
        if error.kind != MlErrorKind::Exception(*identity)
            || (*identity >> 64) != u128::from(self.runtime_id)
        {
            return Err(self.invalid_exception_error(error, operation));
        }
        Ok(())
    }

    fn invalid_exception_error(&self, error: &MlError, operation: &str) -> MlError {
        self.request_stop();
        self.error(
            MlErrorKind::HostFailure,
            operation,
            format!("invalid exception error ({:?}): {error}", error.kind),
        )
    }

    pub(crate) fn append_exception_frame(
        &mut self,
        error: &mut MlError,
        location: &SourceLocation,
    ) {
        error.trace.push(location.describe("apply"));
        if let Some(packet) = &error.exception {
            let key = Rc::as_ptr(&packet.0) as usize;
            if let Some((weak, origin)) = self.exception_origins.get_mut(&key)
                && weak.upgrade().is_some_and(|object| Rc::ptr_eq(&object, &packet.0))
            {
                origin.trace = error.trace.clone();
            }
        }
    }

    fn remember_exception_origin(
        &mut self,
        packet: &Value,
        location: SourceLocation,
        trace: Vec<String>,
    ) {
        self.exception_origins.insert(
            Rc::as_ptr(&packet.0) as usize,
            (Rc::downgrade(&packet.0), ExceptionOrigin { location, trace }),
        );
    }

    fn exception_origin(&self, packet: &Value) -> Option<&ExceptionOrigin> {
        let (weak, origin) = self.exception_origins.get(&(Rc::as_ptr(&packet.0) as usize))?;
        weak.upgrade().is_some_and(|object| Rc::ptr_eq(&object, &packet.0)).then_some(origin)
    }
}

impl SourceLocation {
    fn describe(&self, operation: &str) -> String {
        format!(
            "{}:{}:{}-{}:{}: {operation}",
            self.span.source_name,
            self.start_line,
            self.start_position,
            self.end_line,
            self.end_position
        )
    }
}

fn exception_location(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let packet = arg(vm, args, 0, "PolyML.Exception.exceptionLocation")?;
    validate_exception(vm, packet, "PolyML.Exception.exceptionLocation")?;
    let Some(origin) = vm.exception_origin(packet) else {
        return Ok(super::text::option(vm, None));
    };
    let location = &origin.location;
    let record = Value(Rc::new(ValueData::Record(BTreeMap::from([
        ("file".to_owned(), Value::text(&location.span.source_name)),
        ("startLine".to_owned(), Value::int(location.start_line)),
        ("startPosition".to_owned(), Value::int(location.start_position)),
        ("endLine".to_owned(), Value::int(location.end_line)),
        ("endPosition".to_owned(), Value::int(location.end_position)),
    ]))));
    let record = vm.track_value(record);
    let some = Value(Rc::new(ValueData::Constructor {
        stamp: vm.option_some_stamp,
        name: "SOME".to_owned(),
        argument: Some(record),
    }));
    Ok(vm.track_value(some))
}

fn reraise(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let packet = arg(vm, args, 0, "PolyML.Exception.reraise")?;
    if vm.exception_origin(packet).is_some() {
        return Err(vm.raise_exception(packet, None, true)?);
    }
    // The NONE branch is an ordinary raise at this Rust implementation site.
    Err(vm.raise_exception(packet, Some(native_raise_location(line!(), column!())), false)?)
}

fn native_raise_location(line: u32, column: u32) -> &'static SourceLocation {
    // This cache contains only the fixed, compile-time Rust implementation site.
    static LOCATION: OnceLock<SourceLocation> = OnceLock::new();
    LOCATION.get_or_init(|| {
        let source = include_str!("exception_runtime.rs");
        let line_start =
            source.split_inclusive('\n').take(line as usize - 1).map(str::len).sum::<usize>();
        let column_start = source[line_start..]
            .chars()
            .take(column as usize - 1)
            .map(char::len_utf8)
            .sum::<usize>();
        let byte_start = line_start + column_start;
        let symbol_position = source[..byte_start].chars().count() as i64 + 1;
        SourceLocation {
            span: Span::new(file!(), byte_start, byte_start + 1),
            start_line: i64::from(line),
            start_position: symbol_position,
            end_line: i64::from(line),
            end_position: symbol_position + 1,
        }
    })
}

fn set_error_depth(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    if args.first().and_then(Value::as_int).is_none() {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML.error_depth",
            "expected integer display depth",
        ));
    }
    Err(vm.error(
        MlErrorKind::HostPermission,
        "PolyML.error_depth",
        "native compiler error-value pretty-printing is not installed",
    ))
}

fn trace_exception(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let pair = super::fields(
        vm,
        arg(vm, args, 0, "PolyML.Exception.traceException")?,
        2,
        "PolyML.Exception.traceException",
    )?;
    let execution = pair[0].clone();
    let report = pair[1].clone();
    match apply_trace_callback(vm, &execution, &Value::unit(), "1") {
        Ok(result) => Ok(result),
        Err(error) if matches!(error.kind, MlErrorKind::Exception(_)) => {
            vm.validate_exception_error(&error, "PolyML.Exception.traceException")?;
            let trace = Value::list(error.trace.iter().map(Value::text).collect());
            let Some(packet) = error.exception else {
                return Err(vm.error(
                    MlErrorKind::HostFailure,
                    "PolyML.Exception.traceException",
                    "validated exception lost its packet",
                ));
            };
            let report_input = super::text::tuple(vm, vec![trace, packet]);
            apply_trace_callback(vm, &report, &report_input, "2")
        },
        Err(error) => Err(error),
    }
}

fn apply_trace_callback(
    vm: &mut Vm,
    callback: &Value,
    argument: &Value,
    field: &str,
) -> Result<Value, MlError> {
    let Some(Type::Function(input, _)) = vm.native_argument_field_type(0, field) else {
        return Err(vm.error(
            MlErrorKind::HostFailure,
            "PolyML.Exception.traceException",
            "missing compiler-certified callback type",
        ));
    };
    vm.apply_with_type(callback, argument, *input)
}

fn validate_exception(vm: &Vm, packet: &Value, operation: &str) -> Result<(), MlError> {
    let ValueData::Exception { identity, .. } = &*packet.0 else {
        return Err(vm.error(MlErrorKind::Type, operation, "argument is not exception"));
    };
    if (*identity >> 64) != u128::from(vm.runtime_id) {
        vm.request_stop();
        return Err(vm.error(MlErrorKind::HostFailure, operation, "foreign runtime exception"));
    }
    Ok(())
}
