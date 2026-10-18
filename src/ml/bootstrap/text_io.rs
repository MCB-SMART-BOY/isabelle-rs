//! TextIO source input streams with one child Stream lease per live handle.
use super::*;
use crate::ml::host::files::DiagnosticChannel;
use crate::ml::host::lifecycle::TaskLease;

use std::cell::RefCell;

struct TextInput {
    path: String,
    bytes: Vec<u8>,
    cursor: usize,
    lease: Option<TaskLease>,
}
struct TextOutput {
    channel: DiagnosticChannel,
    is_open: bool,
}

pub(super) fn install(vm: &mut Vm) -> Result<(), MlError> {
    vm.register_host_type("TextIO.instream", 0, false)?;
    vm.register_host_type("TextIO.outstream", 0, false)?;
    let path = Type::Constructor("string".to_owned(), vec![]);
    let input = Type::Constructor("TextIO.instream".to_owned(), vec![]);
    let output = Type::Constructor("TextIO.outstream".to_owned(), vec![]);
    let unit = Type::Constructor("unit".to_owned(), vec![]);
    vm.register_native(
        "TextIO.openIn",
        TypeScheme::mono(Type::Function(Box::new(path.clone()), Box::new(input.clone()))),
        open_in,
    )?;
    vm.register_native(
        "TextIO.inputAll",
        TypeScheme::mono(Type::Function(Box::new(input.clone()), Box::new(path.clone()))),
        input_all,
    )?;
    vm.register_native(
        "TextIO.closeIn",
        TypeScheme::mono(Type::Function(Box::new(input), Box::new(unit.clone()))),
        close_in,
    )?;
    let tuple = Type::Record(
        BTreeMap::from([("1".to_owned(), output.clone()), ("2".to_owned(), path)]),
        false,
    );
    vm.register_native(
        "TextIO.output",
        TypeScheme::mono(Type::Function(Box::new(tuple), Box::new(unit.clone()))),
        output_text,
    )?;
    for (name, callback) in [
        ("TextIO.flushOut", flush_out as super::super::NativeFunction),
        ("TextIO.closeOut", close_out),
    ] {
        vm.register_native(
            name,
            TypeScheme::mono(Type::Function(Box::new(output.clone()), Box::new(unit.clone()))),
            callback,
        )?;
    }
    for (name, channel) in
        [("TextIO.stdOut", DiagnosticChannel::Stdout), ("TextIO.stdErr", DiagnosticChannel::Stderr)]
    {
        let value =
            vm.insert_host_object(Rc::new(RefCell::new(TextOutput { channel, is_open: true })))?;
        vm.register_value(name, TypeScheme::mono(output.clone()), value);
    }
    Ok(())
}

fn open_in(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(name) = args.first().and_then(Value::as_text) else {
        return Err(vm.error(MlErrorKind::Type, "TextIO.openIn", "expected source path string"));
    };
    let path = if name.starts_with(PURE_SOURCE) {
        name.to_owned()
    } else {
        format!("{PURE_SOURCE}{name}")
    };
    let Some(host) = vm.bootstrap_host.as_ref().cloned() else {
        return Err(vm.error(
            MlErrorKind::HostPermission,
            "TextIO.openIn",
            "no leased bootstrap host installed",
        ));
    };
    let (bytes, lease) = host
        .open_source_stream(Path::new(&path))
        .map_err(|error| vm.host_io_failure("TextIO.openIn", &path, error))?;
    let input = Rc::new(RefCell::new(TextInput { path, bytes, cursor: 0, lease: Some(lease) }));
    vm.insert_host_object(input)
}

fn get_input(
    vm: &mut Vm,
    args: &[Value],
    operation: &str,
) -> Result<Rc<RefCell<TextInput>>, MlError> {
    let Some(id) = args.first().and_then(Value::as_host_object) else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected TextIO.instream"));
    };
    let object = vm.get_host_object(id)?;
    match Rc::downcast::<RefCell<TextInput>>(object) {
        Ok(input) => Ok(input),
        Err(_) => {
            vm.request_stop();
            Err(vm.error(MlErrorKind::HostFailure, operation, "host object has wrong stream kind"))
        },
    }
}

fn input_all(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let input = get_input(vm, args, "TextIO.inputAll")?;
    let mut input = input.try_borrow_mut().map_err(|cause| {
        vm.request_stop();
        vm.error(
            MlErrorKind::HostFailure,
            "TextIO.inputAll",
            format!("reentrant stream access: {cause}"),
        )
    })?;
    if input.lease.is_none() {
        return Err(vm.raise_io_exception(
            "TextIO.inputAll",
            &input.path,
            "stream already closed".to_owned(),
        ));
    }
    vm.check_stop()?;
    if input.cursor == 0 {
        vm.record_root_read(&input.path, &input.bytes)?;
    }
    let remaining = Value::bytes(input.bytes[input.cursor..].to_vec());
    input.cursor = input.bytes.len();
    Ok(remaining)
}

fn close_in(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let input = get_input(vm, args, "TextIO.closeIn")?;
    let lease = input
        .try_borrow_mut()
        .map_err(|cause| {
            vm.request_stop();
            vm.error(
                MlErrorKind::HostFailure,
                "TextIO.closeIn",
                format!("reentrant stream access: {cause}"),
            )
        })?
        .lease
        .take();
    let Some(lease) = lease else {
        return Err(vm.raise_io_exception(
            "TextIO.closeIn",
            "closed TextIO stream",
            "stream already closed".to_owned(),
        ));
    };
    lease.complete().map_err(|error| {
        vm.request_stop();
        vm.error(
            MlErrorKind::Stopped,
            "TextIO.closeIn",
            format!("complete TextIO input stream: {error}"),
        )
    })?;
    Ok(Value::unit())
}

fn get_output(
    vm: &mut Vm,
    value: &Value,
    operation: &str,
) -> Result<Rc<RefCell<TextOutput>>, MlError> {
    let Some(id) = value.as_host_object() else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected TextIO.outstream"));
    };
    let object = vm.get_host_object(id)?;
    match Rc::downcast::<RefCell<TextOutput>>(object) {
        Ok(output) => Ok(output),
        Err(_) => {
            vm.request_stop();
            Err(vm.error(MlErrorKind::HostFailure, operation, "host object has wrong output kind"))
        },
    }
}

fn output_text(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some([output, text]) = args.first().and_then(Value::as_tuple) else {
        return Err(vm.error(MlErrorKind::Type, "TextIO.output", "expected (outstream, string)"));
    };
    let output = get_output(vm, output, "TextIO.output")?;
    let stream = output.try_borrow().map_err(|cause| {
        vm.request_stop();
        vm.error(
            MlErrorKind::HostFailure,
            "TextIO.output",
            format!("reentrant stream access: {cause}"),
        )
    })?;
    if !stream.is_open {
        return Err(vm.raise_io_exception(
            "TextIO.output",
            "standard output",
            "stream already closed".to_owned(),
        ));
    }
    let Some(bytes) = text.as_bytes() else {
        return Err(vm.error(MlErrorKind::Type, "TextIO.output", "expected string payload"));
    };
    let Some(host) = vm.bootstrap_host.as_ref().cloned() else {
        return Err(vm.error(
            MlErrorKind::HostPermission,
            "TextIO.output",
            "no leased bootstrap host installed",
        ));
    };
    host.write_output(stream.channel, bytes)
        .map_err(|error| vm.host_io_failure("TextIO.output", "standard output", error))?;
    Ok(Value::unit())
}

fn flush_out(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(stream) = args.first() else {
        return Err(vm.error(MlErrorKind::Type, "TextIO.flushOut", "expected outstream"));
    };
    let output = get_output(vm, stream, "TextIO.flushOut")?;
    let output = output.try_borrow().map_err(|cause| {
        vm.request_stop();
        vm.error(
            MlErrorKind::HostFailure,
            "TextIO.flushOut",
            format!("reentrant stream access: {cause}"),
        )
    })?;
    if !output.is_open {
        return Err(vm.raise_io_exception(
            "TextIO.flushOut",
            "standard output",
            "stream already closed".to_owned(),
        ));
    }
    vm.check_stop()?;
    // Each preceding output was synchronously written and synced by RestrictedHost.
    Ok(Value::unit())
}

fn close_out(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(stream) = args.first() else {
        return Err(vm.error(MlErrorKind::Type, "TextIO.closeOut", "expected outstream"));
    };
    let output = get_output(vm, stream, "TextIO.closeOut")?;
    let mut output = output.try_borrow_mut().map_err(|cause| {
        vm.request_stop();
        vm.error(
            MlErrorKind::HostFailure,
            "TextIO.closeOut",
            format!("reentrant stream access: {cause}"),
        )
    })?;
    vm.check_stop()?;
    output.is_open = false;
    Ok(Value::unit())
}
