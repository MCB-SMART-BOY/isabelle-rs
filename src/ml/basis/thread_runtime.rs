//! VM-owned thread identity, generative tags and the original ROOT0 word-flags bridge.
use super::{
    MlError, MlErrorKind, Type, TypeScheme, Value, ValueData, Vm, container, function, pair, typ,
    var,
};
use crate::ml::value::HostObjectId;
use std::cell::Cell;
use std::rc::Rc;

const FLAGS_WORD_OFFSET: u64 = 1;

pub(super) struct VmThread {
    flags: Cell<u64>,
}

pub(super) struct UniversalTag;

pub(super) fn install(vm: &mut Vm) {
    vm.register_host_type("Universal.tag", 1, false).expect("fresh VM Universal.tag type");
    vm.register_host_type("Thread.Thread.thread", 0, false).expect("fresh VM thread type");
    let tag = container("Universal.tag", var(1));
    vm.register_pure("Universal.tag", &[1], function(typ("unit"), tag.clone()), 1, new_tag);
    vm.register_pure(
        "Thread.Thread.getLocal",
        &[1],
        function(tag.clone(), container("option", var(1))),
        1,
        get_local,
    );
    vm.register_pure(
        "Thread.Thread.setLocal",
        &[1],
        function(pair(tag, var(1)), typ("unit")),
        1,
        set_local,
    );
    vm.register_pure(
        "Thread.Thread.self",
        &[],
        function(typ("unit"), typ("Thread.Thread.thread")),
        1,
        thread_self,
    );
    vm.register_pure(
        "Thread.Thread.equal",
        &[],
        function(pair(typ("Thread.Thread.thread"), typ("Thread.Thread.thread")), typ("bool")),
        1,
        thread_equal,
    );
    vm.register_pure(
        "Thread.Thread.testInterrupt",
        &[],
        function(typ("unit"), typ("unit")),
        1,
        test_interrupt,
    );
    vm.register_pure(
        "Thread.Thread.isActive",
        &[],
        function(typ("Thread.Thread.thread"), typ("bool")),
        1,
        is_active,
    );
    vm.register_pure(
        "Thread.Thread.fork",
        &[],
        function(
            pair(
                function(typ("unit"), typ("unit")),
                container("list", typ("Thread.Thread.threadAttribute")),
            ),
            typ("Thread.Thread.thread"),
        ),
        1,
        unavailable_fork,
    );
    vm.register_pure(
        "Thread.Thread.interrupt",
        &[],
        function(typ("Thread.Thread.thread"), typ("unit")),
        1,
        unavailable_interrupt,
    );
    vm.register_pure(
        "Thread.Thread.numProcessors",
        &[],
        function(typ("unit"), typ("int")),
        1,
        unavailable_processor_count,
    );
    vm.register_pure(
        "Thread.Thread.numPhysicalProcessors",
        &[],
        function(typ("unit"), container("option", typ("int"))),
        1,
        unavailable_physical_count,
    );
    let thread_exception = vm.fresh_identity();
    vm.register_value(
        "Thread.Thread",
        TypeScheme::mono(function(typ("string"), typ("exn"))),
        Value(Rc::new(ValueData::ExceptionFunction {
            identity: thread_exception,
            name: "Thread".to_owned(),
        })),
    );
    vm.register_pure("RunCall.unsafeCast", &[1, 2], function(var(1), var(2)), 1, cast_thread);
    vm.register_pure(
        "RunCall.loadWord",
        &[],
        function(pair(typ("word"), typ("word")), typ("word")),
        1,
        load_word,
    );
    vm.register_pure(
        "RunCall.storeWord",
        &[],
        function(
            Type::Record(
                std::collections::BTreeMap::from([
                    ("1".to_owned(), typ("word")),
                    ("2".to_owned(), typ("word")),
                    ("3".to_owned(), typ("word")),
                ]),
                false,
            ),
            typ("unit"),
        ),
        1,
        store_word,
    );
    vm.register_pure(
        "RunCall.clearMutableBit",
        &[1],
        function(container("ref", var(1)), typ("unit")),
        1,
        clear_mutable_bit,
    );
    register_attributes(vm);
}

fn register_attributes(vm: &mut Vm) {
    vm.type_environment.register_type("Thread.Thread.interruptState", 0, true);
    vm.type_environment.register_type("Thread.Thread.threadAttribute", 0, true);
    let state = typ("Thread.Thread.interruptState");
    let attribute = typ("Thread.Thread.threadAttribute");
    for name in ["InterruptDefer", "InterruptSynch", "InterruptAsynch", "InterruptAsynchOnce"] {
        let stamp = vm.fresh_identity();
        vm.register_value(
            &format!("Thread.Thread.{name}"),
            TypeScheme::mono(state.clone()),
            Value(Rc::new(ValueData::Constructor { stamp, name: name.to_owned(), argument: None })),
        );
    }
    for (name, input) in [
        ("EnableBroadcastInterrupt", typ("bool")),
        ("InterruptState", state),
        ("MaximumMLStack", container("option", typ("int"))),
    ] {
        let stamp = vm.fresh_identity();
        vm.register_value(
            &format!("Thread.Thread.{name}"),
            TypeScheme::mono(function(input, attribute.clone())),
            Value(Rc::new(ValueData::ConstructorFunction { stamp, name: name.to_owned() })),
        );
    }
}

fn new_tag(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    vm.insert_host_object(Rc::new(UniversalTag))
}

fn tag_id(vm: &Vm, tag: &Value, operation: &str) -> Result<HostObjectId, MlError> {
    if tag.downcast_host_object::<UniversalTag>().is_none() {
        return Err(vm.error(MlErrorKind::Type, operation, "expected VM-owned Universal.tag"));
    }
    let id = tag
        .as_host_object()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "missing tag identity"))?;
    vm.get_host_object(id)?;
    Ok(id)
}

fn get_local(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let id = tag_id(vm, &args[0], "Thread.Thread.getLocal")?;
    let value = vm
        .thread_locals
        .get(&std::thread::current().id())
        .and_then(|locals| locals.get(&id))
        .cloned();
    vm.make_option(value)
}

fn set_local(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [tag, value] = super::fields(vm, &args[0], 2, "Thread.Thread.setLocal")? else {
        return Err(vm.error(
            MlErrorKind::Type,
            "Thread.Thread.setLocal",
            "expected tag and value pair",
        ));
    };
    let id = tag_id(vm, tag, "Thread.Thread.setLocal")?;
    vm.thread_locals.entry(std::thread::current().id()).or_default().insert(id, value.clone());
    Ok(Value::unit())
}

fn thread_self(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    if let Some(value) = vm.thread_self.clone() {
        return Ok(value);
    }
    let value = vm.insert_host_object(Rc::new(VmThread { flags: Cell::new(0) }))?;
    vm.thread_self = Some(value.clone());
    Ok(value)
}

fn thread_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [left, right] = super::fields(vm, &args[0], 2, "Thread.Thread.equal")? else {
        return Err(vm.error(
            MlErrorKind::Type,
            "Thread.Thread.equal",
            "expected two thread handles",
        ));
    };
    if left.downcast_host_object::<VmThread>().is_none()
        || right.downcast_host_object::<VmThread>().is_none()
    {
        return Err(vm.error(
            MlErrorKind::Type,
            "Thread.Thread.equal",
            "expected VM-owned thread handles",
        ));
    }
    vm.get_host_object(left.as_host_object().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "Thread.Thread.equal", "missing left thread identity")
    })?)?;
    vm.get_host_object(right.as_host_object().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "Thread.Thread.equal", "missing right thread identity")
    })?)?;
    Ok(Value::bool(left.is_same_object(right)))
}

fn test_interrupt(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    vm.check_stop()?;
    Ok(Value::unit())
}

fn is_active(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let thread = &args[0];
    let id = thread.as_host_object().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "Thread.Thread.isActive", "expected thread handle")
    })?;
    vm.get_host_object(id)?;
    if thread.downcast_host_object::<VmThread>().is_none() {
        return Err(vm.error(
            MlErrorKind::Type,
            "Thread.Thread.isActive",
            "expected thread handle",
        ));
    }
    Ok(Value::bool(vm.thread_self.as_ref().is_some_and(|current| current.is_same_object(thread))))
}
fn unavailable_fork(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    Err(vm.error(
        MlErrorKind::HostPermission,
        "Thread.Thread.fork",
        "VM has no lifecycle-managed concurrent SML worker",
    ))
}
fn unavailable_interrupt(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    Err(vm.error(
        MlErrorKind::HostPermission,
        "Thread.Thread.interrupt",
        "VM has no lifecycle-managed target thread",
    ))
}
fn unavailable_processor_count(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    Err(vm.error(
        MlErrorKind::HostPermission,
        "Thread.Thread.numProcessors",
        "no approved processor-count snapshot is available to this VM",
    ))
}
fn unavailable_physical_count(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    Err(vm.error(
        MlErrorKind::HostPermission,
        "Thread.Thread.numPhysicalProcessors",
        "no approved physical-processor-count snapshot is available to this VM",
    ))
}
fn clear_mutable_bit(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    if !matches!(
        args.first().map(|value| &*value.0),
        Some(ValueData::Reference(_) | ValueData::WeakReference(_))
    ) {
        return Err(vm.error(
            MlErrorKind::Type,
            "RunCall.clearMutableBit",
            "expected ML reference",
        ));
    }
    // Rust GC rescans every reachable reference. There is no mutable-bit cache to invalidate.
    vm.check_stop()?;
    Ok(Value::unit())
}

fn cast_thread(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let value = &args[0];
    if value.downcast_host_object::<VmThread>().is_none() {
        return Err(vm.error(
            MlErrorKind::Type,
            "RunCall.unsafeCast",
            "only VM-owned thread flags handle is approved",
        ));
    }
    vm.get_host_object(value.as_host_object().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "RunCall.unsafeCast", "missing thread identity")
    })?)?;
    Ok(value.clone())
}

fn thread_flag<'a>(
    vm: &Vm,
    value: &'a Value,
    offset: &Value,
    operation: &str,
) -> Result<&'a VmThread, MlError> {
    if offset.as_word() != Some(FLAGS_WORD_OFFSET) {
        return Err(vm.error(
            MlErrorKind::HostPermission,
            operation,
            "only the fixed thread flags field is accessible",
        ));
    }
    vm.get_host_object(
        value
            .as_host_object()
            .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "missing thread identity"))?,
    )?;
    value.downcast_host_object::<VmThread>().ok_or_else(|| {
        vm.error(MlErrorKind::Type, operation, "expected VM-owned thread flags handle")
    })
}

fn load_word(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [thread, offset] = super::fields(vm, &args[0], 2, "RunCall.loadWord")? else {
        return Err(vm.error(
            MlErrorKind::Type,
            "RunCall.loadWord",
            "expected thread and fixed offset",
        ));
    };
    Ok(Value::word(thread_flag(vm, thread, offset, "RunCall.loadWord")?.flags.get()))
}

fn store_word(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [thread, offset, value] = super::fields(vm, &args[0], 3, "RunCall.storeWord")? else {
        return Err(vm.error(
            MlErrorKind::Type,
            "RunCall.storeWord",
            "expected thread, offset and word",
        ));
    };
    let value = value
        .as_word()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "RunCall.storeWord", "expected word flags"))?;
    thread_flag(vm, thread, offset, "RunCall.storeWord")?.flags.set(value);
    Ok(Value::unit())
}
