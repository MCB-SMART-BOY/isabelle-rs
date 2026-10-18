//! VM-local synchronization objects used by the original Isabelle thread wrappers.
use super::{MlError, MlErrorKind, Value, Vm, function, pair, typ};
use std::rc::Rc;
use std::sync::{Condvar, Mutex, MutexGuard};
use std::thread::ThreadId;
use std::time::Duration;

const WAIT_CHECK_INTERVAL: Duration = Duration::from_millis(20);

struct NativeMutex {
    owner: Mutex<Option<ThreadId>>,
    ready: Condvar,
}
struct NativeCondition {
    generation: Mutex<u64>,
    ready: Condvar,
}

pub(super) fn install(vm: &mut Vm) {
    vm.register_host_type("Thread.Mutex.mutex", 0, false).expect("fresh VM mutex type");
    vm.register_host_type("Thread.ConditionVar.conditionVar", 0, false)
        .expect("fresh VM condition type");
    let unit = typ("unit");
    let mutex = typ("Thread.Mutex.mutex");
    let condition = typ("Thread.ConditionVar.conditionVar");
    vm.register_pure(
        "Thread.Mutex.mutex",
        &[],
        function(unit.clone(), mutex.clone()),
        1,
        make_mutex,
    );
    vm.register_pure("Thread.Mutex.lock", &[], function(mutex.clone(), unit.clone()), 1, lock);
    vm.register_pure(
        "Thread.Mutex.trylock",
        &[],
        function(mutex.clone(), typ("bool")),
        1,
        try_lock,
    );
    vm.register_pure("Thread.Mutex.unlock", &[], function(mutex.clone(), unit.clone()), 1, unlock);
    vm.register_pure(
        "Thread.ConditionVar.conditionVar",
        &[],
        function(unit.clone(), condition.clone()),
        1,
        make_condition,
    );
    vm.register_pure(
        "Thread.ConditionVar.signal",
        &[],
        function(condition.clone(), unit.clone()),
        1,
        signal,
    );
    vm.register_pure(
        "Thread.ConditionVar.broadcast",
        &[],
        function(condition.clone(), unit.clone()),
        1,
        broadcast,
    );
    vm.register_pure(
        "Thread.ConditionVar.wait",
        &[],
        function(pair(condition.clone(), mutex.clone()), unit),
        1,
        wait,
    );
    vm.register_pure(
        "Thread.ConditionVar.waitUntil",
        &[],
        function(super::triple(condition, mutex, typ("Time.time")), typ("bool")),
        1,
        wait_until,
    );
}

fn synchronization_error(vm: &Vm, operation: &str, cause: &str) -> MlError {
    vm.error(MlErrorKind::HostFailure, operation, cause)
}
fn lock_state<'a>(
    vm: &Vm,
    mutex: &'a NativeMutex,
    operation: &str,
) -> Result<MutexGuard<'a, Option<ThreadId>>, MlError> {
    mutex.owner.lock().map_err(|error| {
        synchronization_error(vm, operation, &format!("VM mutex poisoned: {error}"))
    })
}
fn mutex_value<'a>(vm: &Vm, value: &'a Value, operation: &str) -> Result<&'a NativeMutex, MlError> {
    let id = value
        .as_host_object()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected mutex"))?;
    vm.get_host_object(id)?;
    value
        .downcast_host_object::<NativeMutex>()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected mutex"))
}
fn condition_value<'a>(
    vm: &Vm,
    value: &'a Value,
    operation: &str,
) -> Result<&'a NativeCondition, MlError> {
    let id = value
        .as_host_object()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected condition"))?;
    vm.get_host_object(id)?;
    value
        .downcast_host_object::<NativeCondition>()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected condition"))
}
fn make_mutex(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    vm.insert_host_object(Rc::new(NativeMutex { owner: Mutex::new(None), ready: Condvar::new() }))
}
fn make_condition(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    vm.insert_host_object(Rc::new(NativeCondition {
        generation: Mutex::new(0),
        ready: Condvar::new(),
    }))
}
fn lock(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let mutex = mutex_value(vm, &args[0], "Thread.Mutex.lock")?;
    lock_mutex(vm, mutex, "Thread.Mutex.lock")?;
    Ok(Value::unit())
}
fn try_lock(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let mutex = mutex_value(vm, &args[0], "Thread.Mutex.trylock")?;
    let mut owner = lock_state(vm, mutex, "Thread.Mutex.trylock")?;
    if owner.is_some() {
        return Ok(Value::bool(false));
    }
    *owner = Some(std::thread::current().id());
    Ok(Value::bool(true))
}
fn unlock(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let mutex = mutex_value(vm, &args[0], "Thread.Mutex.unlock")?;
    release(vm, mutex, "Thread.Mutex.unlock")?;
    Ok(Value::unit())
}
fn release(vm: &Vm, mutex: &NativeMutex, operation: &str) -> Result<(), MlError> {
    let mut owner = lock_state(vm, mutex, operation)?;
    if *owner != Some(std::thread::current().id()) {
        return Err(vm.error(
            MlErrorKind::Type,
            operation,
            "current thread does not hold this mutex",
        ));
    }
    *owner = None;
    mutex.ready.notify_one();
    Ok(())
}
fn notify(
    vm: &mut Vm,
    args: &[Value],
    operation: &str,
    is_broadcast: bool,
) -> Result<Value, MlError> {
    let condition = condition_value(vm, &args[0], operation)?;
    let mut generation = condition.generation.lock().map_err(|error| {
        synchronization_error(vm, operation, &format!("condition poisoned: {error}"))
    })?;
    *generation = generation.wrapping_add(1);
    if is_broadcast {
        condition.ready.notify_all();
    } else {
        condition.ready.notify_one();
    }
    Ok(Value::unit())
}
fn signal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    notify(vm, args, "Thread.ConditionVar.signal", false)
}
fn broadcast(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    notify(vm, args, "Thread.ConditionVar.broadcast", true)
}
fn wait(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [condition, mutex] = super::fields(vm, &args[0], 2, "Thread.ConditionVar.wait")? else {
        return Err(vm.error(
            MlErrorKind::Type,
            "Thread.ConditionVar.wait",
            "expected condition and mutex",
        ));
    };
    let condition = condition_value(vm, condition, "Thread.ConditionVar.wait")?;
    let mutex = mutex_value(vm, mutex, "Thread.ConditionVar.wait")?;
    let _ = wait_for_signal(vm, condition, mutex, "Thread.ConditionVar.wait", None)?;
    Ok(Value::unit())
}
fn wait_until(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [condition, mutex, deadline] =
        super::fields(vm, &args[0], 3, "Thread.ConditionVar.waitUntil")?
    else {
        return Err(vm.error(
            MlErrorKind::Type,
            "Thread.ConditionVar.waitUntil",
            "expected condition, mutex and deadline",
        ));
    };
    let deadline = super::time::unix_nanos(vm, deadline, "Thread.ConditionVar.waitUntil")?;
    let condition = condition_value(vm, condition, "Thread.ConditionVar.waitUntil")?;
    let mutex = mutex_value(vm, mutex, "Thread.ConditionVar.waitUntil")?;
    Ok(Value::bool(wait_for_signal(
        vm,
        condition,
        mutex,
        "Thread.ConditionVar.waitUntil",
        Some(deadline),
    )?))
}
fn wait_for_signal(
    vm: &mut Vm,
    condition: &NativeCondition,
    mutex: &NativeMutex,
    operation: &str,
    deadline: Option<i128>,
) -> Result<bool, MlError> {
    let mut generation = condition.generation.lock().map_err(|error| {
        synchronization_error(vm, operation, &format!("condition poisoned: {error}"))
    })?;
    let original = *generation;
    release(vm, mutex, operation)?;
    let signaled = loop {
        vm.check_stop()?;
        if *generation != original {
            break true;
        }
        if let Some(deadline) = deadline {
            let now = super::time::unix_now_nanos(vm, operation)?;
            if now >= deadline {
                break false;
            }
        }
        let (next, _) = condition
            .ready
            .wait_timeout(generation, WAIT_CHECK_INTERVAL)
            .map_err(|error| synchronization_error(vm, operation, &format!("wait: {error}")))?;
        generation = next;
    };
    drop(generation);
    lock_mutex(vm, mutex, operation)?;
    Ok(signaled)
}
fn lock_mutex(vm: &Vm, mutex: &NativeMutex, operation: &str) -> Result<(), MlError> {
    let mut owner = lock_state(vm, mutex, operation)?;
    while let Some(holder) = *owner {
        vm.check_stop()?;
        if holder == std::thread::current().id() {
            return Err(synchronization_error(vm, operation, "recursive lock would deadlock"));
        }
        let (next, _) = mutex
            .ready
            .wait_timeout(owner, WAIT_CHECK_INTERVAL)
            .map_err(|error| synchronization_error(vm, operation, &format!("wait: {error}")))?;
        owner = next;
    }
    vm.check_stop()?;
    *owner = Some(std::thread::current().id());
    Ok(())
}
