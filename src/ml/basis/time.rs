//! Time values are VM-owned and clock/sleep effects use the restricted leased bridge.
use super::{MlError, MlErrorKind, Value, Vm, function, typ};
use std::rc::Rc;
use std::time::{Duration, SystemTime};

#[derive(Debug)]
struct NativeTime(i128);
#[derive(Debug)]
struct NativeTimer(i128);
const NANOS_PER_SECOND: i128 = 1_000_000_000;

pub(super) fn install(vm: &mut Vm) {
    // A fresh VM has no stop request and no user-defined Time type during Basis installation.
    vm.register_host_type("Time.time", 0, false).expect("fresh VM Basis Time type");
    vm.register_host_type("Timer.real_timer", 0, false).expect("fresh VM Basis real timer type");
    let time = typ("Time.time");
    let real = typ("real");
    let unit = typ("unit");
    vm.register_pure("Time.fromReal", &[], function(real.clone(), time.clone()), 1, from_real);
    vm.register_pure("Time.toReal", &[], function(time.clone(), real), 1, to_real);
    vm.register_pure("Time.now", &[], function(unit.clone(), time.clone()), 1, now);
    vm.register_pure("OS.Process.sleep", &[], function(time.clone(), unit), 1, sleep);
    vm.register_pure("Time.toString", &[], function(time.clone(), typ("string")), 1, to_string);
    vm.register_pure(
        "Timer.startRealTimer",
        &[],
        function(typ("unit"), typ("Timer.real_timer")),
        1,
        start_real_timer,
    );
    vm.register_pure(
        "Timer.checkRealTimer",
        &[],
        function(typ("Timer.real_timer"), time.clone()),
        1,
        check_real_timer,
    );
    vm.register_pure(
        "Time.compare",
        &[],
        function(super::pair(time.clone(), time.clone()), typ("order")),
        1,
        compare,
    );
    for (name, callback) in [("Time.+", add as super::NativeFunction), ("Time.-", subtract)] {
        vm.register_pure(
            name,
            &[],
            function(super::pair(time.clone(), time.clone()), time.clone()),
            1,
            callback,
        );
    }
    vm.register_pure(
        "Time.<",
        &[],
        function(super::pair(time.clone(), time), typ("bool")),
        1,
        less,
    );
    // A fresh VM can allocate the first host object before evaluation can request stop.
    let zero = vm.insert_host_object(Rc::new(NativeTime(0))).expect("fresh VM Basis Time zero");
    vm.register_value("Time.zeroTime", super::TypeScheme::mono(typ("Time.time")), zero);
}

fn time_value<'a>(vm: &Vm, value: &'a Value, operation: &str) -> Result<&'a NativeTime, MlError> {
    let id = value
        .as_host_object()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected Time.time"))?;
    vm.get_host_object(id)?;
    value
        .downcast_host_object::<NativeTime>()
        .ok_or_else(|| vm.error(MlErrorKind::Type, operation, "expected Time.time"))
}
fn create_time(vm: &mut Vm, nanos: i128) -> Result<Value, MlError> {
    vm.insert_host_object(Rc::new(NativeTime(nanos)))
}
fn from_real(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let seconds = args
        .first()
        .and_then(Value::as_real)
        .ok_or_else(|| vm.error(MlErrorKind::Type, "Time.fromReal", "expected real seconds"))?;
    let nanos = seconds * NANOS_PER_SECOND as f64;
    if !nanos.is_finite() || nanos <= i128::MIN as f64 || nanos >= i128::MAX as f64 {
        return Err(vm.raise_builtin("Overflow"));
    }
    create_time(vm, nanos.round() as i128)
}
fn to_real(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(value) = args.first() else {
        return Err(vm.error(MlErrorKind::Type, "Time.toReal", "expected Time.time"));
    };
    let nanos = time_value(vm, value, "Time.toReal")?.0;
    Ok(Value::real(nanos as f64 / NANOS_PER_SECOND as f64))
}
fn to_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let nanos = args
        .first()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "Time.toString", "expected Time.time"))
        .and_then(|value| unix_nanos(vm, value, "Time.toString"))?;
    let millis = (nanos.unsigned_abs() + 500_000) / 1_000_000;
    let sign = if nanos < 0 { "~" } else { "" };
    Ok(Value::text(format!("{sign}{}.{:03}", millis / 1_000, millis % 1_000)))
}
fn start_real_timer(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let instant = unix_now_nanos(vm, "Timer.startRealTimer")?;
    vm.insert_host_object(Rc::new(NativeTimer(instant)))
}
fn check_real_timer(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let timer = args.first().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "Timer.checkRealTimer", "expected Timer.real_timer")
    })?;
    let id = timer.as_host_object().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "Timer.checkRealTimer", "expected Timer.real_timer")
    })?;
    vm.get_host_object(id)?;
    let start = timer
        .downcast_host_object::<NativeTimer>()
        .ok_or_else(|| {
            vm.error(MlErrorKind::Type, "Timer.checkRealTimer", "expected Timer.real_timer")
        })?
        .0;
    let now = unix_now_nanos(vm, "Timer.checkRealTimer")?;
    let elapsed = now.checked_sub(start).ok_or_else(|| vm.raise_builtin("Overflow"))?;
    if elapsed < 0 {
        return Err(vm.error(
            MlErrorKind::HostFailure,
            "Timer.checkRealTimer",
            "approved clock moved backwards",
        ));
    }
    create_time(vm, elapsed)
}

pub(super) fn unix_nanos(vm: &Vm, value: &Value, operation: &str) -> Result<i128, MlError> {
    Ok(time_value(vm, value, operation)?.0)
}
pub(super) fn unix_now_nanos(vm: &mut Vm, operation: &str) -> Result<i128, MlError> {
    let host = vm.bootstrap_host.as_ref().cloned().ok_or_else(|| {
        vm.error(MlErrorKind::HostPermission, operation, "no leased bootstrap clock installed")
    })?;
    let instant =
        host.read_clock(vm).map_err(|error| vm.host_io_failure(operation, "clock", error))?;
    match instant.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(duration) => i128::try_from(duration.as_nanos()),
        Err(error) => i128::try_from(error.duration().as_nanos()).map(|duration| -duration),
    }
    .map_err(|error| vm.error(MlErrorKind::HostFailure, operation, format!("clock range: {error}")))
}
fn now(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let nanos = unix_now_nanos(vm, "Time.now")?;
    create_time(vm, nanos)
}
fn sleep(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(value) = args.first() else {
        return Err(vm.error(MlErrorKind::Type, "OS.Process.sleep", "expected Time.time"));
    };
    let nanos = time_value(vm, value, "OS.Process.sleep")?.0;
    if nanos < 0 {
        return Err(vm.raise_builtin("Size"));
    }
    let nanos = u128::try_from(nanos).map_err(|_| vm.raise_builtin("Overflow"))?;
    let seconds = u64::try_from(nanos / NANOS_PER_SECOND as u128)
        .map_err(|_| vm.raise_builtin("Overflow"))?;
    let duration = Duration::new(seconds, (nanos % NANOS_PER_SECOND as u128) as u32);
    let host = vm.bootstrap_host.as_ref().cloned().ok_or_else(|| {
        vm.error(
            MlErrorKind::HostPermission,
            "OS.Process.sleep",
            "no leased bootstrap host installed",
        )
    })?;
    host.sleep(vm, duration)
        .map_err(|error| vm.host_io_failure("OS.Process.sleep", "timer", error))?;
    Ok(Value::unit())
}
fn pair(vm: &Vm, args: &[Value], operation: &str) -> Result<(i128, i128), MlError> {
    let [left, right] = super::fields(vm, &args[0], 2, operation)? else {
        return Err(vm.error(MlErrorKind::Type, operation, "expected pair of Time.time"));
    };
    Ok((time_value(vm, left, operation)?.0, time_value(vm, right, operation)?.0))
}
fn add(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = pair(vm, args, "Time.+")?;
    let nanos = left.checked_add(right).ok_or_else(|| vm.raise_builtin("Overflow"))?;
    create_time(vm, nanos)
}
fn subtract(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = pair(vm, args, "Time.-")?;
    let nanos = left.checked_sub(right).ok_or_else(|| vm.raise_builtin("Overflow"))?;
    create_time(vm, nanos)
}
impl Vm {
    pub(in crate::ml) fn compare_time_values(
        &self,
        left: &Value,
        right: &Value,
    ) -> Result<std::cmp::Ordering, MlError> {
        let left = time_value(self, left, "compare Time.time")?.0;
        let right = time_value(self, right, "compare Time.time")?.0;
        Ok(left.cmp(&right))
    }
}

fn compare(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = pair(vm, args, "Time.compare")?;
    let order = vm.basis_order.as_ref().ok_or_else(|| {
        vm.error(MlErrorKind::HostFailure, "Time.compare", "Basis order constructors missing")
    })?;
    Ok(order[match left.cmp(&right) {
        std::cmp::Ordering::Less => 0,
        std::cmp::Ordering::Equal => 1,
        std::cmp::Ordering::Greater => 2,
    }]
    .clone())
}
fn less(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = pair(vm, args, "Time.<")?;
    Ok(Value::bool(left < right))
}
