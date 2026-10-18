//! Poly/ML bootstrap statistics declarations without inventing unavailable host metrics.
use super::{MlError, MlErrorKind, Value, ValueData, Vm, function, pair, typ};
use std::rc::Rc;

pub(in crate::ml) const USER_COUNTER_SLOTS: usize = 8;

pub(super) fn install(vm: &mut Vm) {
    let integer = typ("int");
    let unit = typ("unit");
    let gc_state = typ("PolyML.Statistics.gcState");
    vm.type_environment.register_type("PolyML.Statistics.gcState", 0, true);
    for name in ["MinorGC", "MajorGC", "GCSharing", "OtherState"] {
        let stamp = vm.fresh_identity();
        vm.register_value(
            &format!("PolyML.Statistics.{name}"),
            super::TypeScheme::mono(function(integer.clone(), gc_state.clone())),
            Value(Rc::new(ValueData::ConstructorFunction { stamp, name: name.to_owned() })),
        );
    }
    let stamp = vm.fresh_identity();
    vm.register_value(
        "PolyML.Statistics.MLCode",
        super::TypeScheme::mono(gc_state.clone()),
        Value(Rc::new(ValueData::Constructor { stamp, name: "MLCode".to_owned(), argument: None })),
    );
    vm.register_pure(
        "PolyML.Statistics.setUserCounter",
        &[],
        function(pair(integer.clone(), integer.clone()), unit.clone()),
        1,
        set_user_counter,
    );
    let mut fields = std::collections::BTreeMap::new();
    for field in [
        "gcFullGCs",
        "gcPartialGCs",
        "gcSharePasses",
        "sizeAllocation",
        "sizeAllocationFree",
        "sizeCode",
        "sizeHeap",
        "sizeHeapFreeLastFullGC",
        "sizeHeapFreeLastGC",
        "sizeStacks",
        "threadsInML",
        "threadsTotal",
        "threadsWaitCondVar",
        "threadsWaitIO",
        "threadsWaitMutex",
        "threadsWaitSignal",
    ] {
        fields.insert(field.to_owned(), integer.clone());
    }
    for field in [
        "timeGCReal",
        "timeGCSystem",
        "timeGCUser",
        "timeNonGCReal",
        "timeNonGCSystem",
        "timeNonGCUser",
    ] {
        fields.insert(field.to_owned(), typ("Time.time"));
    }
    fields.insert("userCounters".to_owned(), super::container("vector", integer.clone()));
    fields.insert("gcState".to_owned(), gc_state);
    let stats = super::Type::Record(fields, false);
    vm.register_pure(
        "PolyML.Statistics.getLocalStats",
        &[],
        function(unit.clone(), stats.clone()),
        1,
        unavailable_local_stats,
    );
    vm.register_pure(
        "PolyML.Statistics.getRemoteStats",
        &[],
        function(integer, stats),
        1,
        unavailable_remote_stats,
    );
    vm.type_environment.register_type("OS.Process.status", 0, true);
    vm.register_value(
        "OS.Process.success",
        super::TypeScheme::mono(typ("OS.Process.status")),
        Value::int(0),
    );
    vm.register_pure(
        "OS.Process.exit",
        &[1],
        function(typ("OS.Process.status"), super::var(1)),
        1,
        deny_process_exit,
    );
}

fn set_user_counter(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let [index, value] = super::fields(vm, &args[0], 2, "PolyML.Statistics.setUserCounter")? else {
        return Err(vm.error(
            MlErrorKind::Type,
            "PolyML.Statistics.setUserCounter",
            "expected int pair",
        ));
    };
    let index = index.as_int().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.Statistics.setUserCounter", "expected int index")
    })?;
    let value = value.as_int().ok_or_else(|| {
        vm.error(MlErrorKind::Type, "PolyML.Statistics.setUserCounter", "expected int counter")
    })?;
    let index = usize::try_from(index)
        .ok()
        .filter(|index| *index < USER_COUNTER_SLOTS)
        .ok_or_else(|| vm.raise_builtin("Subscript"))?;
    vm.user_counters[index] = value;
    Ok(Value::unit())
}
fn unavailable_local_stats(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    Err(vm.error(
        MlErrorKind::HostPermission,
        "PolyML.Statistics.getLocalStats",
        "full Poly/ML GC, CPU and allocation counters are not available in native VM authority",
    ))
}
fn unavailable_remote_stats(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    Err(vm.error(
        MlErrorKind::HostPermission,
        "PolyML.Statistics.getRemoteStats",
        "external process statistics require an ungranted process-inspection capability",
    ))
}
fn deny_process_exit(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    Err(vm.error(
        MlErrorKind::HostPermission,
        "OS.Process.exit",
        "native VM cannot terminate the supervisor process",
    ))
}
