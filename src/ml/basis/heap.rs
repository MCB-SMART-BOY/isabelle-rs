//! Heap operations that the native VM can perform without Poly/ML image or telemetry claims.
use super::{MlError, MlErrorKind, Value, Vm, function, typ};

pub(super) fn install(vm: &mut Vm) {
    vm.register_pure("PolyML.fullGC", &[], function(typ("unit"), typ("unit")), 1, full_gc);
}

fn full_gc(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    vm.check_stop()?;
    if !args.first().is_some_and(Value::is_unit) {
        return Err(vm.error(MlErrorKind::Type, "PolyML.fullGC", "expected unit"));
    }
    vm.collect_garbage()?;
    Ok(Value::unit())
}
