//! Poly/ML weak option references, cleared only during VM garbage collection.
use super::{MlError, MlErrorKind, Value, ValueData, Vm, container, function, var};
use std::cell::RefCell;
use std::rc::Rc;

pub(super) fn install(vm: &mut Vm) {
    let reference = container("ref", var(1));
    let optional_reference = container("option", reference);
    vm.register_pure(
        "Weak.weak",
        &[1],
        function(optional_reference.clone(), container("ref", optional_reference)),
        1,
        make_weak,
    );
}

fn make_weak(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    vm.check_stop()?;
    let Some(initial) = args.first() else {
        return Err(vm.error(MlErrorKind::Type, "Weak.weak", "missing option reference"));
    };
    vm.validate_weak_contents(initial, "Weak.weak")?;
    Ok(vm.track_value(Value(Rc::new(ValueData::WeakReference(RefCell::new(initial.clone()))))))
}

impl Vm {
    pub(in crate::ml) fn validate_weak_contents(
        &self,
        value: &Value,
        operation: &str,
    ) -> Result<(), MlError> {
        match &*value.0 {
            ValueData::Constructor { stamp, argument: None, .. }
                if *stamp == self.option_none_stamp =>
            {
                Ok(())
            },
            ValueData::Constructor { stamp, argument: Some(referent), .. }
                if *stamp == self.option_some_stamp
                    && matches!(
                        &*referent.0,
                        ValueData::Reference(_) | ValueData::WeakReference(_)
                    ) =>
            {
                Ok(())
            },
            _ => Err(self.error(
                MlErrorKind::Type,
                operation,
                "expected SOME of a VM reference or NONE",
            )),
        }
    }
}
