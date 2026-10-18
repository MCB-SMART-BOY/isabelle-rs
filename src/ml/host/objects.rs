//! Typed logical values bound to one VM and one live build.
//!
//! This store preserves kernel objects; it neither constructs theorems nor
//! restores authority from ML records, serials, or serialized diagnostics.
use std::rc::Rc;

use isabelle_kernel::{CTerm, CType, KernelThm, ProofContext, TrustedTheory};
use thiserror::Error;

use super::lifecycle::{BuildLifecycle, LifecycleError, TaskLease};
use crate::ml::{MlError, Value, Vm};

/// The logical category of an opaque ML host value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectKind {
    CertifiedType,
    CertifiedTerm,
    Theorem,
    Theory,
    ProofContext,
}

pub(super) mod sealed {
    pub trait Sealed {}
}

/// Only sealed, checked logical values and their immutable host contexts enter this store.
pub trait LogicalObject: sealed::Sealed + 'static {
    const KIND: ObjectKind;
}

macro_rules! logical_object {
    ($ty:ty, $kind:ident) => {
        impl sealed::Sealed for $ty {}
        impl LogicalObject for $ty {
            const KIND: ObjectKind = ObjectKind::$kind;
        }
    };
}

logical_object!(CType, CertifiedType);
logical_object!(CTerm, CertifiedTerm);
logical_object!(KernelThm, Theorem);
logical_object!(TrustedTheory, Theory);
logical_object!(ProofContext, ProofContext);

/// A rejected lookup never returns a logical payload.
#[derive(Debug, Error)]
pub enum ObjectError {
    /// The VM does not share the build's cancellation domain.
    #[error("logical object operation uses a foreign VM or stop domain")]
    ForeignRuntime,
    /// A genuine handle belongs to a different build.
    #[error("logical object lookup uses a foreign build")]
    ForeignBuild,
    /// The ML value is not an opaque host object.
    #[error("logical object lookup expected {expected:?}, received a non-host ML value")]
    NotHostObject { expected: ObjectKind },
    /// A host value has a different payload category, or is not a logical value.
    #[error("logical object lookup expected {expected:?}, received a different host object")]
    WrongKind { expected: ObjectKind },
    /// Cancellation, an invalid phase, or a foreign lease revoked access.
    #[error("logical object lifecycle check failed: {0}")]
    Lifecycle(#[from] LifecycleError),
    /// The VM rejected a foreign, expired, or stale handle.
    #[error("logical object VM check failed: {0}")]
    Vm(#[from] MlError),
    /// Revocation failed as well; retain the original boundary failure and cleanup cause.
    #[error("{cause}; failed to revoke logical build: {cancellation}")]
    Revocation {
        #[source]
        cause: Box<ObjectError>,
        cancellation: LifecycleError,
    },
}

struct Envelope {
    lifecycle: BuildLifecycle,
    value: Rc<dyn std::any::Any>,
}

/// A typed view over the VM's existing runtime/generation checked object table.
///
/// The store owns no independent handle allocator and cannot revive expired
/// values. Every operation requires a live lease from the same build.
pub struct ObjectStore {
    runtime: u64,
    lifecycle: BuildLifecycle,
}

impl ObjectStore {
    pub fn new(vm: &Vm, lifecycle: BuildLifecycle) -> Result<Self, ObjectError> {
        vm.check_stop()?;
        if !lifecycle.matches_stop_handle(&vm.stop_handle()) {
            return Err(ObjectError::ForeignRuntime);
        }
        Ok(Self { runtime: vm.runtime_id, lifecycle })
    }

    pub fn insert<T: LogicalObject>(
        &self,
        vm: &mut Vm,
        lease: &TaskLease,
        value: T,
    ) -> Result<Value, ObjectError> {
        self.check_access(vm, lease)?;
        let envelope = Envelope { lifecycle: self.lifecycle.clone(), value: Rc::new(value) };
        vm.insert_host_object(Rc::new(envelope)).map_err(|error| self.revoke(vm, error.into()))
    }

    pub fn get<T: LogicalObject>(
        &self,
        vm: &Vm,
        lease: &TaskLease,
        value: &Value,
    ) -> Result<Rc<T>, ObjectError> {
        self.check_access(vm, lease)?;
        let id = value.as_host_object().ok_or(ObjectError::NotHostObject { expected: T::KIND })?;
        let object = vm.get_host_object(id).map_err(|error| self.revoke(vm, error.into()))?;
        let envelope = object
            .downcast_ref::<Envelope>()
            .ok_or(ObjectError::WrongKind { expected: T::KIND })?;
        if !self.lifecycle.shares_build(&envelope.lifecycle) {
            return Err(self.revoke(vm, ObjectError::ForeignBuild));
        }
        Rc::clone(&envelope.value)
            .downcast::<T>()
            .map_err(|_| ObjectError::WrongKind { expected: T::KIND })
    }

    fn check_access(&self, vm: &Vm, lease: &TaskLease) -> Result<(), ObjectError> {
        vm.check_stop().map_err(|error| self.revoke(vm, error.into()))?;
        if vm.runtime_id != self.runtime || !self.lifecycle.matches_stop_handle(&vm.stop_handle()) {
            return Err(self.revoke(vm, ObjectError::ForeignRuntime));
        }
        self.lifecycle.check_task(lease).map_err(|error| self.revoke(vm, error.into()))?;
        Ok(())
    }

    fn revoke(&self, vm: &Vm, cause: ObjectError) -> ObjectError {
        vm.request_stop();
        match self.lifecycle.cancel(cause.to_string()) {
            Ok(()) => cause,
            Err(cancellation) => ObjectError::Revocation { cause: Box::new(cause), cancellation },
        }
    }
}
