//! One-shot, registry-local request IDs and independently cancellable service calls.
//! The registry definitions never mutate; only transient request accounting lives here.
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use super::PluginReply;
use crate::ml::host::lifecycle::{LifecycleError, TaskLease};

/// Opaque and unforgeable across distinct build registries, even with the same serial.
#[derive(Clone)]
pub struct InvocationId {
    domain: Arc<()>,
    serial: u64,
}
impl InvocationId {
    pub fn serial(&self) -> u64 {
        self.serial
    }
}
impl std::fmt::Debug for InvocationId {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("InvocationId").field("serial", &self.serial).finish_non_exhaustive()
    }
}
impl PartialEq for InvocationId {
    fn eq(&self, other: &Self) -> bool {
        self.serial == other.serial && Arc::ptr_eq(&self.domain, &other.domain)
    }
}
impl Eq for InvocationId {}

#[derive(Debug, thiserror::Error)]
pub enum InvocationError {
    /// A previously used or forged invocation ID may not be started twice.
    #[error("service request ID was not issued by this registry")]
    Unknown,
    /// Once one result is terminal, neither reuse nor subsequent cancellation can change it.
    #[error("service request has already started or completed")]
    AlreadyStarted,
    /// Build-local request IDs must never wrap around and be reused.
    #[error("build-local service request ID exhausted")]
    Exhausted,
    /// Issued-but-unfinished requests are capped by caller's immutable resource budget.
    #[error("live service requests exceed the configured budget")]
    Limit,
    /// Poisoned request accounting is fatal for the current build.
    #[error("service request state lock poisoned")]
    Poisoned,
}

#[derive(Debug, thiserror::Error)]
pub enum InvocationFinishError {
    #[error("finish plugin request: {0}")]
    State(#[from] InvocationError),
    #[error("complete plugin request lease: {0}")]
    Lifecycle(#[from] LifecycleError),
}
/// A per-request cancellation never revokes unrelated operations in the build.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CancelOutcome {
    /// The request belongs to another registry or was never issued.
    Unknown,
    /// The result or cancellation was already acknowledged.
    AlreadyFinished,
    /// The call is running and must acknowledge cancellation after joining its work.
    Requested,
    /// The queued call's lease is completed; the caller may now deliver interrupt.
    CancelledReady,
}

pub(super) enum StartOutcome {
    Running(TaskLease),
    CancelledReady,
}

enum Stage {
    Ready,
    Running,
    Finished,
}
struct CallState {
    stage: Stage,
    is_cancelled: bool,
    lease: Option<TaskLease>,
}

pub(super) struct ServiceCancellation {
    pub(super) name: String,
    state: Mutex<CallState>,
}
impl ServiceCancellation {
    fn new(name: &str, lease: TaskLease) -> Self {
        Self {
            name: name.to_owned(),
            state: Mutex::new(CallState {
                stage: Stage::Ready,
                is_cancelled: false,
                lease: Some(lease),
            }),
        }
    }
    pub(super) fn start(&self) -> Result<StartOutcome, InvocationError> {
        let mut state = self.state.lock().map_err(|_| InvocationError::Poisoned)?;
        if matches!(state.stage, Stage::Finished) && state.is_cancelled {
            return Ok(StartOutcome::CancelledReady);
        }
        if !matches!(state.stage, Stage::Ready) {
            return Err(InvocationError::AlreadyStarted);
        }
        let lease = state.lease.take().ok_or(InvocationError::Unknown)?;
        state.stage = Stage::Running;
        Ok(StartOutcome::Running(lease))
    }
    pub(super) fn is_cancelled(&self) -> Result<bool, InvocationError> {
        Ok(self.state.lock().map_err(|_| InvocationError::Poisoned)?.is_cancelled)
    }
    pub(super) fn cancel(&self) -> Result<CancelOutcome, InvocationFinishError> {
        let mut state = self.state.lock().map_err(|_| InvocationError::Poisoned)?;
        match state.stage {
            Stage::Finished => Ok(CancelOutcome::AlreadyFinished),
            Stage::Running => {
                state.is_cancelled = true;
                Ok(CancelOutcome::Requested)
            },
            Stage::Ready => {
                state.is_cancelled = true;
                let lease = state.lease.take().ok_or(InvocationError::Unknown)?;
                let completed = lease.complete();
                state.stage = Stage::Finished;
                completed?;
                Ok(CancelOutcome::CancelledReady)
            },
        }
    }
    pub(super) fn settle(&self, reply: PluginReply) -> Result<PluginReply, InvocationFinishError> {
        let mut state = self.state.lock().map_err(|_| InvocationError::Poisoned)?;
        if !matches!(state.stage, Stage::Running) {
            return Err(InvocationError::AlreadyStarted.into());
        }
        state.stage = Stage::Finished;
        if state.is_cancelled { Ok(PluginReply::Interrupt) } else { Ok(reply) }
    }
    /// Only the runner owns the live lease after start; a separate cancellation
    /// sets its flag but may not release or retire the running call's lease.
    pub(super) fn abort(
        &self,
        running_lease: Option<TaskLease>,
    ) -> Result<bool, InvocationFinishError> {
        let mut state = self.state.lock().unwrap_or_else(|poisoned| {
            tracing::error!("recovering poisoned plugin request exclusively for lease cleanup");
            poisoned.into_inner()
        });
        if matches!(state.stage, Stage::Finished) {
            if let Some(lease) = running_lease
                && let Err(error) = lease.complete()
            {
                tracing::error!(error = %error, "complete already settled plugin reservation");
            }
            return Ok(true);
        }
        let Some(lease) = running_lease.or_else(|| state.lease.take()) else {
            if matches!(state.stage, Stage::Running) {
                state.is_cancelled = true;
                return Ok(false);
            }
            return Err(InvocationError::Unknown.into());
        };
        let completed = lease.complete();
        state.stage = Stage::Finished;
        if let Err(error) = completed {
            tracing::error!(error = %error, "aborted plugin lease completed after build stop");
        }
        Ok(true)
    }
}

struct TrackerState {
    next_serial: u64,
    pending: BTreeMap<u64, Arc<ServiceCancellation>>,
}

pub(super) struct InvocationTracker {
    domain: Arc<()>,
    state: Mutex<TrackerState>,
    max_active: usize,
}
impl InvocationTracker {
    pub(super) fn new(max_active: usize) -> Self {
        Self {
            domain: Arc::new(()),
            max_active,
            state: Mutex::new(TrackerState { next_serial: 0, pending: BTreeMap::new() }),
        }
    }
    pub(super) fn issue(
        &self,
        name: &str,
        reserved: &mut Option<TaskLease>,
    ) -> Result<InvocationId, InvocationError> {
        let mut state = self.state.lock().map_err(|_| InvocationError::Poisoned)?;
        if state.pending.len() >= self.max_active {
            return Err(InvocationError::Limit);
        }
        let serial = state.next_serial.checked_add(1).ok_or(InvocationError::Exhausted)?;
        let lease = reserved.take().ok_or(InvocationError::Unknown)?;
        let request = Arc::new(ServiceCancellation::new(name, lease));
        state.pending.insert(serial, request);
        state.next_serial = serial;
        Ok(InvocationId { domain: Arc::clone(&self.domain), serial })
    }
    pub(super) fn lookup(
        &self,
        id: &InvocationId,
    ) -> Result<Option<Arc<ServiceCancellation>>, InvocationError> {
        if !Arc::ptr_eq(&self.domain, &id.domain) {
            return Ok(None);
        }
        Ok(self
            .state
            .lock()
            .map_err(|_| InvocationError::Poisoned)?
            .pending
            .get(&id.serial)
            .cloned())
    }
    pub(super) fn retire(&self, id: &InvocationId) -> Result<(), InvocationError> {
        let mut state = self.state.lock().map_err(|_| InvocationError::Poisoned)?;
        if !Arc::ptr_eq(&self.domain, &id.domain) || state.pending.remove(&id.serial).is_none() {
            return Err(InvocationError::Unknown);
        }
        Ok(())
    }
    pub(super) fn pending_count(&self) -> Result<usize, InvocationError> {
        Ok(self.state.lock().map_err(|_| InvocationError::Poisoned)?.pending.len())
    }
    pub(super) fn owns(&self, id: &InvocationId) -> bool {
        Arc::ptr_eq(&self.domain, &id.domain)
    }
    pub(super) fn abort_all(&self) -> Result<(), InvocationFinishError> {
        let pending = {
            let mut state = self.state.lock().unwrap_or_else(|poisoned| {
                tracing::error!(
                    "recovering poisoned request tracker exclusively for lease cleanup"
                );
                poisoned.into_inner()
            });
            std::mem::take(&mut state.pending)
        };
        let mut first_error = None;
        for (_, request) in pending {
            match request.abort(None) {
                Ok(true) => {},
                Ok(false) => tracing::error!("registry teardown found a running plugin worker"),
                Err(error) => {
                    if first_error.is_none() {
                        first_error = Some(error);
                    }
                },
            }
        }
        match first_error {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}
