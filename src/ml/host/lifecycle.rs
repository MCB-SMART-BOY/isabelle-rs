//! Supervisor-owned lifecycle barrier for one native ML build.
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;
use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

use super::publisher::BuildPublisher;
use crate::ml::{StopBarrierError, StopHandle};

const WORK_KIND_COUNT: usize = 6;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimePhase {
    Active,
    Draining,
    Closed,
    Succeeded,
    Cancelling,
    Failed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WorkKind {
    Evaluation,
    Future,
    Callback,
    Stream,
    Process,
    Proof,
}

impl WorkKind {
    const fn index(self) -> usize {
        match self {
            Self::Evaluation => 0,
            Self::Future => 1,
            Self::Callback => 2,
            Self::Stream => 3,
            Self::Process => 4,
            Self::Proof => 5,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PendingCounts([usize; WORK_KIND_COUNT]);

impl PendingCounts {
    pub fn count(self, kind: WorkKind) -> usize {
        self.0[kind.index()]
    }

    pub fn total(self) -> u128 {
        self.0.iter().map(|count| *count as u128).sum()
    }

    fn is_empty(self) -> bool {
        self.0.iter().all(|count| *count == 0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LifecycleErrorClass {
    Recoverable,
    Fatal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LifecycleErrorKind {
    /// A task from a different build cannot authorize this runtime's effects.
    WrongBuild,
    /// An operation was attempted outside the phase where it is legal.
    InvalidPhase,
    /// Registered work is still in flight; the caller may wait and retry.
    PendingWork,
    /// A supervisor cancellation irrevocably stopped this build.
    Cancelled,
    /// A work lease was dropped without being explicitly completed.
    AbandonedWork,
    /// A task counter or root identifier exceeded its representable range.
    Overflow,
    /// A synchronization lock was poisoned by a panic.
    Poisoned,
    /// The atomic no-replace filesystem publication failed; no registry is exposed.
    PublicationFailed,
}

#[derive(Debug)]
struct PoisonedLock(String);

impl fmt::Display for PoisonedLock {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(output, "lifecycle lock poisoned: {}", self.0)
    }
}

impl Error for PoisonedLock {}

#[derive(Debug)]
pub struct LifecycleError {
    pub kind: LifecycleErrorKind,
    pub class: LifecycleErrorClass,
    /// None means no trustworthy stage can be attributed (foreign lease or poisoned lock).
    pub stage: Option<RuntimePhase>,
    pub operation: &'static str,
    pub origin: String,
    pub cause: String,
    source: Option<Arc<dyn Error + Send + Sync>>,
}

impl LifecycleError {
    fn new(
        kind: LifecycleErrorKind,
        stage: RuntimePhase,
        operation: &'static str,
        origin: &str,
        cause: impl Into<String>,
    ) -> Self {
        let class = if kind == LifecycleErrorKind::PendingWork {
            LifecycleErrorClass::Recoverable
        } else {
            LifecycleErrorClass::Fatal
        };
        Self {
            kind,
            class,
            stage: Some(stage),
            operation,
            origin: origin.to_owned(),
            cause: cause.into(),
            source: None,
        }
    }

    fn wrong_build(origin: &str) -> Self {
        Self {
            kind: LifecycleErrorKind::WrongBuild,
            class: LifecycleErrorClass::Fatal,
            stage: None,
            operation: "check_task",
            origin: origin.to_owned(),
            cause: "task lease belongs to a different build".to_owned(),
            source: None,
        }
    }

    fn with_source(mut self, source: Arc<dyn Error + Send + Sync>) -> Self {
        self.source = Some(source);
        self
    }

    fn poisoned(operation: &'static str, origin: &str, cause: impl Into<String>) -> Self {
        let detail = cause.into();
        Self {
            kind: LifecycleErrorKind::Poisoned,
            class: LifecycleErrorClass::Fatal,
            stage: None,
            operation,
            origin: origin.to_owned(),
            cause: "cannot safely inspect lifecycle state".to_owned(),
            source: Some(Arc::new(PoisonedLock(detail))),
        }
    }

    fn publication_failed(source: io::Error) -> Self {
        Self {
            kind: LifecycleErrorKind::PublicationFailed,
            class: LifecycleErrorClass::Fatal,
            stage: Some(RuntimePhase::Closed),
            operation: "commit_publication",
            origin: "publisher".to_owned(),
            cause: "atomic no-replace rename failed".to_owned(),
            source: Some(Arc::new(source)),
        }
    }
}

impl fmt::Display for LifecycleError {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(output, "{} at {} ({:?}): {}", self.operation, self.origin, self.stage, self.cause)
    }
}

impl Error for LifecycleError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.source.as_deref().map(|source| source as &(dyn Error + 'static))
    }
}

struct State {
    phase: RuntimePhase,
    counts: PendingCounts,
    roots: BTreeMap<u64, usize>,
    next_root: u64,
    first_failure: Option<Arc<LifecycleError>>,
}

struct Inner {
    state: Mutex<State>,
    stopped: AtomicBool,
    stop: StopHandle,
}

impl Inner {
    fn request_stop(&self) {
        self.stopped.store(true, Ordering::Release);
        self.stop.request_stop();
    }

    fn lock(
        &self,
        operation: &'static str,
        origin: &str,
    ) -> Result<MutexGuard<'_, State>, LifecycleError> {
        let mut state = self.state.lock().map_err(|error| {
            self.request_stop();
            LifecycleError::poisoned(operation, origin, error.to_string())
        })?;
        if matches!(state.phase, RuntimePhase::Active | RuntimePhase::Draining)
            && !self.stopped.load(Ordering::Acquire)
            && self.stop.is_stop_requested()
        {
            record_failure_locked(
                self,
                &mut state,
                LifecycleErrorKind::Cancelled,
                operation,
                origin,
                "shared VM stop requested outside build lifecycle",
            );
        }
        Ok(state)
    }
}

#[derive(Clone)]
pub struct BuildLifecycle(Arc<Inner>);

#[derive(Clone)]
pub struct Cancellation(Arc<Inner>);

/// A live task in exactly one build. It cannot be cloned or moved to another build.
pub struct TaskLease {
    inner: Arc<Inner>,
    kind: WorkKind,
    root: u64,
    origin: String,
    is_live: bool,
}

impl BuildLifecycle {
    pub fn new(stop: StopHandle) -> Self {
        Self(Arc::new(Inner {
            state: Mutex::new(State {
                phase: RuntimePhase::Active,
                counts: PendingCounts([0; WORK_KIND_COUNT]),
                roots: BTreeMap::new(),
                next_root: 0,
                first_failure: None,
            }),
            stopped: AtomicBool::new(false),
            stop,
        }))
    }

    pub fn cancellation(&self) -> Cancellation {
        Cancellation(Arc::clone(&self.0))
    }

    pub fn phase(&self) -> Result<RuntimePhase, LifecycleError> {
        Ok(self.0.lock("phase", "supervisor")?.phase)
    }

    pub fn shares_build(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    pub fn matches_stop_handle(&self, stop: &StopHandle) -> bool {
        self.0.stop.shares_domain(stop)
    }

    pub fn pending_counts(&self) -> Result<PendingCounts, LifecycleError> {
        Ok(self.0.lock("pending_counts", "supervisor")?.counts)
    }

    /// Verify domain identity before consulting the lease or the runtime state.
    pub fn check_task(&self, lease: &TaskLease) -> Result<(), LifecycleError> {
        if !Arc::ptr_eq(&self.0, &lease.inner) {
            return Err(LifecycleError::wrong_build(&lease.origin));
        }
        lease.check_active_with("check_task")
    }

    pub fn start_root(&self, kind: WorkKind, origin: &str) -> Result<TaskLease, LifecycleError> {
        let mut state = self.0.lock("start_root", origin)?;
        ensure_open(&self.0, &state, "start_root", origin, false)?;
        let root = state.next_root.checked_add(1).ok_or_else(|| {
            fail_locked(
                &self.0,
                &mut state,
                LifecycleErrorKind::Overflow,
                "start_root",
                origin,
                "root identifier exhausted",
            )
        })?;
        register_work(&self.0, &mut state, kind, root, "start_root", origin)?;
        state.next_root = root;
        Ok(TaskLease::new(&self.0, kind, root, origin))
    }

    pub fn begin_draining(&self) -> Result<(), LifecycleError> {
        let mut state = self.0.lock("begin_draining", "supervisor")?;
        ensure_open(&self.0, &state, "begin_draining", "supervisor", false)?;
        state.phase = RuntimePhase::Draining;
        Ok(())
    }

    pub fn try_close(&self) -> Result<(), LifecycleError> {
        let mut state = self.0.lock("try_close", "supervisor")?;
        if state.phase != RuntimePhase::Draining || self.0.stopped.load(Ordering::Acquire) {
            return Err(phase_error(&state, "try_close", "supervisor"));
        }
        if !state.counts.is_empty() || !state.roots.is_empty() {
            return Err(LifecycleError::new(
                LifecycleErrorKind::PendingWork,
                state.phase,
                "try_close",
                "supervisor",
                "registered tasks remain live",
            ));
        }
        if let Some(first) = &state.first_failure {
            return Err(cancelled_error(&state, "try_close", "supervisor", first));
        }
        state.phase = RuntimePhase::Closed;
        self.0.stopped.store(true, Ordering::Release);
        self.0.stop.revoke_for_close();
        Ok(())
    }

    pub fn cancel(&self, reason: String) -> Result<(), LifecycleError> {
        let mut state = self.0.lock("cancel", "supervisor")?;
        if matches!(state.phase, RuntimePhase::Succeeded | RuntimePhase::Failed) {
            return Err(phase_error(&state, "cancel", "supervisor"));
        }
        if state.first_failure.is_none() {
            state.first_failure = Some(Arc::new(LifecycleError::new(
                LifecycleErrorKind::Cancelled,
                state.phase,
                "cancel",
                "supervisor",
                reason,
            )));
        }
        state.phase = RuntimePhase::Cancelling;
        self.0.request_stop();
        Ok(())
    }

    pub fn finish_failed(&self) -> Result<(), LifecycleError> {
        let mut state = self.0.lock("finish_failed", "supervisor")?;
        if state.phase != RuntimePhase::Cancelling {
            return Err(phase_error(&state, "finish_failed", "supervisor"));
        }
        if !state.counts.is_empty() || !state.roots.is_empty() {
            return Err(LifecycleError::new(
                LifecycleErrorKind::PendingWork,
                state.phase,
                "finish_failed",
                "supervisor",
                "cleanup has live registered tasks",
            ));
        }
        if state.first_failure.is_none() {
            return Err(LifecycleError::new(
                LifecycleErrorKind::Cancelled,
                state.phase,
                "finish_failed",
                "supervisor",
                "first cancellation cause is still being recorded",
            ));
        }
        state.phase = RuntimePhase::Failed;
        Ok(())
    }

    /// The real publisher's no-replace rename and terminal state update use the
    /// same lock as cancellation; no caller-supplied callback may produce success.
    pub(super) fn commit_publication(
        &self,
        publisher: &BuildPublisher,
    ) -> Result<(), LifecycleError> {
        let mut state = self.0.lock("commit_publication", "publisher")?;
        if state.phase != RuntimePhase::Closed
            || !state.counts.is_empty()
            || !state.roots.is_empty()
        {
            if matches!(state.phase, RuntimePhase::Active | RuntimePhase::Draining) {
                return Err(fail_locked(
                    &self.0,
                    &mut state,
                    LifecycleErrorKind::InvalidPhase,
                    "commit_publication",
                    "publisher",
                    "publisher invoked before build closed",
                ));
            }
            return Err(phase_error(&state, "commit_publication", "publisher"));
        }
        if !publisher.matches_lifecycle(self) {
            return Err(LifecycleError::wrong_build("publisher"));
        }
        if let Some(first) = &state.first_failure {
            return Err(cancelled_error(&state, "commit_publication", "publisher", first));
        }
        // The lifecycle state lock is acquired before the VM stop gate. External
        // StopHandle cancellation wins if it acquired that gate first; if
        // publication acquires it first, rename and Succeeded remain indivisible.
        let commit = self.0.stop.with_publication_guard(|| {
            let result = publisher.rename_for_commit();
            if result.is_ok() {
                state.phase = RuntimePhase::Succeeded;
            }
            result
        });
        match commit {
            Ok(Ok(())) => Ok(()),
            Ok(Err(source)) => {
                let failure = Arc::new(LifecycleError::publication_failed(source));
                state.first_failure = Some(Arc::clone(&failure));
                state.phase = RuntimePhase::Cancelling;
                self.0.request_stop();
                Err(cancelled_error(&state, "commit_publication", "publisher", &failure))
            },
            Err(StopBarrierError::Cancelled) => Err(fail_locked(
                &self.0,
                &mut state,
                LifecycleErrorKind::Cancelled,
                "commit_publication",
                "publisher",
                "VM cancellation won publication",
            )),
            Err(StopBarrierError::Poisoned) => Err(fail_locked(
                &self.0,
                &mut state,
                LifecycleErrorKind::Poisoned,
                "commit_publication",
                "publisher",
                "VM stop publication gate poisoned",
            )),
        }
    }
}

impl Cancellation {
    pub fn is_requested(&self) -> bool {
        self.0.stopped.load(Ordering::Acquire) || self.0.stop.is_stop_requested()
    }
    pub fn check(&self) -> Result<(), LifecycleError> {
        let state = self.0.lock("check", "cancellation")?;
        ensure_open(&self.0, &state, "check", "cancellation", true)
    }
}

impl TaskLease {
    fn new(inner: &Arc<Inner>, kind: WorkKind, root: u64, origin: &str) -> Self {
        Self { inner: Arc::clone(inner), kind, root, origin: origin.to_owned(), is_live: true }
    }

    pub fn start_child(&self, kind: WorkKind, origin: &str) -> Result<TaskLease, LifecycleError> {
        let mut state = self.inner.lock("start_child", origin)?;
        ensure_open(&self.inner, &state, "start_child", origin, true)?;
        if !self.is_live || !state.roots.contains_key(&self.root) {
            return Err(LifecycleError::new(
                LifecycleErrorKind::InvalidPhase,
                state.phase,
                "start_child",
                origin,
                "parent/root lease is not live",
            ));
        }
        register_work(&self.inner, &mut state, kind, self.root, "start_child", origin)?;
        Ok(Self::new(&self.inner, kind, self.root, origin))
    }

    pub fn check_active(&self) -> Result<(), LifecycleError> {
        self.check_active_with("check_active")
    }

    fn check_active_with(&self, operation: &'static str) -> Result<(), LifecycleError> {
        let state = self.inner.lock(operation, &self.origin)?;
        ensure_open(&self.inner, &state, operation, &self.origin, true)?;
        if !self.is_live || !state.roots.contains_key(&self.root) {
            return Err(LifecycleError::new(
                LifecycleErrorKind::InvalidPhase,
                state.phase,
                operation,
                &self.origin,
                "lease is not live",
            ));
        }
        Ok(())
    }

    pub fn complete(mut self) -> Result<(), LifecycleError> {
        self.finish("complete")
    }

    fn finish(&mut self, operation: &'static str) -> Result<(), LifecycleError> {
        let inner = Arc::clone(&self.inner);
        let mut state = inner.lock(operation, &self.origin)?;
        self.release_work(&mut state, operation)?;
        if let Some(first) = &state.first_failure {
            return Err(cancelled_error(&state, operation, &self.origin, first));
        }
        if inner.stopped.load(Ordering::Acquire) {
            return Err(LifecycleError::new(
                LifecycleErrorKind::Cancelled,
                state.phase,
                operation,
                &self.origin,
                "stop requested during task completion",
            ));
        }
        Ok(())
    }

    fn release_work(
        &mut self,
        state: &mut State,
        operation: &'static str,
    ) -> Result<(), LifecycleError> {
        if !self.is_live {
            return Err(LifecycleError::new(
                LifecycleErrorKind::InvalidPhase,
                state.phase,
                operation,
                &self.origin,
                "lease already completed",
            ));
        }
        let count = state.counts.0[self.kind.index()];
        let root_count = state.roots.get(&self.root).copied();
        if count == 0 || root_count.is_none_or(|count| count == 0) {
            return Err(fail_locked(
                &self.inner,
                state,
                LifecycleErrorKind::Overflow,
                operation,
                &self.origin,
                "inconsistent task accounting",
            ));
        }
        state.counts.0[self.kind.index()] = count - 1;
        if root_count == Some(1) {
            state.roots.remove(&self.root);
        } else if let Some(root) = state.roots.get_mut(&self.root) {
            *root -= 1;
        }
        self.is_live = false;
        Ok(())
    }
}

impl Drop for TaskLease {
    fn drop(&mut self) {
        if !self.is_live {
            return;
        }
        let inner = Arc::clone(&self.inner);
        if let Ok(mut state) = inner.lock("drop", &self.origin) {
            record_failure_locked(
                &inner,
                &mut state,
                LifecycleErrorKind::AbandonedWork,
                "drop",
                &self.origin,
                "lease dropped without complete",
            );
            if self.release_work(&mut state, "drop").is_err() {
                inner.request_stop();
            }
        }
    }
}

fn phase_error(state: &State, operation: &'static str, origin: &str) -> LifecycleError {
    if let Some(first) = &state.first_failure {
        return cancelled_error(state, operation, origin, first);
    }
    LifecycleError::new(
        LifecycleErrorKind::InvalidPhase,
        state.phase,
        operation,
        origin,
        "operation not permitted in current phase",
    )
}

fn cancelled_error(
    state: &State,
    operation: &'static str,
    origin: &str,
    first: &Arc<LifecycleError>,
) -> LifecycleError {
    LifecycleError::new(
        LifecycleErrorKind::Cancelled,
        state.phase,
        operation,
        origin,
        "build cancelled; original failure follows",
    )
    .with_source(Arc::clone(first) as Arc<dyn Error + Send + Sync>)
}

fn ensure_open(
    inner: &Inner,
    state: &State,
    operation: &'static str,
    origin: &str,
    allow_draining: bool,
) -> Result<(), LifecycleError> {
    if let Some(first) = &state.first_failure {
        return Err(cancelled_error(state, operation, origin, first));
    }
    if inner.stopped.load(Ordering::Acquire) {
        return Err(phase_error(state, operation, origin));
    }
    if state.phase == RuntimePhase::Active
        || (allow_draining && state.phase == RuntimePhase::Draining)
    {
        return Ok(());
    }
    Err(phase_error(state, operation, origin))
}

fn fail_locked(
    inner: &Inner,
    state: &mut State,
    kind: LifecycleErrorKind,
    operation: &'static str,
    origin: &str,
    cause: &str,
) -> LifecycleError {
    record_failure_locked(inner, state, kind, operation, origin, cause)
}

fn record_failure_locked(
    inner: &Inner,
    state: &mut State,
    kind: LifecycleErrorKind,
    operation: &'static str,
    origin: &str,
    cause: &str,
) -> LifecycleError {
    let failure = LifecycleError::new(kind, state.phase, operation, origin, cause);
    if state.first_failure.is_none() {
        state.first_failure =
            Some(Arc::new(LifecycleError::new(kind, state.phase, operation, origin, cause)));
    }
    state.phase = RuntimePhase::Cancelling;
    inner.request_stop();
    failure
}

fn register_work(
    inner: &Inner,
    state: &mut State,
    kind: WorkKind,
    root: u64,
    operation: &'static str,
    origin: &str,
) -> Result<(), LifecycleError> {
    let next_kind = state.counts.0[kind.index()].checked_add(1);
    let next_root = state.roots.get(&root).copied().unwrap_or(0).checked_add(1);
    let (Some(next_kind), Some(next_root)) = (next_kind, next_root) else {
        return Err(fail_locked(
            inner,
            state,
            LifecycleErrorKind::Overflow,
            operation,
            origin,
            "task counter exhausted",
        ));
    };
    state.counts.0[kind.index()] = next_kind;
    state.roots.insert(root, next_root);
    Ok(())
}
