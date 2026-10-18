//! Immutable ML Context metadata. Kernel owners remain independent of ML serials.
//! No data value can change an owner or commit a pending theorem.
#[path = "context_bridge.rs"]
mod bridge;

/// Exact replacement for `structure Context: PRIVATE_CONTEXT` in the fixed
/// official context.ML. The source loader retains the preceding signatures
/// and following data functors, substituting only this complete structure.
pub fn replacement_structure() -> &'static str {
    bridge::SOURCE
}

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use isabelle_kernel::TrustedTheory;
use thiserror::Error;

use super::lifecycle::{BuildLifecycle, LifecycleError, TaskLease, WorkKind};
use super::objects::{LogicalObject, ObjectError, ObjectKind, ObjectStore, sealed::Sealed};
use crate::ml::value::ValueData;
use crate::ml::{MlError, MlErrorKind, Span, Type, TypeScheme, Value, Vm, WeakValue};

/// Context failures are user-correctable ML errors unless an object-store check
/// detects a revoked, foreign, or stale capability.
#[derive(Debug, Error)]
pub enum ContextError {
    /// The caller supplied an invalid context value or data-kind identifier.
    #[error("invalid context input for {operation}: {reason}")]
    Invalid { operation: &'static str, reason: String },
    /// Official `Context.THEORY` error with the precise offending theories.
    #[error("Context theory {operation}: {reason}")]
    Theory { operation: &'static str, reason: String, theories: Vec<Value> },
    /// A handle failed the build/runtime/lease boundary.
    #[error("context object access failed: {0}")]
    Object(#[from] ObjectError),
    /// The kernel rejected a proposed joint parent owner.
    #[error("cannot merge Context parents: {0}")]
    Kernel(#[from] isabelle_kernel::KernelError),
    /// Callback work could not be registered or completed under this build lease.
    #[error("Context callback lifecycle failed: {0}")]
    Lifecycle(#[from] LifecycleError),
    /// An ML callback failed with its original exception and its prior ref effects intact.
    #[error("context callback failed: {0}")]
    Callback(#[from] MlError),
    /// Installing original signatures, bridge and original functors failed;
    /// the VM has been stopped and the build cancellation was recorded.
    #[error("cannot install official Context at {source_name}: {cause}")]
    Installation {
        source_name: String,
        #[source]
        cause: Box<ContextError>,
    },
    /// The original installation failure and revocation failure are both retained.
    #[error(
        "cannot install official Context at {source_name}: {cause}; also failed to cancel build: {cancellation}"
    )]
    InstallRevocation {
        source_name: String,
        #[source]
        cause: Box<ContextError>,
        cancellation: LifecycleError,
    },
}

#[derive(Clone)]
struct TheoryNode {
    serial: u64,
    name: String,
    stage: u64,
    // Shared only by sibling ML updates, matching the original per-theory allocation state.
    stage_counter: Rc<Cell<u64>>,
    lineage: BTreeSet<u64>,
    parents: Vec<Value>,
    ancestors: Vec<Value>,
    owner: Value,
    data: BTreeMap<i64, Value>,
}
impl Sealed for TheoryNode {}
impl LogicalObject for TheoryNode {
    const KIND: ObjectKind = ObjectKind::Theory;
}

#[derive(Clone)]
struct TheoryIdNode {
    serial: u64,
    name: String,
    stage: u64,
    lineage: BTreeSet<u64>,
}
impl Sealed for TheoryIdNode {}
impl LogicalObject for TheoryIdNode {
    const KIND: ObjectKind = ObjectKind::Theory;
}

#[derive(Clone)]
struct ProofNode {
    theory: Value,
    data: BTreeMap<i64, Value>,
}
impl Sealed for ProofNode {}
impl LogicalObject for ProofNode {
    const KIND: ObjectKind = ObjectKind::ProofContext;
}

struct TheoryKind {
    position: Value,
    empty: Value,
    merge: Value,
    merge_type: Type,
}
struct ProofKind {
    init: Value,
    init_type: Type,
}

#[derive(Clone)]
enum GenericContext {
    Theory(Value),
    Proof(Value),
}
#[derive(Clone)]
struct ContextExceptions {
    theory: Value,
    error: Value,
    empty: Value,
}
struct State {
    next_serial: u64,
    next_kind: i64,
    theory_kinds: BTreeMap<i64, TheoryKind>,
    proof_kinds: BTreeMap<i64, ProofKind>,
    dynamic: Option<GenericContext>,
    exceptions: Option<ContextExceptions>,
    trace_theories: bool,
    trace_proofs: bool,
    trace_position: Option<Value>,
    theory_tokens: Vec<(WeakValue, Value)>,
    proof_tokens: Vec<(WeakValue, Value)>,
    total_theories: usize,
    total_proofs: usize,
}

/// One VM-local host. It holds the supervised evaluation lease for its entire
/// lifetime; callers must complete that lease only after this host is dropped.
pub struct ContextHost {
    store: ObjectStore,
    lease: Rc<TaskLease>,
    state: RefCell<State>,
}

impl ContextHost {
    /// Execute the fixed official module and seal its private bridge in one
    /// transaction. The source bytes must be those read and hashed through the
    /// caller's RestrictedHost; the VM structurally validates the replacement.
    pub fn install_official(
        vm: &mut Vm,
        store: ObjectStore,
        lifecycle: BuildLifecycle,
        lease: Rc<TaskLease>,
        pure: TrustedTheory,
        source_name: &str,
        official_source: &str,
    ) -> Result<Rc<Self>, ContextError> {
        let installation = (|| {
            if !lifecycle.matches_stop_handle(&vm.stop_handle()) {
                return Err(invalid("install Context", "build and VM use different stop domains"));
            }
            lifecycle.check_task(&lease)?;
            let host = Self::prepare(vm, store, lease, pure)?;
            vm.evaluate_native_context_module(
                source_name,
                official_source,
                replacement_structure(),
            )?;
            host.capture_exceptions(vm)?;
            Ok(host)
        })();
        match installation {
            Ok(host) => Ok(host),
            Err(cause) => {
                vm.request_stop();
                let cancellation =
                    lifecycle.cancel(format!("cannot install Context at {source_name}: {cause}"));
                match cancellation {
                    Ok(()) => Err(ContextError::Installation {
                        source_name: source_name.to_owned(),
                        cause: Box::new(cause),
                    }),
                    Err(cancellation) => Err(ContextError::InstallRevocation {
                        source_name: source_name.to_owned(),
                        cause: Box::new(cause),
                        cancellation,
                    }),
                }
            },
        }
    }

    fn prepare(
        vm: &mut Vm,
        store: ObjectStore,
        lease: Rc<TaskLease>,
        pure: TrustedTheory,
    ) -> Result<Rc<Self>, ContextError> {
        if vm.context_host().is_some() {
            return Err(invalid("install Context", "VM already has a Context host"));
        }
        if vm.resolve_host_type("Position.T").is_none() {
            return Err(invalid(
                "install Context",
                "official Position.T must be elaborated before Context",
            ));
        }
        let host = Rc::new(Self {
            store,
            lease,
            state: RefCell::new(State {
                next_serial: 1,
                next_kind: 0,
                theory_kinds: BTreeMap::new(),
                proof_kinds: BTreeMap::new(),
                dynamic: None,
                exceptions: None,
                trace_theories: false,
                trace_proofs: false,
                trace_position: None,
                theory_tokens: Vec::new(),
                proof_tokens: Vec::new(),
                total_theories: 0,
                total_proofs: 0,
            }),
        });
        let owner = host.store.insert(vm, &host.lease, pure)?;
        let root = host.make_theory(
            vm,
            TheoryNode {
                serial: 0,
                name: "Pure".to_owned(),
                stage: 1,
                stage_counter: Rc::new(Cell::new(1)),
                lineage: BTreeSet::new(),
                parents: Vec::new(),
                ancestors: Vec::new(),
                owner,
                data: BTreeMap::new(),
            },
        )?;
        host.state.borrow_mut().dynamic = Some(GenericContext::Theory(root));
        if let Err(error) = host.register(vm) {
            vm.request_stop();
            return Err(error);
        }
        vm.set_context_host(Rc::clone(&host))?;
        Ok(host)
    }

    fn capture_exceptions(&self, vm: &Vm) -> Result<(), ContextError> {
        let theory = capture_exception(vm, "Context.THEORY", true)?;
        let error_name = if vm.lookup_value("ERROR")?.is_some() { "ERROR" } else { "Exn.ERROR" };
        let error = capture_exception(vm, error_name, true)?;
        let empty = capture_exception(vm, "List.Empty", false)?;
        self.state.borrow_mut().exceptions = Some(ContextExceptions { theory, error, empty });
        Ok(())
    }

    fn allocate_serial(&self) -> Result<u64, ContextError> {
        let mut state = self.state.borrow_mut();
        let serial = state.next_serial;
        if serial > i64::MAX as u64 {
            return Err(invalid("allocate serial", "ML identity exhausted"));
        }
        state.next_serial = serial
            .checked_add(1)
            .ok_or_else(|| invalid("allocate serial", "ML identity exhausted"))?;
        Ok(serial)
    }
    fn make_theory(&self, vm: &mut Vm, mut node: TheoryNode) -> Result<Value, ContextError> {
        node.serial = self.allocate_serial()?;
        self.store.get::<TrustedTheory>(vm, &self.lease, &node.owner)?;
        let value = self.store.insert(vm, &self.lease, node)?;
        self.track_context(&value, true)?;
        Ok(value)
    }

    fn make_proof(&self, vm: &mut Vm, node: ProofNode) -> Result<Value, ContextError> {
        self.theory(vm, &node.theory)?;
        let value = self.store.insert(vm, &self.lease, node)?;
        self.track_context(&value, false)?;
        Ok(value)
    }

    fn track_context(&self, value: &Value, is_theory: bool) -> Result<(), ContextError> {
        let mut state = self.state.borrow_mut();
        let is_traced = if is_theory { state.trace_theories } else { state.trace_proofs };
        if !is_traced {
            return Ok(());
        }
        let position = state
            .trace_position
            .clone()
            .ok_or_else(|| invalid("trace Context", "missing Position.thread_data value"))?;
        if is_theory {
            state.total_theories = state
                .total_theories
                .checked_add(1)
                .ok_or_else(|| invalid("trace Context", "theory counter exhausted"))?;
            state.theory_tokens.push((value.downgrade(), position));
        } else {
            state.total_proofs = state
                .total_proofs
                .checked_add(1)
                .ok_or_else(|| invalid("trace Context", "proof counter exhausted"))?;
            state.proof_tokens.push((value.downgrade(), position));
        }
        Ok(())
    }

    /// Return the checked logical owner to another trusted Rust host module.
    /// No owner-handle constructor is installed in the ML namespace.
    pub(crate) fn owner_of(
        &self,
        vm: &Vm,
        theory: &Value,
    ) -> Result<Rc<TrustedTheory>, ContextError> {
        let node = self.theory(vm, theory)?;
        Ok(self.store.get::<TrustedTheory>(vm, &self.lease, &node.owner)?)
    }

    /// Compare validated kernel owners without exporting either token to ML.
    pub fn has_same_logical_owner(
        &self,
        vm: &Vm,
        left: &Value,
        right: &Value,
    ) -> Result<bool, ContextError> {
        Ok(self.owner_of(vm, left)?.id() == self.owner_of(vm, right)?.id())
    }
    fn theory(&self, vm: &Vm, value: &Value) -> Result<Rc<TheoryNode>, ContextError> {
        let node = self.store.get::<TheoryNode>(vm, &self.lease, value)?;
        self.store.get::<TrustedTheory>(vm, &self.lease, &node.owner)?;
        Ok(node)
    }

    fn proof(&self, vm: &Vm, value: &Value) -> Result<Rc<ProofNode>, ContextError> {
        let node = self.store.get::<ProofNode>(vm, &self.lease, value)?;
        self.theory(vm, &node.theory)?;
        Ok(node)
    }

    fn with_dynamic<T>(
        &self,
        context: Option<GenericContext>,
        f: impl FnOnce() -> Result<T, ContextError>,
    ) -> Result<T, ContextError> {
        let original = std::mem::replace(&mut self.state.borrow_mut().dynamic, context);
        let result = f();
        self.state.borrow_mut().dynamic = original;
        result
    }

    fn invoke_callback(
        &self,
        vm: &mut Vm,
        function: &Value,
        function_type: &Type,
        argument: Value,
        context: GenericContext,
    ) -> Result<Value, ContextError> {
        let Type::Function(input, _) = function_type else {
            return Err(ContextError::Callback(vm.error(
                MlErrorKind::HostFailure,
                "Context data callback",
                "registered callback lacks a certified function type",
            )));
        };
        let callback = self.lease.start_child(WorkKind::Callback, "Context data callback")?;
        let result = self.with_dynamic(Some(context), || {
            vm.apply_with_type(function, &argument, (**input).clone())
                .map_err(ContextError::Callback)
        });
        callback.complete()?;
        result
    }

    fn get_dynamic(&self) -> Option<GenericContext> {
        self.state.borrow().dynamic.clone()
    }

    fn set_dynamic(&self, vm: &Vm, context: Option<GenericContext>) -> Result<(), ContextError> {
        if let Some(value) = &context {
            match value {
                GenericContext::Theory(thy) => {
                    self.theory(vm, thy)?;
                },
                GenericContext::Proof(proof) => {
                    self.proof(vm, proof)?;
                },
            }
        }
        self.state.borrow_mut().dynamic = context;
        Ok(())
    }

    fn declare_theory_kind(
        &self,
        position: Value,
        empty: Value,
        merge: Value,
        merge_type: Type,
    ) -> Result<i64, ContextError> {
        let mut state = self.state.borrow_mut();
        let kind = state.next_kind;
        state.next_kind = kind
            .checked_add(1)
            .ok_or_else(|| invalid("Theory_Data.declare", "data kind exhausted"))?;
        state.theory_kinds.insert(kind, TheoryKind { position, empty, merge, merge_type });
        Ok(kind)
    }

    fn declare_proof_kind(&self, init: Value, init_type: Type) -> Result<i64, ContextError> {
        let mut state = self.state.borrow_mut();
        let kind = state.next_kind;
        state.next_kind = kind
            .checked_add(1)
            .ok_or_else(|| invalid("Proof_Data.declare", "data kind exhausted"))?;
        state.proof_kinds.insert(kind, ProofKind { init, init_type });
        Ok(kind)
    }

    fn theory_data(&self, vm: &Vm, kind: i64, thy: &Value) -> Result<Value, ContextError> {
        let node = self.theory(vm, thy)?;
        if let Some(value) = node.data.get(&kind) {
            return Ok(value.clone());
        }
        self.state
            .borrow()
            .theory_kinds
            .get(&kind)
            .map(|entry| entry.empty.clone())
            .ok_or_else(|| invalid("Theory_Data.get", format!("unknown kind {kind}")))
    }

    fn put_theory_data(
        &self,
        vm: &mut Vm,
        kind: i64,
        value: Value,
        thy: &Value,
    ) -> Result<Value, ContextError> {
        if !self.state.borrow().theory_kinds.contains_key(&kind) {
            return Err(invalid("Theory_Data.put", format!("unknown kind {kind}")));
        }
        let mut node = (*self.theory(vm, thy)?).clone();
        node.data.insert(kind, value);
        self.update_theory(vm, thy, node, false)
    }

    fn update_theory(
        &self,
        vm: &mut Vm,
        previous: &Value,
        mut node: TheoryNode,
        finish: bool,
    ) -> Result<Value, ContextError> {
        let prior = self.theory(vm, previous)?;
        node.lineage.insert(prior.serial);
        if prior.stage == 0 {
            node.parents = vec![previous.clone()];
            node.ancestors = self.prepend_ancestor(vm, previous, &prior.ancestors)?;
        }
        node.stage = if finish { 0 } else { self.next_stage(&node.stage_counter)? };
        self.make_theory(vm, node)
    }

    fn next_stage(&self, counter: &Cell<u64>) -> Result<u64, ContextError> {
        let next = counter
            .get()
            .checked_add(1)
            .ok_or_else(|| invalid("update theory", "stage exhausted"))?;
        counter.set(next);
        Ok(next)
    }

    fn prepend_ancestor(
        &self,
        vm: &Vm,
        value: &Value,
        ancestors: &[Value],
    ) -> Result<Vec<Value>, ContextError> {
        let mut result = ancestors.to_vec();
        self.insert_ancestor(vm, value, &mut result)?;
        if result.len() == ancestors.len() {
            return Err(ContextError::Theory {
                operation: "finish_thy",
                reason: "Duplicate theory node".to_owned(),
                theories: std::iter::once(value.clone()).chain(ancestors.iter().cloned()).collect(),
            });
        }
        Ok(result)
    }

    fn is_subtheory(
        &self,
        vm: &Vm,
        ancestor: &Value,
        descendant: &Value,
    ) -> Result<bool, ContextError> {
        let left = self.theory(vm, ancestor)?;
        let right = self.theory(vm, descendant)?;
        Ok(left.serial == right.serial || right.lineage.contains(&left.serial))
    }

    fn canonical_parents(&self, vm: &Vm, imports: &[Value]) -> Result<Vec<Value>, ContextError> {
        let mut unique = Vec::new();
        let mut seen = BTreeSet::new();
        for import in imports {
            let node = self.theory(vm, import)?;
            if seen.insert(node.serial) {
                unique.push(import.clone());
            }
        }
        let mut result = Vec::new();
        for parent in &unique {
            let mut is_covered = false;
            for other in &unique {
                if !parent.is_same_object(other) && self.is_subtheory(vm, parent, other)? {
                    is_covered = true;
                    break;
                }
            }
            if !is_covered {
                result.push(parent.clone());
            }
        }
        Ok(result)
    }

    fn merge_data(
        &self,
        vm: &mut Vm,
        parents: &[Value],
        provisional: &Value,
    ) -> Result<BTreeMap<i64, Value>, ContextError> {
        let first = self.theory(vm, &parents[0])?;
        if parents.len() == 1 {
            return Ok(first.data.clone());
        }
        let kinds = self
            .state
            .borrow()
            .theory_kinds
            .iter()
            .map(|(&kind, entry)| (kind, entry.merge.clone(), entry.merge_type.clone()))
            .collect::<Vec<_>>();
        let mut data = first.data.clone();
        for (kind, merge, merge_type) in kinds {
            let mut present = Vec::new();
            for parent in parents {
                if let Some(value) = self.theory(vm, parent)?.data.get(&kind) {
                    present.push((parent.clone(), value.clone()));
                }
            }
            match present.as_slice() {
                [] => {},
                [(_, value)] => {
                    data.entry(kind).or_insert_with(|| value.clone());
                },
                _ => {
                    let arguments = present
                        .into_iter()
                        .map(|(theory, value)| Value::tuple(vec![theory, value]))
                        .collect();
                    let merged = self.invoke_callback(
                        vm,
                        &merge,
                        &merge_type,
                        Value::list(arguments),
                        GenericContext::Theory(provisional.clone()),
                    )?;
                    data.insert(kind, merged);
                },
            }
        }
        Ok(data)
    }

    fn insert_ancestor(
        &self,
        vm: &Vm,
        candidate: &Value,
        ancestors: &mut Vec<Value>,
    ) -> Result<(), ContextError> {
        let node = self.theory(vm, candidate)?;
        let base = node.name.rsplit('.').next().unwrap_or(&node.name);
        for existing in ancestors.iter() {
            let prior = self.theory(vm, existing)?;
            if prior.serial == node.serial {
                return Ok(());
            }
            if prior.name.rsplit('.').next().unwrap_or(&prior.name) == base {
                return Err(ContextError::Theory {
                    operation: "merge ancestors",
                    reason: "Duplicate theory name".to_owned(),
                    theories: vec![candidate.clone(), existing.clone()],
                });
            }
        }
        ancestors.insert(0, candidate.clone());
        Ok(())
    }

    fn merge_ancestors(&self, vm: &Vm, parents: &[Value]) -> Result<Vec<Value>, ContextError> {
        let mut ancestors = self.theory(vm, &parents[0])?.ancestors.clone();
        for parent in &parents[1..] {
            let node = self.theory(vm, parent)?;
            for ancestor in node.ancestors.iter().rev() {
                self.insert_ancestor(vm, ancestor, &mut ancestors)?;
            }
        }
        for parent in parents {
            self.insert_ancestor(vm, parent, &mut ancestors)?;
        }
        Ok(ancestors)
    }

    fn begin_theory(
        &self,
        vm: &mut Vm,
        name: String,
        imports: &[Value],
    ) -> Result<Value, ContextError> {
        if name.is_empty() {
            return Err(invalid("begin_thy", "Bad theory name: \"\""));
        }
        if imports.is_empty() {
            return Err(invalid("begin_thy", "Missing theory imports"));
        }
        let parents = self.canonical_parents(vm, imports)?;
        let ancestors = self.merge_ancestors(vm, &parents)?;
        let mut owners = Vec::with_capacity(parents.len());
        let mut lineage = BTreeSet::new();
        for parent in &parents {
            let node = self.theory(vm, parent)?;
            owners.push((*self.store.get::<TrustedTheory>(vm, &self.lease, &node.owner)?).clone());
            lineage.insert(node.serial);
            lineage.extend(&node.lineage);
        }
        let owner = self.store.insert(
            vm,
            &self.lease,
            TrustedTheory::merge_parents(name.clone(), &owners)?,
        )?;
        let stage_counter = Rc::new(Cell::new(1));
        let provisional = self.make_theory(
            vm,
            TheoryNode {
                serial: 0,
                name: name.clone(),
                stage: 1,
                stage_counter: Rc::clone(&stage_counter),
                lineage: lineage.clone(),
                parents: parents.clone(),
                ancestors: ancestors.clone(),
                owner: owner.clone(),
                data: BTreeMap::new(),
            },
        )?;
        let data = self.merge_data(vm, &parents, &provisional)?;
        self.make_theory(
            vm,
            TheoryNode {
                serial: 0,
                name,
                stage: 1,
                stage_counter,
                lineage,
                parents,
                ancestors,
                owner,
                data,
            },
        )
    }

    fn get_proof_data(&self, vm: &mut Vm, kind: i64, proof: &Value) -> Result<Value, ContextError> {
        let node = self.proof(vm, proof)?;
        if let Some(value) = node.data.get(&kind) {
            return Ok(value.clone());
        }
        let (init, init_type) = self
            .state
            .borrow()
            .proof_kinds
            .get(&kind)
            .map(|item| (item.init.clone(), item.init_type.clone()))
            .ok_or_else(|| invalid("Proof_Data.get", format!("unknown kind {kind}")))?;
        self.invoke_callback(
            vm,
            &init,
            &init_type,
            node.theory.clone(),
            GenericContext::Proof(proof.clone()),
        )
    }

    fn init_proof(&self, vm: &mut Vm, thy: &Value) -> Result<Value, ContextError> {
        self.theory(vm, thy)?;
        let mut data = BTreeMap::new();
        let kinds = self
            .state
            .borrow()
            .proof_kinds
            .iter()
            .map(|(&kind, item)| (kind, item.init.clone(), item.init_type.clone()))
            .collect::<Vec<_>>();
        for (kind, init, init_type) in kinds {
            let provisional =
                self.make_proof(vm, ProofNode { theory: thy.clone(), data: data.clone() })?;
            let value = self.invoke_callback(
                vm,
                &init,
                &init_type,
                thy.clone(),
                GenericContext::Proof(provisional),
            )?;
            data.insert(kind, value);
        }
        self.make_proof(vm, ProofNode { theory: thy.clone(), data })
    }

    fn transfer_proof(
        &self,
        vm: &mut Vm,
        thy: &Value,
        proof: &Value,
    ) -> Result<Value, ContextError> {
        let previous = self.proof(vm, proof)?;
        if self.is_subtheory(vm, &previous.theory, thy)?
            && !self.is_subtheory(vm, thy, &previous.theory)?
        {
            let kinds = self
                .state
                .borrow()
                .proof_kinds
                .iter()
                .filter_map(|(&kind, entry)| {
                    (!previous.data.contains_key(&kind)).then_some((
                        kind,
                        entry.init.clone(),
                        entry.init_type.clone(),
                    ))
                })
                .collect::<Vec<_>>();
            let mut data = previous.data.clone();
            for (kind, init, init_type) in kinds {
                let provisional =
                    self.make_proof(vm, ProofNode { theory: thy.clone(), data: data.clone() })?;
                let value = self.invoke_callback(
                    vm,
                    &init,
                    &init_type,
                    thy.clone(),
                    GenericContext::Proof(provisional),
                )?;
                data.insert(kind, value);
            }
            return self.make_proof(vm, ProofNode { theory: thy.clone(), data });
        }
        if self.is_subtheory(vm, thy, &previous.theory)?
            && self.is_subtheory(vm, &previous.theory, thy)?
        {
            return Ok(proof.clone());
        }
        Err(invalid("raw_transfer", "Cannot transfer proof context: not a super theory"))
    }

    fn put_proof_data(
        &self,
        vm: &mut Vm,
        kind: i64,
        value: Value,
        proof: &Value,
    ) -> Result<Value, ContextError> {
        if !self.state.borrow().proof_kinds.contains_key(&kind) {
            return Err(invalid("Proof_Data.put", format!("unknown kind {kind}")));
        }
        let mut node = (*self.proof(vm, proof)?).clone();
        node.data.insert(kind, value);
        self.make_proof(vm, node)
    }

    fn register(&self, vm: &mut Vm) -> Result<(), ContextError> {
        let position = vm.resolve_host_type("Position.T").ok_or_else(|| {
            invalid("install Context", "official Position.T must be elaborated before Context")
        })?;
        for name in ["host_context_theory", "host_context_proof", "host_context_id"] {
            vm.register_host_type(name, 0, false)?;
        }
        register_theory_primitives(vm, position.clone())?;
        register_remaining_primitives(vm, position)?;
        Ok(())
    }
}

type Primitive = (&'static str, Type, crate::ml::NativeFunction);

fn register_primitives<const N: usize>(
    vm: &mut Vm,
    primitives: [Primitive; N],
) -> Result<(), ContextError> {
    for (name, scheme, callback) in primitives {
        vm.register_native(name, TypeScheme::mono(scheme), callback)?;
    }
    Ok(())
}

fn register_theory_primitives(vm: &mut Vm, position: Type) -> Result<(), ContextError> {
    let theory = typ("host_context_theory");
    let any = typ("exn");
    let integer = typ("int");
    let list = |ty: Type| Type::Constructor("list".into(), vec![ty]);
    let pair =
        |a: Type, b: Type| Type::Record(BTreeMap::from([("1".into(), a), ("2".into(), b)]), false);
    let func = |a: Type, b: Type| Type::Function(Box::new(a), Box::new(b));
    register_primitives(
        vm,
        [
            (
                "Native_Context.begin",
                func(pair(typ("string"), list(theory.clone())), theory.clone()),
                begin,
            ),
            ("Native_Context.finish", func(theory.clone(), theory.clone()), finish),
            ("Native_Context.join", func(list(theory.clone()), theory.clone()), join),
            ("Native_Context.parents", func(theory.clone(), list(theory.clone())), parents),
            ("Native_Context.ancestors", func(theory.clone(), list(theory.clone())), ancestors),
            ("Native_Context.name", func(theory.clone(), typ("string")), name),
            ("Native_Context.identifier", func(theory.clone(), integer.clone()), identifier),
            ("Native_Context.stage", func(theory.clone(), integer.clone()), stage),
            ("Native_Context.eq", func(pair(theory.clone(), theory.clone()), typ("bool")), eq),
            ("Native_Context.sub", func(pair(theory.clone(), theory.clone()), typ("bool")), sub),
            (
                "Native_Context.data_declare",
                func(
                    Type::Record(
                        BTreeMap::from([
                            ("1".into(), position.clone()),
                            ("2".into(), any.clone()),
                            (
                                "3".into(),
                                func(list(pair(theory.clone(), any.clone())), any.clone()),
                            ),
                        ]),
                        false,
                    ),
                    integer.clone(),
                ),
                declare_theory,
            ),
            (
                "Native_Context.data_get",
                func(pair(integer.clone(), theory.clone()), any.clone()),
                get_theory_data,
            ),
            (
                "Native_Context.data_put",
                func(
                    Type::Record(
                        BTreeMap::from([
                            ("1".into(), integer),
                            ("2".into(), any),
                            ("3".into(), theory.clone()),
                        ]),
                        false,
                    ),
                    theory,
                ),
                put_theory_data,
            ),
        ],
    )
}

fn register_remaining_primitives(vm: &mut Vm, position: Type) -> Result<(), ContextError> {
    let theory = typ("host_context_theory");
    let proof = typ("host_context_proof");
    let theory_id = typ("host_context_id");
    let any = typ("exn");
    let integer = typ("int");
    let unit = typ("unit");
    let list = |ty: Type| Type::Constructor("list".into(), vec![ty]);
    let pair =
        |a: Type, b: Type| Type::Record(BTreeMap::from([("1".into(), a), ("2".into(), b)]), false);
    let func = |a: Type, b: Type| Type::Function(Box::new(a), Box::new(b));
    register_primitives(
        vm,
        [
            (
                "Native_Context.proof_declare",
                func(func(theory.clone(), any.clone()), integer.clone()),
                declare_proof,
            ),
            (
                "Native_Context.proof_get",
                func(pair(integer.clone(), proof.clone()), any.clone()),
                get_proof_data,
            ),
            (
                "Native_Context.proof_put",
                func(
                    Type::Record(
                        BTreeMap::from([
                            ("1".into(), integer.clone()),
                            ("2".into(), any.clone()),
                            ("3".into(), proof.clone()),
                        ]),
                        false,
                    ),
                    proof.clone(),
                ),
                put_proof_data,
            ),
            ("Native_Context.proof_init", func(theory.clone(), proof.clone()), init_proof),
            ("Native_Context.proof_theory", func(proof.clone(), theory.clone()), proof_theory),
            (
                "Native_Context.proof_transfer",
                func(pair(theory.clone(), proof.clone()), proof.clone()),
                transfer,
            ),
            ("Native_Context.dynamic_kind", func(unit.clone(), integer.clone()), dynamic_kind),
            ("Native_Context.dynamic_theory", func(unit.clone(), theory.clone()), dynamic_theory),
            ("Native_Context.dynamic_proof", func(unit.clone(), proof.clone()), dynamic_proof),
            (
                "Native_Context.dynamic_set_theory",
                func(theory.clone(), unit.clone()),
                dynamic_set_theory,
            ),
            (
                "Native_Context.dynamic_set_proof",
                func(proof.clone(), unit.clone()),
                dynamic_set_proof,
            ),
            ("Native_Context.dynamic_clear", func(unit.clone(), unit.clone()), dynamic_clear),
            ("Native_Context.theory_id", func(theory.clone(), theory_id.clone()), theory_id_of),
            ("Native_Context.id_name", func(theory_id.clone(), typ("string")), id_name),
            ("Native_Context.id_stage", func(theory_id.clone(), integer.clone()), id_stage),
            ("Native_Context.id_serial", func(theory_id.clone(), integer.clone()), id_serial),
            (
                "Native_Context.id_eq",
                func(pair(theory_id.clone(), theory_id.clone()), typ("bool")),
                id_eq,
            ),
            (
                "Native_Context.id_sub",
                func(pair(theory_id.clone(), theory_id.clone()), typ("bool")),
                id_sub,
            ),
            (
                "Native_Context.theory_kinds",
                func(unit.clone(), list(pair(integer.clone(), position.clone()))),
                theory_kinds,
            ),
            (
                "Native_Context.present_kinds",
                func(theory.clone(), list(pair(integer.clone(), position.clone()))),
                present_kinds,
            ),
            (
                "Native_Context.set_tracing",
                func(
                    Type::Record(
                        BTreeMap::from([
                            ("1".into(), typ("bool")),
                            ("2".into(), typ("bool")),
                            ("3".into(), position.clone()),
                        ]),
                        false,
                    ),
                    unit.clone(),
                ),
                set_tracing,
            ),
            (
                "Native_Context.finish_tracing",
                func(
                    unit.clone(),
                    Type::Record(
                        BTreeMap::from([
                            ("1".into(), list(pair(theory.clone(), position.clone()))),
                            ("2".into(), list(pair(proof.clone(), position.clone()))),
                            ("3".into(), integer.clone()),
                            ("4".into(), integer),
                        ]),
                        false,
                    ),
                ),
                finish_tracing,
            ),
            ("Native_Context.initial", func(unit, theory), initial),
        ],
    )
}

fn invalid(operation: &'static str, reason: impl Into<String>) -> ContextError {
    ContextError::Invalid { operation, reason: reason.into() }
}
fn typ(name: &str) -> Type {
    Type::Constructor(name.into(), Vec::new())
}
fn host(vm: &Vm) -> Result<Rc<ContextHost>, MlError> {
    vm.context_host().ok_or_else(|| MlError {
        kind: MlErrorKind::HostFailure,
        span: Box::new(Span::new("<native Context>", 0, 0)),
        operation: "Context".into(),
        cause: "Context host not installed".to_owned(),
        exception: None,
        trace: Vec::new(),
    })
}
fn mapped<T>(result: Result<T, ContextError>) -> Result<T, MlError> {
    result.map_err(|error| match error {
        ContextError::Callback(error) => error,
        error => MlError {
            kind: if matches!(
                error,
                ContextError::Object(_)
                    | ContextError::Lifecycle(_)
                    | ContextError::Kernel(isabelle_kernel::KernelError::Invariant(_))
            ) {
                MlErrorKind::HostFailure
            } else {
                MlErrorKind::Type
            },
            span: Box::new(Span::new("<native Context>", 0, 0)),
            operation: "Context".into(),
            cause: error.to_string(),
            exception: None,
            trace: Vec::new(),
        },
    })
}
fn capture_exception(vm: &Vm, name: &str, has_argument: bool) -> Result<Value, ContextError> {
    let value = vm
        .lookup_value(name)?
        .cloned()
        .ok_or_else(|| invalid("install Context", format!("missing exception {name}")))?;
    let is_expected = matches!(
        (&*value.0, has_argument),
        (ValueData::ExceptionFunction { .. }, true)
            | (ValueData::Exception { argument: None, .. }, false)
    );
    if !is_expected {
        return Err(invalid("install Context", format!("invalid exception constructor {name}")));
    }
    Ok(value)
}

fn captured_exceptions(vm: &Vm) -> Result<ContextExceptions, MlError> {
    let host = host(vm)?;
    let result = host.state.borrow().exceptions.clone();
    result.ok_or_else(|| MlError {
        kind: MlErrorKind::HostFailure,
        span: Box::new(Span::new("<native Context>", 0, 0)),
        operation: "Context".into(),
        cause: "Context exceptions not installed".to_owned(),
        exception: None,
        trace: Vec::new(),
    })
}

fn raise_captured_exception(
    vm: &mut Vm,
    constructor: &Value,
    argument: Option<Value>,
    operation: &str,
    cause: String,
) -> MlError {
    let packet = match argument {
        Some(argument) => match vm.apply_captured_exception(constructor, &argument) {
            Ok(packet) => packet,
            Err(error) => return error,
        },
        None => constructor.clone(),
    };
    match vm.raise_exception(&packet, None, false) {
        Ok(mut error) => {
            error.operation = operation.into();
            error.cause = cause;
            error.span = Box::new(vm.declaration_span.clone());
            error
        },
        Err(error) => error,
    }
}

fn reify_context_error(vm: &mut Vm, result: Result<Value, ContextError>) -> Result<Value, MlError> {
    let error = match result {
        Ok(value) => return Ok(value),
        Err(error) => error,
    };
    if matches!(error, ContextError::Kernel(isabelle_kernel::KernelError::Invariant(_))) {
        vm.request_stop();
        return mapped(Err(error));
    }
    match &error {
        ContextError::Theory { reason, theories, .. } => {
            let exceptions = captured_exceptions(vm)?;
            let argument =
                Value::tuple(vec![Value::text(reason.clone()), Value::list(theories.clone())]);
            return Err(raise_captured_exception(
                vm,
                &exceptions.theory,
                Some(argument),
                "Context theory",
                error.to_string(),
            ));
        },
        ContextError::Invalid { .. } | ContextError::Kernel(_) => {
            let exceptions = captured_exceptions(vm)?;
            let message = match &error {
                ContextError::Invalid { reason, .. } => reason.clone(),
                _ => error.to_string(),
            };
            return Err(raise_captured_exception(
                vm,
                &exceptions.error,
                Some(Value::text(message)),
                "Context",
                error.to_string(),
            ));
        },
        _ => {},
    }
    mapped(Err(error))
}
fn args<'a>(
    value: &'a Value,
    expected: usize,
    operation: &'static str,
) -> Result<&'a [Value], ContextError> {
    value
        .as_tuple()
        .filter(|values| values.len() == expected)
        .ok_or_else(|| invalid(operation, format!("expected {expected} tuple fields")))
}
fn kind(value: &Value, operation: &'static str) -> Result<i64, ContextError> {
    value.as_int().ok_or_else(|| invalid(operation, "expected integer kind"))
}
fn begin(vm: &mut Vm, args_: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    let result = (|| {
        let fields = args(&args_[0], 2, "begin_thy")?;
        let name = fields[0].as_text().ok_or_else(|| invalid("begin_thy", "expected name"))?;
        let imports =
            fields[1].as_list().ok_or_else(|| invalid("begin_thy", "expected imports list"))?;
        host.begin_theory(vm, name.to_owned(), imports)
    })();
    reify_context_error(vm, result)
}
fn finish(vm: &mut Vm, args_: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    let result = (|| {
        let node = (*host.theory(vm, &args_[0])?).clone();
        host.update_theory(vm, &args_[0], node, true)
    })();
    reify_context_error(vm, result)
}
fn is_join_compatible(first: &TheoryNode, other: &TheoryNode) -> bool {
    other.stage != 0
        && first.name == other.name
        && first.parents.len() == other.parents.len()
        && first.ancestors.len() == other.ancestors.len()
        && first.parents.iter().zip(&other.parents).all(|(left, right)| left.is_same_object(right))
        && first
            .ancestors
            .iter()
            .zip(&other.ancestors)
            .all(|(left, right)| left.is_same_object(right))
}

fn join(vm: &mut Vm, args_: &[Value]) -> Result<Value, MlError> {
    if args_[0].as_list().is_some_and(|values| values.is_empty()) {
        let exceptions = captured_exceptions(vm)?;
        return Err(raise_captured_exception(
            vm,
            &exceptions.empty,
            None,
            "Context.join_thys",
            "empty theory list".to_owned(),
        ));
    }
    let host = host(vm)?;
    let result = (|| {
        let values =
            args_[0].as_list().ok_or_else(|| invalid("join_thys", "expected theory list"))?;
        let theories =
            values.iter().map(|value| host.theory(vm, value)).collect::<Result<Vec<_>, _>>()?;
        let first = theories.first().ok_or_else(|| invalid("join_thys", "empty theory list"))?;
        let bad = values
            .iter()
            .zip(&theories)
            .filter_map(|(value, theory)| {
                (!is_join_compatible(first, theory)).then_some(value.clone())
            })
            .collect::<Vec<_>>();
        if !bad.is_empty() {
            return Err(ContextError::Theory {
                operation: "join_thys",
                reason: "Cannot join theories".to_owned(),
                theories: bad,
            });
        }
        let mut node = (**first).clone();
        node.lineage.insert(node.serial);
        let mut owners = Vec::with_capacity(values.len());
        for (value, theory) in values.iter().zip(&theories) {
            owners.push((*host.owner_of(vm, value)?).clone());
            node.lineage.insert(theory.serial);
            node.lineage.extend(&theory.lineage);
        }
        if owners.iter().any(|owner| owner.id() != owners[0].id()) {
            node.owner = host.store.insert(
                vm,
                &host.lease,
                TrustedTheory::merge_parents(node.name.clone(), &owners)?,
            )?;
        }
        node.stage = host.next_stage(&node.stage_counter)?;
        if values.len() == 1 {
            return host.make_theory(vm, node);
        }
        let provisional = host.make_theory(vm, node.clone())?;
        node.data = host.merge_data(vm, values, &provisional)?;
        host.make_theory(vm, node)
    })();
    reify_context_error(vm, result)
}
fn parents(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.theory(vm, &values[0]).map(|node| Value::list(node.parents.clone())))
}
fn ancestors(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.theory(vm, &values[0]).map(|node| Value::list(node.ancestors.clone())))
}
fn name(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.theory(vm, &values[0]).map(|node| Value::text(node.name.clone())))
}
fn identifier(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.theory(vm, &values[0]).and_then(|node| {
        i64::try_from(node.serial)
            .map(Value::int)
            .map_err(|_| invalid("theory_identifier", "ML serial exceeds int"))
    }))
}
fn stage(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.theory(vm, &values[0]).and_then(|node| {
        i64::try_from(node.stage)
            .map(Value::int)
            .map_err(|_| invalid("stage", "theory stage exceeds int"))
    }))
}
fn eq(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let fields = args(&values[0], 2, "eq_thy")?;
        Ok(Value::bool(host.theory(vm, &fields[0])?.serial == host.theory(vm, &fields[1])?.serial))
    })())
}
fn sub(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let fields = args(&values[0], 2, "subthy")?;
        Ok(Value::bool(host.is_subtheory(vm, &fields[0], &fields[1])?))
    })())
}
fn declare_theory(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let merge_type = match vm.native_argument_type(0) {
        Some(Type::Record(fields, false)) => fields.get("3").cloned(),
        _ => None,
    }
    .ok_or_else(|| {
        vm.error(
            MlErrorKind::HostFailure,
            "Theory_Data.declare",
            "missing certified merge callback type",
        )
    })?;
    let host = host(vm)?;
    mapped((|| {
        let parts = args(&values[0], 3, "Theory_Data.declare")?;
        Ok(Value::int(host.declare_theory_kind(
            parts[0].clone(),
            parts[1].clone(),
            parts[2].clone(),
            merge_type,
        )?))
    })())
}
fn get_theory_data(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let fields = args(&values[0], 2, "Theory_Data.get")?;
        host.theory_data(vm, kind(&fields[0], "Theory_Data.get")?, &fields[1])
    })())
}
fn put_theory_data(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    let result = (|| {
        let fields = args(&values[0], 3, "Theory_Data.put")?;
        host.put_theory_data(
            vm,
            kind(&fields[0], "Theory_Data.put")?,
            fields[1].clone(),
            &fields[2],
        )
    })();
    reify_context_error(vm, result)
}
fn declare_proof(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let init_type = vm.native_argument_type(0).ok_or_else(|| {
        vm.error(
            MlErrorKind::HostFailure,
            "Proof_Data.declare",
            "missing certified init callback type",
        )
    })?;
    let host = host(vm)?;
    mapped(host.declare_proof_kind(values[0].clone(), init_type).map(Value::int))
}
fn get_proof_data(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let fields = args(&values[0], 2, "Proof_Data.get")?;
        host.get_proof_data(vm, kind(&fields[0], "Proof_Data.get")?, &fields[1])
    })())
}
fn put_proof_data(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let fields = args(&values[0], 3, "Proof_Data.put")?;
        host.put_proof_data(vm, kind(&fields[0], "Proof_Data.put")?, fields[1].clone(), &fields[2])
    })())
}
fn init_proof(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.init_proof(vm, &values[0]))
}
fn proof_theory(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.proof(vm, &values[0]).map(|node| node.theory.clone()))
}
fn transfer(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    let result = (|| {
        let fields = args(&values[0], 2, "raw_transfer")?;
        host.transfer_proof(vm, &fields[0], &fields[1])
    })();
    reify_context_error(vm, result)
}
fn dynamic_kind(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    Ok(Value::int(match host.get_dynamic() {
        None => 0,
        Some(GenericContext::Theory(_)) => 1,
        Some(GenericContext::Proof(_)) => 2,
    }))
}
fn dynamic_theory(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(match host.get_dynamic() {
        Some(GenericContext::Theory(thy)) => Ok(thy),
        _ => Err(invalid("get_generic_context", "no theory context")),
    })
}
fn dynamic_proof(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(match host.get_dynamic() {
        Some(GenericContext::Proof(proof)) => Ok(proof),
        _ => Err(invalid("get_generic_context", "no proof context")),
    })
}
fn dynamic_set_theory(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.set_dynamic(vm, Some(GenericContext::Theory(values[0].clone()))))?;
    Ok(Value::unit())
}
fn dynamic_set_proof(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.set_dynamic(vm, Some(GenericContext::Proof(values[0].clone()))))?;
    Ok(Value::unit())
}
fn dynamic_clear(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(host.set_dynamic(vm, None))?;
    Ok(Value::unit())
}
fn theory_id_of(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let node = host.theory(vm, &values[0])?;
        Ok(host.store.insert(
            vm,
            &host.lease,
            TheoryIdNode {
                serial: node.serial,
                name: node.name.clone(),
                stage: node.stage,
                lineage: node.lineage.clone(),
            },
        )?)
    })())
}
fn id_name(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(
        host.store
            .get::<TheoryIdNode>(vm, &host.lease, &values[0])
            .map(|node| Value::text(node.name.clone()))
            .map_err(Into::into),
    )
}
fn id_serial(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped(
        host.store
            .get::<TheoryIdNode>(vm, &host.lease, &values[0])
            .map(|node| Value::int(node.serial as i64))
            .map_err(Into::into),
    )
}
fn id_stage(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let id = host.store.get::<TheoryIdNode>(vm, &host.lease, &values[0])?;
        let stage = i64::try_from(id.stage)
            .map_err(|_| invalid("theory_id stage", "stage exceeds ML int"))?;
        Ok(Value::int(stage))
    })())
}
fn id_eq(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let fields = args(&values[0], 2, "eq_thy_id")?;
        let left = host.store.get::<TheoryIdNode>(vm, &host.lease, &fields[0])?;
        let right = host.store.get::<TheoryIdNode>(vm, &host.lease, &fields[1])?;
        Ok(Value::bool(left.serial == right.serial))
    })())
}
fn id_sub(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let fields = args(&values[0], 2, "subthy_id")?;
        let left = host.store.get::<TheoryIdNode>(vm, &host.lease, &fields[0])?;
        let right = host.store.get::<TheoryIdNode>(vm, &host.lease, &fields[1])?;
        Ok(Value::bool(left.serial == right.serial || right.lineage.contains(&left.serial)))
    })())
}
fn theory_kinds(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    Ok(Value::list(
        host.state
            .borrow()
            .theory_kinds
            .iter()
            .map(|(&kind, entry)| Value::tuple(vec![Value::int(kind), entry.position.clone()]))
            .collect(),
    ))
}
fn present_kinds(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let node = host.theory(vm, &values[0])?;
        let state = host.state.borrow();
        let mut present = Vec::with_capacity(node.data.len());
        for kind in node.data.keys() {
            let entry = state.theory_kinds.get(kind).ok_or_else(|| {
                invalid("theory_data_sizeof1", format!("missing registered kind {kind}"))
            })?;
            present.push(Value::tuple(vec![Value::int(*kind), entry.position.clone()]));
        }
        Ok(Value::list(present))
    })())
}
fn set_tracing(vm: &mut Vm, values: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let args = args(&values[0], 3, "set Context tracing")?;
        let theories = args[0]
            .as_bool()
            .ok_or_else(|| invalid("set Context tracing", "expected theory guard"))?;
        let proofs = args[1]
            .as_bool()
            .ok_or_else(|| invalid("set Context tracing", "expected proof guard"))?;
        let mut state = host.state.borrow_mut();
        state.trace_theories = theories;
        state.trace_proofs = proofs;
        state.trace_position = Some(args[2].clone());
        Ok(Value::unit())
    })())
}
fn finish_tracing(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    mapped((|| {
        let mut state = host.state.borrow_mut();
        state.theory_tokens.retain(|(token, _)| token.upgrade().is_some());
        state.proof_tokens.retain(|(token, _)| token.upgrade().is_some());
        let theories = state
            .theory_tokens
            .iter()
            .filter_map(|(token, pos)| {
                token.upgrade().map(|value| Value::tuple(vec![value, pos.clone()]))
            })
            .collect();
        let proofs = state
            .proof_tokens
            .iter()
            .filter_map(|(token, pos)| {
                token.upgrade().map(|value| Value::tuple(vec![value, pos.clone()]))
            })
            .collect();
        let total_theories = i64::try_from(state.total_theories)
            .map_err(|_| invalid("finish_tracing", "theory total exceeds ML int"))?;
        let total_proofs = i64::try_from(state.total_proofs)
            .map_err(|_| invalid("finish_tracing", "proof total exceeds ML int"))?;
        Ok(Value::tuple(vec![
            Value::list(theories),
            Value::list(proofs),
            Value::int(total_theories),
            Value::int(total_proofs),
        ]))
    })())
}
fn initial(vm: &mut Vm, _: &[Value]) -> Result<Value, MlError> {
    let host = host(vm)?;
    match host.get_dynamic() {
        Some(GenericContext::Theory(thy)) => Ok(thy),
        _ => mapped(Err(invalid("initial", "initial Pure context is unavailable"))),
    }
}
