use super::environment::ValueEnvironment;
use super::value::{ClosureStatic, ValueData};
use super::{MlError, Value, Vm};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

impl Vm {
    pub(super) fn track_value(&mut self, value: Value) -> Value {
        let is_closure_like = matches!(
            &*value.0,
            ValueData::Closure { .. }
                | ValueData::CurriedClosure { .. }
                | ValueData::NativePartial { .. }
        );
        if matches!(
            &*value.0,
            ValueData::Tuple(_)
                | ValueData::List(_)
                | ValueData::Vector(_)
                | ValueData::Array(_)
                | ValueData::Record(_)
                | ValueData::Constructor { .. }
                | ValueData::Exception { .. }
                | ValueData::Closure { .. }
                | ValueData::CurriedClosure { .. }
                | ValueData::NativePartial { .. }
                | ValueData::Reference(_)
                | ValueData::WeakReference(_)
                | ValueData::Host { .. }
        ) {
            self.heap.push(Rc::downgrade(&value.0));
        }
        if is_closure_like {
            if let Some(next) = self.next_closure_epoch.checked_add(1) {
                self.next_closure_epoch = next;
            } else {
                self.request_stop();
            }
            let pointer = Rc::as_ptr(&value.0) as usize;
            self.closure_creation_epoch.insert(pointer, self.next_closure_epoch);
            self.record_active_closure_views(pointer);
        }
        value
    }

    /// Collect only inaccessible cycles; live Rust Values are automatically roots.
    pub fn collect_garbage(&mut self) -> Result<usize, MlError> {
        self.check_stop()?;
        let nodes = self.heap.iter().filter_map(|value| value.upgrade()).collect::<Vec<_>>();
        let indexes = nodes
            .iter()
            .enumerate()
            .map(|(index, value)| (Rc::as_ptr(value) as usize, index))
            .collect::<HashMap<_, _>>();
        let edges = build_heap_edges(self, &nodes, &indexes)?;
        let reachable = mark_reachable(self, &nodes, &edges)?;
        let live = collect_live_closures(&nodes, &reachable);
        let none = self.make_option(None)?;
        clear_weak_referents(self, &nodes, &indexes, &reachable, &none)?;
        let collected = sweep_unreachable(self, &nodes, &reachable, &live, &none)?;
        drop(nodes);
        self.heap.retain(|value| value.strong_count() > 0);
        self.exception_origins.retain(|_, (weak, _)| weak.strong_count() > 0);
        let live_pointers = self
            .heap
            .iter()
            .filter_map(|value| value.upgrade())
            .map(|value| Rc::as_ptr(&value) as usize)
            .collect::<HashSet<_>>();
        self.closure_input_types.retain(|pointer, _| live_pointers.contains(pointer));
        self.closure_type_substitutions.retain(|pointer, _| live_pointers.contains(pointer));
        self.closure_definition_paths.retain(|pointer, _| live_pointers.contains(pointer));
        self.closure_weak_variables.retain(|pointer, _| live_pointers.contains(pointer));
        self.closure_type_views.retain(|pointer, _| live_pointers.contains(pointer));
        self.closure_creation_epoch.retain(|pointer, _| live_pointers.contains(pointer));
        // Slots are stable identities; dead weak entries must not shift live object indices.
        Ok(collected)
    }
}

struct HeapEdges {
    incoming: Vec<usize>,
    strong: Vec<Vec<usize>>,
}

fn build_heap_edges(
    vm: &Vm,
    nodes: &[Rc<ValueData>],
    indexes: &HashMap<usize, usize>,
) -> Result<HeapEdges, MlError> {
    let mut edges =
        HeapEdges { incoming: vec![0; nodes.len()], strong: vec![Vec::new(); nodes.len()] };
    let mut counted_environments = HashSet::new();
    for (index, node) in nodes.iter().enumerate() {
        vm.check_stop()?;
        if let ValueData::WeakReference(cell) = &**node {
            vm.validate_weak_contents(&cell.borrow(), "collect weak reference")?;
        }
        let should_count = match &**node {
            ValueData::Closure { environment, .. }
            | ValueData::CurriedClosure { environment, .. } => {
                counted_environments.insert(Rc::as_ptr(environment) as usize)
            },
            _ => true,
        };
        let argument_count = match &**node {
            ValueData::CurriedClosure { arguments, .. } => arguments.borrow().len(),
            _ => 0,
        };
        for (position, child) in children_of(node).into_iter().enumerate() {
            let Some(&child_index) = indexes.get(&(Rc::as_ptr(&child.0) as usize)) else {
                continue;
            };
            if should_count || position < argument_count {
                edges.incoming[child_index] += 1;
            }
            if !matches!(&**node, ValueData::WeakReference(_)) {
                edges.strong[index].push(child_index);
            }
        }
    }
    Ok(edges)
}

fn mark_reachable(
    vm: &Vm,
    nodes: &[Rc<ValueData>],
    edges: &HeapEdges,
) -> Result<Vec<bool>, MlError> {
    let mut reachable = vec![false; nodes.len()];
    let mut stack = nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            (Rc::strong_count(node) > edges.incoming[index] + 1).then_some(index)
        })
        .collect::<Vec<_>>();
    while let Some(index) = stack.pop() {
        vm.check_stop()?;
        if reachable[index] {
            continue;
        }
        reachable[index] = true;
        stack.extend(edges.strong[index].iter().copied());
    }
    Ok(reachable)
}

#[derive(Default)]
struct LiveClosures {
    environments: HashSet<usize>,
    lexical: HashSet<usize>,
}

fn collect_live_closures(nodes: &[Rc<ValueData>], reachable: &[bool]) -> LiveClosures {
    let mut live = LiveClosures::default();
    for (index, node) in nodes.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        match &**node {
            ValueData::Closure { environment, lexical, .. } => {
                live.environments.insert(Rc::as_ptr(environment) as usize);
                if let Some(lexical) = lexical {
                    live.lexical.insert(Rc::as_ptr(lexical) as usize);
                }
            },
            ValueData::CurriedClosure { environment, lexical, .. } => {
                live.environments.insert(Rc::as_ptr(environment) as usize);
                live.lexical.insert(Rc::as_ptr(lexical) as usize);
            },
            _ => {},
        }
    }
    live
}

fn clear_weak_referents(
    vm: &Vm,
    nodes: &[Rc<ValueData>],
    indexes: &HashMap<usize, usize>,
    reachable: &[bool],
    none: &Value,
) -> Result<(), MlError> {
    // The weak edge is excluded from marking, but a separately rooted SOME
    // keeps its ordinary strong edge to the referent.
    for (index, node) in nodes.iter().enumerate() {
        vm.check_stop()?;
        if !reachable[index] {
            continue;
        }
        let ValueData::WeakReference(cell) = &**node else { continue };
        let referent_index = match &*cell.borrow().0 {
            ValueData::Constructor { argument: Some(referent), .. } => {
                indexes.get(&(Rc::as_ptr(&referent.0) as usize)).copied()
            },
            _ => None,
        };
        if referent_index.is_some_and(|index| !reachable[index]) {
            *cell.borrow_mut() = none.clone();
        }
    }
    Ok(())
}

fn sweep_unreachable(
    vm: &Vm,
    nodes: &[Rc<ValueData>],
    reachable: &[bool],
    live: &LiveClosures,
    none: &Value,
) -> Result<usize, MlError> {
    let mut collected = 0;
    for (index, node) in nodes.iter().enumerate() {
        vm.check_stop()?;
        if !reachable[index] && clear_unreachable_value(node, live, none) {
            collected += 1;
        }
    }
    Ok(collected)
}

fn clear_unreachable_value(node: &ValueData, live: &LiveClosures, none: &Value) -> bool {
    match node {
        ValueData::WeakReference(cell) => *cell.borrow_mut() = none.clone(),
        ValueData::Reference(cell) => *cell.borrow_mut() = Value::unit(),
        ValueData::Array(cell) => cell.borrow_mut().clear(),
        ValueData::NativePartial { arguments, argument_types, .. } => {
            arguments.borrow_mut().clear();
            argument_types.borrow_mut().clear();
        },
        ValueData::Closure { environment, lexical, .. } => {
            clear_closure_state(environment, lexical.as_ref(), live);
        },
        ValueData::CurriedClosure { arguments, environment, lexical, .. } => {
            arguments.borrow_mut().clear();
            clear_closure_state(environment, Some(lexical), live);
        },
        _ => return false,
    }
    true
}

fn clear_closure_state(
    environment: &Rc<RefCell<ValueEnvironment>>,
    lexical: Option<&Rc<RefCell<ClosureStatic>>>,
    live: &LiveClosures,
) {
    if !live.environments.contains(&(Rc::as_ptr(environment) as usize)) {
        environment.borrow_mut().clear();
    }
    if let Some(lexical) = lexical
        && !live.lexical.contains(&(Rc::as_ptr(lexical) as usize))
    {
        let mut lexical = lexical.borrow_mut();
        lexical.structures.clear();
        lexical.functors.clear();
    }
}

fn children_of(node: &ValueData) -> Vec<Value> {
    match node {
        ValueData::Tuple(values) | ValueData::List(values) | ValueData::Vector(values) => {
            values.clone()
        },
        ValueData::Record(fields) => fields.values().cloned().collect(),
        ValueData::Constructor { argument: Some(value), .. }
        | ValueData::Exception { argument: Some(value), .. } => vec![value.clone()],
        ValueData::Reference(value) | ValueData::WeakReference(value) => {
            vec![value.borrow().clone()]
        },
        ValueData::Array(values) => values.borrow().clone(),
        ValueData::NativePartial { arguments, .. } => arguments.borrow().clone(),
        ValueData::Closure { environment, lexical, .. } => {
            let mut values = Vec::new();
            append_closure_children(environment, lexical.as_ref(), &mut values);
            values
        },
        ValueData::CurriedClosure { arguments, environment, lexical, .. } => {
            let mut values = arguments.borrow().clone();
            append_closure_children(environment, Some(lexical), &mut values);
            values
        },
        _ => Vec::new(),
    }
}

fn append_closure_children(
    environment: &Rc<std::cell::RefCell<super::environment::ValueEnvironment>>,
    lexical: Option<&Rc<std::cell::RefCell<super::value::ClosureStatic>>>,
    values: &mut Vec<Value>,
) {
    values.extend(environment.borrow().values().cloned());
    if let Some(lexical) = lexical {
        let lexical = lexical.borrow();
        for namespace in lexical.structures.values() {
            append_namespace_children(namespace, values);
        }
        for functor in lexical.functors.values() {
            append_functor_children(functor, values);
        }
    }
}

fn append_namespace_children(namespace: &super::value::Namespace, values: &mut Vec<Value>) {
    values.extend(namespace.values.values().cloned());
    for nested in namespace.structures.values() {
        append_namespace_children(nested, values);
    }
}

fn append_functor_children(functor: &super::value::Functor, values: &mut Vec<Value>) {
    append_namespace_children(&functor.environment, values);
    for nested in functor.functors.values() {
        append_functor_children(nested, values);
    }
}
