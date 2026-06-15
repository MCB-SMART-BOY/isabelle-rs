//! Discrimination nets — O(1) term pattern matching.
//!
//! Corresponds to `src/Pure/net.ML`.
//!
//! A discrimination net is a trie-like data structure that indexes
//! terms by their structure, allowing fast retrieval of all terms
//! that match a given pattern. Used extensively by the simplifier
//! and proof methods.

use std::{collections::BTreeMap, sync::Arc};

use super::term::Term;

// =========================================================================
// Net node
// =========================================================================

/// A node in the discrimination net.
/// Each node can contain items (theorems/terms) and children
/// indexed by the next symbol in the pattern.
#[derive(Clone, Debug)]
struct NetNode<T: Clone> {
    /// Items stored at this node (matched by the prefix leading here).
    items: Vec<Arc<T>>,
    /// Children indexed by head symbol.
    children: BTreeMap<String, NetNode<T>>,
    /// Children for variable patterns (match anything).
    var_child: Option<Box<NetNode<T>>>,
}

impl<T: Clone> NetNode<T> {
    fn new() -> Self {
        NetNode { items: Vec::new(), children: BTreeMap::new(), var_child: None }
    }
}

// =========================================================================
// Discrimination net
// =========================================================================

/// A discrimination net for fast pattern matching.
/// `T` is typically `Thm` (for rewrite rules) or `Term` (for term indexing).
#[derive(Clone, Debug)]
pub struct Net<T: Clone> {
    root: NetNode<T>,
}

impl<T: Clone> Net<T> {
    /// Create an empty net.
    pub fn empty() -> Self {
        Net { root: NetNode::new() }
    }

    /// Insert an item keyed by a pattern term.
    /// The pattern's structure determines where in the net it's stored.
    pub fn insert(&mut self, pattern: &Term, item: Arc<T>) {
        insert_into(&mut self.root, pattern, item);
    }

    /// Find all items whose pattern matches the given term.
    pub fn lookup(&self, term: &Term) -> Vec<Arc<T>> {
        let mut results = Vec::new();
        lookup_in(&self.root, term, &mut results);
        results
    }

    /// Check if the net is empty.
    pub fn is_empty(&self) -> bool {
        self.root.items.is_empty() && self.root.children.is_empty() && self.root.var_child.is_none()
    }

    /// Merge another net into this one.
    pub fn merge(&mut self, other: &Net<T>) {
        for item in &other.root.items {
            self.root.items.push(Arc::clone(item));
        }
        for (key, child) in &other.root.children {
            let our_child = self.root.children.entry(key.clone()).or_insert_with(NetNode::new);
            merge_nodes(our_child, child);
        }
        if let Some(var_child) = &other.root.var_child {
            let our_var = self.root.var_child.get_or_insert_with(|| Box::new(NetNode::new()));
            merge_nodes(our_var, var_child);
        }
    }
}

fn insert_into<T: Clone>(node: &mut NetNode<T>, pattern: &Term, item: Arc<T>) {
    match pattern {
        Term::Var { .. } | Term::Bound(_) => {
            // Variable/bound patterns match anything — store in var_child
            let child = node.var_child.get_or_insert_with(|| Box::new(NetNode::new()));
            child.items.push(item);
        },
        Term::Const { name, .. } => {
            let child = node.children.entry(name.to_string()).or_insert_with(NetNode::new);
            child.items.push(item);
        },
        Term::Free { name, .. } => {
            let child = node.children.entry(format!("FREE:{name}")).or_insert_with(NetNode::new);
            child.items.push(item);
        },
        Term::App { func, arg } => {
            // Index by the head of the application
            insert_into_app(node, func, arg, item);
        },
        Term::Abs { body, .. } => {
            insert_into(node, body, item);
        },
    }
}

fn insert_into_app<T: Clone>(node: &mut NetNode<T>, func: &Term, _arg: &Term, item: Arc<T>) {
    match func {
        Term::Const { name, .. } => {
            let child = node.children.entry(name.to_string()).or_insert_with(NetNode::new);
            child.items.push(item);
        },
        _ => {
            // Complex head — store at this level
            node.items.push(item);
        },
    }
}

fn lookup_in<T: Clone>(node: &NetNode<T>, term: &Term, results: &mut Vec<Arc<T>>) {
    // Add items at this level
    results.extend(node.items.iter().map(Arc::clone));

    // Check variable child (matches anything)
    if let Some(ref var_child) = node.var_child {
        results.extend(var_child.items.iter().map(Arc::clone));
    }

    match term {
        Term::Const { name, .. } => {
            if let Some(child) = node.children.get(name.as_ref()) {
                lookup_in(child, term, results);
            }
        },
        Term::Free { name, .. } => {
            let key = format!("FREE:{name}");
            if let Some(child) = node.children.get(&key) {
                lookup_in(child, term, results);
            }
        },
        Term::App { func, arg: _ } => {
            // Look up by head
            if let Term::Const { name, .. } = func.as_ref() {
                if let Some(child) = node.children.get(name.as_ref()) {
                    lookup_in(child, term, results);
                }
            }
            // Also check variable child
            if let Some(ref var_child) = node.var_child {
                lookup_in(var_child, term, results);
            }
        },
        _ => {},
    }
}

fn merge_nodes<T: Clone>(target: &mut NetNode<T>, source: &NetNode<T>) {
    target.items.extend(source.items.iter().map(Arc::clone));
    for (key, child) in &source.children {
        let t = target.children.entry(key.clone()).or_insert_with(NetNode::new);
        merge_nodes(t, child);
    }
    if let Some(ref var_child) = source.var_child {
        let t = target.var_child.get_or_insert_with(|| Box::new(NetNode::new()));
        merge_nodes(t, var_child);
    }
}

impl<T: Clone> Default for Net<T> {
    fn default() -> Self {
        Net::empty()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::types::Typ;

    fn konst(name: &str) -> Term {
        Term::const_(name, Typ::dummy())
    }

    #[test]
    fn test_insert_and_lookup() {
        let mut net: Net<String> = Net::empty();
        let pat = konst("foo");
        net.insert(&pat, Arc::new("rule1".to_string()));

        let results = net.lookup(&konst("foo"));
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].as_ref(), "rule1");
    }

    #[test]
    fn test_no_match() {
        let mut net: Net<String> = Net::empty();
        net.insert(&konst("foo"), Arc::new("rule1".to_string()));

        let results = net.lookup(&konst("bar"));
        assert!(results.is_empty());
    }

    #[test]
    fn test_var_pattern() {
        let mut net: Net<String> = Net::empty();
        let pat = Term::var("x", 0, Typ::dummy());
        net.insert(&pat, Arc::new("matches_all".to_string()));

        // Var pattern should match anything
        let results = net.lookup(&konst("anything"));
        assert!(!results.is_empty());
    }
}
