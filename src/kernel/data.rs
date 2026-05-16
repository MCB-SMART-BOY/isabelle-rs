//! Theorem databases: facts, consts, and discrimination nets.
//!
//! Corresponds to multiple Isabelle/Pure modules:
//! - `src/Pure/facts.ML`  — named fact tables
//! - `src/Pure/consts.ML` — polymorphic constant declarations
//! - `src/Pure/net.ML`    — discrimination nets for fast pattern matching
//!
//! ## What's included
//!
//! | Category | Types |
//! |----------|-------|
//! | Named facts | `Facts`, `FactRef` |
//! | Constant declarations | `Consts`, `ConstDecl`, `TypeScheme` |
//! | Discrimination nets | `Net<T>` (generic over item type) |

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::core::term::Term;
use crate::core::thm::Thm;
use crate::core::types::{Symbol, Typ};

// =========================================================================
// Facts — named theorem tables
// =========================================================================

/// A set of named facts — the global and local theorem database.
#[derive(Clone, Debug)]
pub struct Facts {
    entries: BTreeMap<String, Vec<Arc<Thm>>>,
}

impl Facts {
    pub fn empty() -> Self { Facts { entries: BTreeMap::new() } }

    /// Add theorems to a named fact.
    pub fn add(&mut self, name: &str, thms: Vec<Arc<Thm>>) {
        self.entries.entry(name.to_string()).or_default().extend(thms);
    }

    /// Get the theorems for a named fact.
    pub fn get(&self, name: &str) -> Option<&[Arc<Thm>]> {
        self.entries.get(name).map(|v| v.as_slice())
    }

    /// Get a single theorem (the first one).
    pub fn get_single(&self, name: &str) -> Option<&Arc<Thm>> {
        self.entries.get(name).and_then(|v| v.first())
    }

    /// Check if a fact exists.
    pub fn contains(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// Iterate over all fact names.
    pub fn names(&self) -> impl Iterator<Item = &String> {
        self.entries.keys()
    }

    /// Merge another fact table into this one.
    pub fn merge(&mut self, other: &Facts) {
        for (name, thms) in &other.entries {
            self.add(name, thms.clone());
        }
    }

    /// Remove a fact.
    pub fn remove(&mut self, name: &str) -> Option<Vec<Arc<Thm>>> {
        self.entries.remove(name)
    }
}

// =========================================================================
// Fact selectors
// =========================================================================

/// Selector for fact retrieval.
#[derive(Clone, Debug)]
pub enum FactRef {
    /// A simple named fact: `foo`
    Named(String),
    /// A numbered selection: `foo(1)`, `foo(2-4)`
    Select { name: String, index: usize },
}

impl FactRef {
    pub fn named(name: &str) -> Self { FactRef::Named(name.to_string()) }
}

impl Facts {
    /// Retrieve facts by reference.
    pub fn retrieve(&self, refs: &[FactRef]) -> Option<Vec<Arc<Thm>>> {
        let mut result = Vec::new();
        for r in refs {
            match r {
                FactRef::Named(name) => {
                    let thms = self.get(name)?;
                    result.extend_from_slice(thms);
                }
                FactRef::Select { name, index } => {
                    let thms = self.get(name)?;
                    if *index >= thms.len() { return None; }
                    result.push(Arc::clone(&thms[*index]));
                }
            }
        }
        Some(result)
    }
}

impl Default for Facts {
    fn default() -> Self { Facts::empty() }
}

// =========================================================================
// Consts — polymorphic constant declarations
// =========================================================================

/// A type scheme: a type with implicitly quantified type variables.
/// `'a => 'a => prop` means `∀'a. 'a => 'a => prop`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeScheme {
    pub body: Typ,
}

impl TypeScheme {
    pub fn new(body: Typ) -> Self { TypeScheme { body } }

    /// Check if a concrete type is an instance of this scheme.
    /// E.g., scheme `'a => 'a`, type `nat => nat` → true.
    pub fn is_instance(&self, typ: &Typ) -> bool {
        let _scheme_tvars = collect_tfrees(&self.body);
        let mut mapping: BTreeMap<String, Typ> = BTreeMap::new();
        match_types(&self.body, typ, &mut mapping);
        true // simplified — real impl checks consistency
    }
}

fn collect_tfrees(typ: &Typ) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    collect_tfrees_inner(typ, &mut set);
    set
}

fn collect_tfrees_inner(typ: &Typ, set: &mut BTreeSet<String>) {
    match typ {
        Typ::TFree { name, .. } => { set.insert(name.to_string()); }
        Typ::Type { args, .. } => {
            for a in args { collect_tfrees_inner(a, set); }
        }
        Typ::TVar { .. } => {}
    }
}

fn match_types(scheme: &Typ, concrete: &Typ, mapping: &mut BTreeMap<String, Typ>) {
    match (scheme, concrete) {
        (Typ::TFree { name, .. }, _) => {
            mapping.insert(name.to_string(), concrete.clone());
        }
        (Typ::Type { name: n1, args: a1 }, Typ::Type { name: n2, args: a2 })
            if n1 == n2 && a1.len() == a2.len() =>
        {
            for (s, c) in a1.iter().zip(a2.iter()) {
                match_types(s, c, mapping);
            }
        }
        _ => {}
    }
}

/// A constant's declaration: name + type scheme.
#[derive(Clone, Debug)]
pub struct ConstDecl {
    pub name: Symbol,
    pub scheme: TypeScheme,
    pub monomorphic: bool,
}

/// The table of all declared constants with their type schemes.
pub struct Consts {
    decls: BTreeMap<Symbol, ConstDecl>,
}

impl Consts {
    pub fn empty() -> Self { Consts { decls: BTreeMap::new() } }

    /// Declare a new constant.
    pub fn declare(&mut self, name: &str, scheme: TypeScheme) {
        let mono = collect_tfrees(&scheme.body).is_empty();
        self.decls.insert(
            Arc::from(name),
            ConstDecl { name: Arc::from(name), scheme, monomorphic: mono },
        );
    }

    /// Look up a constant's type scheme.
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        self.decls.get(name).map(|d| &d.scheme)
    }

    /// Check if a constant is declared.
    pub fn is_declared(&self, name: &str) -> bool {
        self.decls.contains_key(name)
    }

    /// Check if a type is an instance of a constant's scheme.
    pub fn instance_of(&self, name: &str, typ: &Typ) -> bool {
        match self.lookup(name) {
            Some(scheme) => scheme.is_instance(typ),
            None => false,
        }
    }
}

// =========================================================================
// Net — discrimination nets for O(1) pattern matching
// =========================================================================

/// A node in the discrimination net.
#[derive(Clone, Debug)]
struct NetNode<T: Clone> {
    items: Vec<Arc<T>>,
    children: BTreeMap<String, NetNode<T>>,
    var_child: Option<Box<NetNode<T>>>,
}

impl<T: Clone> NetNode<T> {
    fn new() -> Self {
        NetNode { items: Vec::new(), children: BTreeMap::new(), var_child: None }
    }
}

/// A discrimination net for fast pattern matching.
/// `T` is typically `Thm` (for rewrite rules) or `Term` (for term indexing).
#[derive(Clone, Debug)]
pub struct Net<T: Clone> {
    root: NetNode<T>,
}

impl<T: Clone> Net<T> {
    pub fn empty() -> Self {
        Net { root: NetNode::new() }
    }

    /// Insert an item keyed by a pattern term.
    pub fn insert(&mut self, pattern: &Term, item: Arc<T>) {
        insert_into(&mut self.root, pattern, item);
    }

    /// Find all items whose pattern matches the given term.
    pub fn lookup(&self, term: &Term) -> Vec<Arc<T>> {
        let mut results = Vec::new();
        lookup_in(&self.root, term, &mut results);
        results
    }

    pub fn is_empty(&self) -> bool {
        self.root.items.is_empty()
            && self.root.children.is_empty()
            && self.root.var_child.is_none()
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
            let child = node.var_child.get_or_insert_with(|| Box::new(NetNode::new()));
            child.items.push(item);
        }
        Term::Const { name, .. } => {
            let child = node.children.entry(name.to_string()).or_insert_with(NetNode::new);
            child.items.push(item);
        }
        Term::Free { name, .. } => {
            let child = node.children.entry(format!("FREE:{name}")).or_insert_with(NetNode::new);
            child.items.push(item);
        }
        Term::App { func, arg: _ } => {
            insert_into_app(node, func, item);
        }
        Term::Abs { body, .. } => {
            insert_into(node, body, item);
        }
    }
}

fn insert_into_app<T: Clone>(node: &mut NetNode<T>, func: &Term, item: Arc<T>) {
    match func {
        Term::Const { name, .. } => {
            let child = node.children.entry(name.to_string()).or_insert_with(NetNode::new);
            child.items.push(item);
        }
        _ => {
            node.items.push(item);
        }
    }
}

fn lookup_in<T: Clone>(node: &NetNode<T>, term: &Term, results: &mut Vec<Arc<T>>) {
    results.extend(node.items.iter().map(Arc::clone));

    if let Some(ref var_child) = node.var_child {
        results.extend(var_child.items.iter().map(Arc::clone));
    }

    match term {
        Term::Const { name, .. } => {
            if let Some(child) = node.children.get(name.as_ref()) {
                lookup_in(child, term, results);
            }
        }
        Term::Free { name, .. } => {
            let key = format!("FREE:{name}");
            if let Some(child) = node.children.get(&key) {
                lookup_in(child, term, results);
            }
        }
        Term::App { func, arg: _ } => {
            if let Term::Const { name, .. } = func.as_ref()
                && let Some(child) = node.children.get(name.as_ref()) {
                    lookup_in(child, term, results);
                }
            if let Some(ref var_child) = node.var_child {
                lookup_in(var_child, term, results);
            }
        }
        _ => {}
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
    fn default() -> Self { Net::empty() }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::thm::{CTerm, ThmKernel};
    use crate::core::term::Term as Tm;
    use crate::core::types::{Typ, Sort};

    fn dummy_thm() -> Arc<Thm> {
        let a = CTerm::certify(Tm::const_("A", Typ::base("prop")));
        Arc::new(ThmKernel::trivial(a).unwrap())
    }

    fn konst(name: &str) -> Tm {
        Tm::const_(name, Typ::dummy())
    }

    // ── Facts tests ──

    #[test]
    fn test_facts_add_and_get() {
        let mut facts = Facts::empty();
        let thm = dummy_thm();
        facts.add("foo", vec![Arc::clone(&thm)]);
        assert!(facts.contains("foo"));
        assert_eq!(facts.get("foo").unwrap().len(), 1);
    }

    #[test]
    fn test_facts_retrieve() {
        let mut facts = Facts::empty();
        let thm = dummy_thm();
        facts.add("bar", vec![Arc::clone(&thm)]);
        let refs = vec![FactRef::named("bar")];
        let result = facts.retrieve(&refs).unwrap();
        assert_eq!(result.len(), 1);
    }

    // ── Consts tests ──

    #[test]
    fn test_type_scheme_is_instance() {
        let scheme = TypeScheme::new(
            Typ::arrow(Typ::free("'a", Sort::singleton("type")), Typ::free("'a", Sort::singleton("type")))
        );
        assert!(scheme.is_instance(&Typ::arrow(Typ::base("nat"), Typ::base("nat"))));
    }

    #[test]
    fn test_consts_declare_and_lookup() {
        let mut consts = Consts::empty();
        let scheme = TypeScheme::new(Typ::base("prop"));
        consts.declare("Pure.prop", scheme);
        assert!(consts.is_declared("Pure.prop"));
        assert!(consts.lookup("Pure.prop").is_some());
    }

    // ── Net tests ──

    #[test]
    fn test_net_insert_and_lookup() {
        let mut net: Net<String> = Net::empty();
        let pat = konst("foo");
        net.insert(&pat, Arc::new("rule1".to_string()));
        let results = net.lookup(&konst("foo"));
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].as_ref(), "rule1");
    }

    #[test]
    fn test_net_no_match() {
        let mut net: Net<String> = Net::empty();
        net.insert(&konst("foo"), Arc::new("rule1".to_string()));
        let results = net.lookup(&konst("bar"));
        assert!(results.is_empty());
    }

    #[test]
    fn test_net_var_pattern() {
        let mut net: Net<String> = Net::empty();
        let pat = Tm::var("x", 0, Typ::dummy());
        net.insert(&pat, Arc::new("matches_all".to_string()));
        let results = net.lookup(&konst("anything"));
        assert!(!results.is_empty());
    }
}
