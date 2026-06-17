//! Order-sorted algebra of type classes.
//! Corresponds to src/Pure/sorts.ML.
//!
//! ## Concepts
//!
//! - **Class**: A type class like `type`, `ord`, `order`, `ring`.
//! - **Sort**: An intersection of classes, e.g., `{type}`, `{ord, order}`. A type belongs to a sort
//!   if it belongs to ALL classes in the sort.
//! - **Subclass**: `order ⊆ ord` means order is a subclass of ord.
//! - **Arity**: `list :: (type) list` means `list` takes one type argument and the result type
//!   class is `list` (a type-class-less declaration). `list :: (ord) ord` means `'a list` is in
//!   `ord` if `'a` is in `ord`.
//! - **Sort checking** (`of_sort`): Can a type have a given sort?

use std::collections::{BTreeSet, HashMap, HashSet};

use super::types::{Sort, Symbol, Typ};

// =========================================================================
// Sort Algebra
// =========================================================================

/// The order-sorted algebra of type classes.
///
/// Maintains:
/// - A class graph (subclass relation, acyclic + transitive)
/// - An arity table (type constructor arities)
#[derive(Clone, Debug)]
pub struct Algebra {
    /// Class graph: class → its direct superclasses
    class_graph: HashMap<Symbol, Vec<Symbol>>,
    /// Arity table: type constructor name → list of (class, argument sorts)
    arities: HashMap<Symbol, Vec<(Symbol, Vec<Sort>)>>,
}

impl Algebra {
    /// Create an empty algebra.
    pub fn empty() -> Self {
        Algebra { class_graph: HashMap::new(), arities: HashMap::new() }
    }

    /// Create the default Pure algebra with the `type` class.
    pub fn pure() -> Self {
        let mut alg = Algebra::empty();
        alg.add_class(&Symbol::from("type"), &[]);
        alg
    }

    /// Add a class with its superclasses.
    /// `add_class(c, [s1, s2])` means c is a subclass of s1 and s2.
    pub fn add_class(&mut self, class: &Symbol, superclasses: &[Symbol]) {
        self.class_graph.insert(class.clone(), superclasses.to_vec());
        // Ensure superclasses exist in the graph
        for sup in superclasses {
            self.class_graph.entry(sup.clone()).or_default();
        }
    }

    /// Add a subclass relation: `sub ≤ sup`.
    pub fn add_classrel(&mut self, sub: &Symbol, sup: &Symbol) {
        self.class_graph.entry(sub.clone()).or_default().push(sup.clone());
        self.class_graph.entry(sup.clone()).or_default();
    }

    /// Add an arity: type constructor `t` has arity `(Ss) C`.
    /// `add_arity(t, C, [S1, S2])` means `t :: (S1, S2) C`.
    pub fn add_arity(&mut self, tycon: &Symbol, class: &Symbol, arg_sorts: Vec<Sort>) {
        self.arities.entry(tycon.clone()).or_default().push((class.clone(), arg_sorts));
    }

    /// Get all classes in the graph.
    pub fn all_classes(&self) -> Vec<&Symbol> {
        self.class_graph.keys().collect()
    }

    /// Get direct superclasses of a class.
    pub fn super_classes(&self, class: &Symbol) -> Vec<&Symbol> {
        self.class_graph.get(class).map(|v| v.iter().collect()).unwrap_or_default()
    }

    /// Check if `c1` is a subclass of `c2` (c1 ≤ c2).
    /// Uses DFS to handle transitive closure.
    pub fn class_le(&self, c1: &Symbol, c2: &Symbol) -> bool {
        if c1 == c2 {
            return true;
        }
        let mut visited = HashSet::new();
        let mut stack = vec![c1.clone()];
        while let Some(cur) = stack.pop() {
            if !visited.insert(cur.clone()) {
                continue;
            }
            if &cur == c2 {
                return true;
            }
            if let Some(supers) = self.class_graph.get(&cur) {
                for sup in supers {
                    stack.push(sup.clone());
                }
            }
        }
        false
    }

    /// Check if `c1 < c2` (strict subclass).
    pub fn class_less(&self, c1: &Symbol, c2: &Symbol) -> bool {
        c1 != c2 && self.class_le(c1, c2)
    }

    /// Check if `s1 ≤ s2` for sorts.
    /// s1 ≤ s2 iff every class in s2 has a subclass in s1.
    /// In other words: s1 is "more specific" (has more constraints) than s2.
    pub fn sort_le(&self, s1: &Sort, s2: &Sort) -> bool {
        s2.iter().all(|c2| s1.iter().any(|c1| self.class_le(c1, c2)))
    }

    /// Check if two sorts are equivalent.
    pub fn sort_eq(&self, s1: &Sort, s2: &Sort) -> bool {
        self.sort_le(s1, s2) && self.sort_le(s2, s1)
    }

    /// Check if a type can have a given sort.
    /// This is the key operation: `of_sort(alg, typ, sort)`.
    pub fn of_sort(&self, typ: &Typ, sort: &Sort) -> bool {
        match typ {
            Typ::TFree { sort: s, .. } | Typ::TVar { sort: s, .. } => {
                // A type variable has its declared sort s.
                // It belongs to sort if s ≤ sort.
                self.sort_le(s, sort)
            },
            Typ::Type { name, args } => {
                // A constructed type t(args) belongs to sort if
                // there is an arity t :: (Ss) C with C ∈ sort
                // and each arg_i has sort Ss_i.
                if let Some(arities) = self.arities.get(name) {
                    for class in sort.iter() {
                        if let Some((_, arg_sorts)) = arities.iter().find(|(c, _)| c == class) {
                            if args.len() != arg_sorts.len() {
                                return false;
                            }
                            if !args
                                .iter()
                                .zip(arg_sorts.iter())
                                .all(|(arg, s)| self.of_sort(arg, s))
                            {
                                return false;
                            }
                            return true;
                        }
                    }
                }
                // No arity found — fail
                false
            },
        }
    }

    /// Compute the minimal sort: given a type, find its minimal sort.
    /// For type variables: just return their declared sort.
    /// For constructed types: return the sort from arities.
    pub fn minimize_sort(&self, typ: &Typ) -> Sort {
        match typ {
            Typ::TFree { sort, .. } | Typ::TVar { sort, .. } => sort.clone(),
            Typ::Type { name, args: _ } => {
                if let Some(arities) = self.arities.get(name) {
                    if let Some((class, _)) = arities.first() {
                        Sort::singleton(class)
                    } else {
                        Sort::top()
                    }
                } else {
                    Sort::top()
                }
            },
        }
    }

    /// Build the class hierarchy closure: collect all superclasses reachable
    /// from the given class.
    pub fn all_super_classes(&self, class: &Symbol) -> Vec<Symbol> {
        let mut result = BTreeSet::new();
        let mut stack = vec![class.clone()];
        while let Some(cur) = stack.pop() {
            if !result.insert(cur.clone()) {
                continue;
            }
            if let Some(supers) = self.class_graph.get(&cur) {
                for sup in supers {
                    stack.push(sup.clone());
                }
            }
        }
        result.into_iter().collect()
    }

    /// Get the arities for a type constructor.
    pub fn arities_of(&self, tycon: &Symbol) -> Option<&Vec<(Symbol, Vec<Sort>)>> {
        self.arities.get(tycon)
    }

    /// Check if a sort is empty (no classes).
    pub fn is_empty_sort(sort: &Sort) -> bool {
        sort.is_empty()
    }

    /// Get the top sort (the sort containing only the `type` class).
    pub fn top_sort() -> Sort {
        Sort::top()
    }
}

impl Default for Algebra {
    fn default() -> Self {
        Algebra::pure()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(s: &str) -> Symbol {
        Symbol::from(s)
    }

    #[test]
    fn test_empty_algebra() {
        let alg = Algebra::empty();
        assert!(alg.all_classes().is_empty());
    }

    #[test]
    fn test_pure_algebra() {
        let alg = Algebra::pure();
        let type_class = sym("type");
        assert!(alg.class_le(&type_class, &type_class));
        assert!(alg.all_classes().contains(&&type_class));
    }

    #[test]
    fn test_class_hierarchy() {
        let mut alg = Algebra::pure();
        let ord = sym("ord");
        let order = sym("order");
        let linorder = sym("linorder");

        alg.add_class(&ord, &[sym("type")]);
        alg.add_class(&order, &[ord.clone()]);
        alg.add_class(&linorder, &[order.clone()]);

        assert!(alg.class_le(&linorder, &ord));
        assert!(alg.class_le(&order, &ord));
        assert!(!alg.class_le(&ord, &order));
        assert!(!alg.class_le(&ord, &linorder));
    }

    #[test]
    fn test_sort_le() {
        let mut alg = Algebra::pure();
        let ord = sym("ord");
        let order = sym("order");

        alg.add_class(&ord, &[sym("type")]);
        alg.add_class(&order, &[ord.clone()]);

        let s_order = Sort::singleton("order");
        let s_ord = Sort::singleton("ord");
        let s_type = Sort::top();

        // {order} ≤ {ord} because order ⊆ ord
        assert!(alg.sort_le(&s_order, &s_ord));
        // {ord} ≰ {order} (ord is not a subclass of order)
        assert!(!alg.sort_le(&s_ord, &s_order));
        // {type} ≤ {type}
        assert!(alg.sort_le(&s_type, &s_type));
    }

    #[test]
    fn test_of_sort() {
        let mut alg = Algebra::pure();
        let ord = sym("ord");
        alg.add_class(&ord, &[sym("type")]);

        // Declare arity: list :: (type) type, list :: (ord) ord
        alg.add_arity(&sym("list"), &sym("type"), vec![Sort::top()]);
        alg.add_arity(&sym("list"), &ord, vec![Sort::singleton("ord")]);

        // 'a::type list : type
        let a_type = Typ::free("'a", Sort::top());
        let list_a = Typ::apply("list", vec![a_type.clone()]);
        assert!(alg.of_sort(&list_a, &Sort::top()));

        // 'a::ord list : ord
        let a_ord = Typ::free("'a", Sort::singleton("ord"));
        let list_a_ord = Typ::apply("list", vec![a_ord.clone()]);
        assert!(alg.of_sort(&list_a_ord, &Sort::singleton("ord")));

        // 'a::type list : ord (should fail — need ord argument)
        assert!(!alg.of_sort(&list_a, &Sort::singleton("ord")));
    }
}
