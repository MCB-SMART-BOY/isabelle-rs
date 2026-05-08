//! Variable name management — fresh names, import/export, focus.
//!
//! Corresponds to `src/Pure/variable.ML`.
//!
//! Variable operations are critical for proof manipulation:
//! - **Fresh names**: generate variable names that don't clash
//! - **Import/export**: move terms between contexts
//! - **Focus**: extract subgoals from a goal term
//! - **Polymorphic**: generalize free variables

use std::collections::BTreeSet;
use std::sync::Arc;

use super::term::Term;
use super::types::Symbol;
use super::types::Typ;

// =========================================================================
// Name context — tracks used names
// =========================================================================

/// A name context tracks which variable names are in use,
/// allowing generation of fresh (unused) names.
#[derive(Clone, Debug, Default)]
pub struct NameContext {
    used: BTreeSet<String>,
}

impl NameContext {
    pub fn new() -> Self {
        NameContext { used: BTreeSet::new() }
    }

    /// Declare a name as used.
    pub fn declare(&mut self, name: &str) {
        self.used.insert(name.to_string());
    }

    /// Check if a name is already used.
    pub fn is_used(&self, name: &str) -> bool {
        self.used.contains(name)
    }

    /// Generate a variant of `name` that is not in the used set.
    /// E.g., `x` → `xa` → `xb` → ...
    pub fn variant(&mut self, base: &str) -> String {
        if !self.is_used(base) {
            self.declare(base);
            return base.to_string();
        }
        // Try appending a, b, c, ...
        for suffix in &["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"] {
            let candidate = format!("{base}{suffix}");
            if !self.is_used(&candidate) {
                self.declare(&candidate);
                return candidate;
            }
        }
        // Fall back to numeric suffixes
        for i in 0..1000 {
            let candidate = format!("{base}{i}");
            if !self.is_used(&candidate) {
                self.declare(&candidate);
                return candidate;
            }
        }
        panic!("NameContext: exhausted variants for '{base}'")
    }

    /// Generate multiple fresh variants.
    pub fn variants(&mut self, bases: &[&str]) -> Vec<String> {
        bases.iter().map(|b| self.variant(b)).collect()
    }

    /// Merge another name context into this one.
    pub fn merge(&mut self, other: &NameContext) {
        for name in &other.used {
            self.used.insert(name.clone());
        }
    }
}

// =========================================================================
// Free variable collection
// =========================================================================

/// Collect all free variable names from a term.
pub fn free_vars(term: &Term) -> BTreeSet<String> {
    let mut frees = BTreeSet::new();
    collect_frees(term, &mut frees);
    frees
}

fn collect_frees(term: &Term, frees: &mut BTreeSet<String>) {
    match term {
        Term::Free { name, .. } => { frees.insert(name.to_string()); }
        Term::Abs { body, .. } => collect_frees(body, frees),
        Term::App { func, arg } => {
            collect_frees(func, frees);
            collect_frees(arg, frees);
        }
        _ => {}
    }
}

/// Collect all schematic variable names.
pub fn schematic_vars(term: &Term) -> BTreeSet<(String, usize)> {
    let mut vars = BTreeSet::new();
    collect_svars(term, &mut vars);
    vars
}

fn collect_svars(term: &Term, vars: &mut BTreeSet<(String, usize)>) {
    match term {
        Term::Var { name, index, .. } => { vars.insert((name.to_string(), *index)); }
        Term::Abs { body, .. } => collect_svars(body, vars),
        Term::App { func, arg } => {
            collect_svars(func, vars);
            collect_svars(arg, vars);
        }
        _ => {}
    }
}
// =========================================================================
// Import / Export
// =========================================================================

/// Import a term into a context: replace all free variables with
/// schematic variables (so they can be instantiated during proof).
pub fn import_terms(terms: &[Term]) -> Vec<Term> {
    let mut frees = BTreeSet::new();
    for t in terms {
        collect_frees(t, &mut frees);
    }

    let mut names = NameContext::new();
    let mut mapping: Vec<(String, (Symbol, usize))> = Vec::new();

    let mut sorted_frees: Vec<&String> = frees.iter().collect();
    sorted_frees.sort();
    for f in sorted_frees {
        let fresh = names.variant(f);
        mapping.push((f.clone(), (Arc::from(fresh), 0)));
    }

    // Replace frees with schematic vars
    terms.iter().map(|t| replace_frees(t, &mapping)).collect()
}

fn replace_frees(term: &Term, mapping: &[(String, (Symbol, usize))]) -> Term {
    match term {
        Term::Free { name, typ } => {
            for (free_name, (var_name, var_idx)) in mapping {
                if name.as_ref() == free_name {
                    return Term::var(Arc::clone(var_name), *var_idx, typ.clone());
                }
            }
            term.clone()
        }
        Term::Abs { name, typ, body } => {
            Term::abs(Arc::clone(name), typ.clone(), replace_frees(body, mapping))
        }
        Term::App { func, arg } => {
            Term::app(replace_frees(func, mapping), replace_frees(arg, mapping))
        }
        _ => term.clone(),
    }
}

/// Export: schematic vars → free vars (reverse of import).
pub fn export_terms(terms: &[Term]) -> Vec<Term> {
    let mut vars = BTreeSet::new();
    for t in terms {
        collect_svars(t, &mut vars);
    }
    let mut names = NameContext::new();
    let mut mapping: Vec<((Symbol, usize), String)> = Vec::new();
    for (name, idx) in &vars {
        let fresh = names.variant(name);
        mapping.push(((Arc::from(name.as_str()), *idx), fresh));
    }
    terms.iter().map(|t| replace_svars(t, &mapping)).collect()
}

fn replace_svars(term: &Term, mapping: &[((Symbol, usize), String)]) -> Term {
    match term {
        Term::Var { name, index, typ } => {
            for ((n, i), free_name) in mapping {
                if name == n && *index == *i {
                    return Term::free(free_name.as_str(), typ.clone());
                }
            }
            term.clone()
        }
        Term::Abs { name, typ, body } => {
            Term::abs(Arc::clone(name), typ.clone(), replace_svars(body, mapping))
        }
        Term::App { func, arg } => {
            Term::app(replace_svars(func, mapping), replace_svars(arg, mapping))
        }
        _ => term.clone(),
    }
}

// =========================================================================
// Focus: extract subgoals
// =========================================================================

/// Break an implication chain into subgoals and a conclusion.
/// `A ==> B ==> C` → `(Some [A, B], C)`
pub fn focus_goal(goal: &Term) -> (Vec<Term>, Term) {
    let mut prems = Vec::new();
    let mut body = goal;
    while let Term::App { func, arg } = body {
        if let Term::App { func: inner, arg: a } = func.as_ref() {
            if let Term::Const { name, .. } = inner.as_ref() {
                if name.as_ref() == "Pure.imp" {
                    prems.push(a.as_ref().clone());
                    body = arg;
                    continue;
                }
            }
        }
        break;
    }
    (prems, body.clone())
}

// =========================================================================
// Polymorphic generalization
// =========================================================================

/// Generalize all free variables in a term to schematic variables.
/// The maxidx parameter controls the starting index for new vars.
pub fn polymorphic(term: &Term, maxidx: usize) -> Term {
    let frees = free_vars(term);
    let mut idx = maxidx;
    let mut result = term.clone();
    for f in &frees {
        idx += 1;
        result = replace_free_with_var(&result, f, idx);
    }
    result
}

fn replace_free_with_var(term: &Term, free_name: &str, var_idx: usize) -> Term {
    match term {
        Term::Free { name, typ } if name.as_ref() == free_name => {
            Term::var(Arc::clone(name), var_idx, typ.clone())
        }
        Term::Abs { name, typ, body } => {
            Term::abs(Arc::clone(name), typ.clone(), replace_free_with_var(body, free_name, var_idx))
        }
        Term::App { func, arg } => {
            Term::app(
                replace_free_with_var(func, free_name, var_idx),
                replace_free_with_var(arg, free_name, var_idx),
            )
        }
        _ => term.clone(),
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_variant() {
        let mut nc = NameContext::new();
        assert_eq!(nc.variant("x"), "x");
        assert_eq!(nc.variant("x"), "xa");
        assert_eq!(nc.variant("x"), "xb");
    }

    #[test]
    fn test_free_vars() {
        let x = Term::free("x", Typ::dummy());
        let y = Term::free("y", Typ::dummy());
        let t = Term::app(x, y);
        let frees = free_vars(&t);
        assert!(frees.contains("x"));
        assert!(frees.contains("y"));
        assert_eq!(frees.len(), 2);
    }

    #[test]
    fn test_import_export() {
        let t = Term::free("x", Typ::dummy());
        let imported = import_terms(&[t.clone()]);
        match &imported[0] {
            Term::Var { .. } => { /* ok */ }
            _ => panic!("expected Var after import"),
        }
        let exported = export_terms(&imported);
        match &exported[0] {
            Term::Free { name, .. } => assert_eq!(name.as_ref(), "x"),
            _ => panic!("expected Free after export"),
        }
    }

    #[test]
    fn test_focus_goal() {
        // A ==> B ==> C
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let c = Term::const_("C", Typ::base("prop"));
        let imp = Term::app(
            Term::app(Term::const_("Pure.imp", Typ::dummy()), a.clone()),
            Term::app(
                Term::app(Term::const_("Pure.imp", Typ::dummy()), b.clone()),
                c.clone(),
            ),
        );
        let (prems, conc) = focus_goal(&imp);
        assert_eq!(prems.len(), 2);
        assert_eq!(conc, c);
    }

    #[test]
    fn test_polymorphic() {
        let t = Term::free("x", Typ::base("nat"));
        let result = polymorphic(&t, 10);
        match &result {
            Term::Var { name, index, .. } => {
                assert_eq!(name.as_ref(), "x");
                assert_eq!(*index, 11);
            }
            _ => panic!("expected Var"),
        }
    }
}
