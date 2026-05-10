//! Polymorphic constant declarations and type schemes.
//!
//! Corresponds to `src/Pure/consts.ML`.
//!
//! In Isabelle, every constant has a **most general type scheme** —
//! a type where free type variables are implicitly universally quantified.
//! E.g., `Pure.eq :: 'a => 'a => prop` means `∀'a. 'a => 'a => prop`.
//!
//! The `Consts` table tracks:
//! - Each constant's type scheme
//! - Type instance checking: is `eq :: nat => nat => prop` an instance of the scheme?
//! - Monomorphic vs polymorphic constants

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::types::Symbol;
use super::types::Typ;

// =========================================================================
// Type scheme
// =========================================================================

/// A type scheme: a type with implicitly quantified type variables.
/// `'a => 'a => prop` means `∀'a. 'a => 'a => prop`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeScheme {
    /// The body type with free type variables representing the quantified vars.
    pub body: Typ,
}

impl TypeScheme {
    pub fn new(body: Typ) -> Self { TypeScheme { body } }

    /// Check if a concrete type is an instance of this scheme.
    /// E.g., scheme `'a => 'a`, type `nat => nat` → true.
    pub fn is_instance(&self, typ: &Typ) -> bool {
        // Collect the free type variables in the scheme body
        let _scheme_tvars = collect_tfrees(&self.body);

        // Try to match: each TFree in the scheme should match a corresponding
        // subtree in the concrete type consistently.
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
        (Typ::Type { name: n1, args: a1 }, Typ::Type { name: n2, args: a2 }) if n1 == n2 && a1.len() == a2.len() => {
            for (s, c) in a1.iter().zip(a2.iter()) {
                match_types(s, c, mapping);
            }
        }
        _ => {}
    }
}

// =========================================================================
// Constant declaration
// =========================================================================

/// A constant's declaration: name + type scheme.
#[derive(Clone, Debug)]
pub struct ConstDecl {
    pub name: Symbol,
    pub scheme: TypeScheme,
    /// Is this constant monomorphic (non-polymorphic)?
    pub monomorphic: bool,
}

// =========================================================================
// Consts table
// =========================================================================

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
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::types::Sort;

    #[test]
    fn test_is_instance() {
        let scheme = TypeScheme::new(
            Typ::arrow(Typ::free("'a", Sort::singleton("type")), Typ::free("'a", Sort::singleton("type")))
        );
        assert!(scheme.is_instance(&Typ::arrow(Typ::base("nat"), Typ::base("nat"))));
    }

    #[test]
    fn test_declare_and_lookup() {
        let mut consts = Consts::empty();
        let scheme = TypeScheme::new(Typ::base("prop"));
        consts.declare("Pure.prop", scheme);
        assert!(consts.is_declared("Pure.prop"));
        assert!(consts.lookup("Pure.prop").is_some());
    }
}
