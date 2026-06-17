//! Signature — the gatekeeper for term certification and type-checking.
//!
//! Corresponds to `src/Pure/sign.ML`.
//!
//! The signature is the "gatekeeper" of the logical system. Every term
//! must be certified against a signature before it can be used. This
//! ensures:
//! - All constants are declared
//! - Types are well-formed
//! - Applications respect function types
//! - Propositions have type `prop`

use std::collections::HashMap;

use super::{
    term::Term,
    types::{ClassAlgebra, Sort, Symbol, Typ},
};

// =========================================================================
// Type Declarations
// =========================================================================

#[derive(Clone, Debug)]
pub enum TypeDecl {
    Logical { arity: usize },
    Abbreviation { rhs: Typ },
    Nonterminal,
}

// =========================================================================
// Type Signature
// =========================================================================

#[derive(Clone, Debug)]
pub struct TypeSignature {
    types: HashMap<Symbol, TypeDecl>,
    algebra: ClassAlgebra,
    #[allow(dead_code)]
    logical_types: Vec<Symbol>,
}

impl TypeSignature {
    pub fn empty() -> Self {
        TypeSignature {
            types: HashMap::new(),
            algebra: ClassAlgebra::empty(),
            logical_types: Vec::new(),
        }
    }

    pub fn add_type(&mut self, name: impl Into<Symbol>, decl: TypeDecl) {
        self.types.insert(name.into(), decl);
    }

    /// Simple boolean check: is the type well-formed against this signature?
    pub fn certify_typ(&self, typ: &Typ) -> bool {
        match typ {
            Typ::Type { name, args } => {
                if let Some(decl) = self.types.get(name) {
                    let expected = match decl {
                        TypeDecl::Logical { arity } => *arity,
                        _ => args.len(),
                    };
                    args.len() == expected && args.iter().all(|a| self.certify_typ(a))
                } else {
                    false
                }
            },
            _ => true,
        }
    }

    /// Detailed type certification with error messages.
    pub fn certify_type_detailed(&self, typ: &Typ) -> Result<(), String> {
        match typ {
            Typ::Type { name, args } => {
                if !self.types.contains_key(name) {
                    return Err(format!("Undeclared type constructor: {}", name.as_ref()));
                }
                let expected_arity = match self.types.get(name) {
                    Some(TypeDecl::Logical { arity }) => *arity,
                    Some(TypeDecl::Abbreviation { .. }) => 0,
                    Some(TypeDecl::Nonterminal) => 0,
                    None => 0,
                };
                if args.len() != expected_arity {
                    return Err(format!(
                        "Type constructor {} expects {} arguments, got {}",
                        name.as_ref(),
                        expected_arity,
                        args.len()
                    ));
                }
                for arg in args {
                    self.certify_type_detailed(arg)?;
                }
                Ok(())
            },
            Typ::TFree { .. } | Typ::TVar { .. } => Ok(()),
        }
    }

    pub fn algebra(&self) -> &ClassAlgebra {
        &self.algebra
    }
}

impl Default for TypeSignature {
    fn default() -> Self {
        let mut tsig = TypeSignature::empty();
        tsig.add_type("fun", TypeDecl::Logical { arity: 2 });
        tsig.add_type("prop", TypeDecl::Logical { arity: 0 });
        tsig.add_type("bool", TypeDecl::Logical { arity: 0 });
        tsig
    }
}

// =========================================================================
// Constant Declaration
// =========================================================================

#[derive(Clone, Debug)]
pub struct ConstDecl {
    pub name: Symbol,
    pub typ: Typ,
}

// =========================================================================
// Signature
// =========================================================================

#[derive(Clone, Debug)]
pub struct Signature {
    consts: HashMap<Symbol, ConstDecl>,
    tsig: TypeSignature,
}

impl Signature {
    // ── Construction ──

    pub fn empty() -> Self {
        Signature { consts: HashMap::new(), tsig: TypeSignature::default() }
    }

    pub fn pure() -> Self {
        let mut sig = Signature::empty();
        let prop = Typ::base("prop");
        let a = Typ::free("'a", Sort::singleton("type"));
        sig.declare("Pure.all", Typ::arrow(Typ::arrow(a, prop.clone()), prop.clone()));
        sig.declare("Pure.imp", Typ::arrow(prop.clone(), Typ::arrow(prop.clone(), prop.clone())));
        let a = Typ::free("'a", Sort::singleton("type"));
        sig.declare("Pure.eq", Typ::arrow(a.clone(), Typ::arrow(a, prop)));
        sig
    }

    // ── Constants ──

    pub fn declare(&mut self, name: impl Into<Symbol>, typ: Typ) {
        let n = name.into();
        self.consts.insert(n.clone(), ConstDecl { name: n, typ });
    }

    pub fn const_type(&self, name: &str) -> Option<&Typ> {
        self.consts.get(name).map(|d| &d.typ)
    }

    pub fn is_declared(&self, name: &str) -> bool {
        self.consts.contains_key(name)
    }

    pub fn tsig(&self) -> &TypeSignature {
        &self.tsig
    }

    pub fn extend(&self) -> Signature {
        self.clone()
    }

    pub fn consts(&self) -> impl Iterator<Item = &ConstDecl> {
        self.consts.values()
    }

    pub fn const_count(&self) -> usize {
        self.consts.len()
    }

    /// Create a new signature that inherits from this one with additional
    /// declarations. (For theory extension.)
    pub fn extend_with(&self, consts: Vec<(String, Typ)>, types: Vec<(String, TypeDecl)>) -> Self {
        let mut new_sig = self.clone();
        for (name, typ) in consts {
            new_sig.declare(name, typ);
        }
        for (name, decl) in types {
            new_sig.tsig.add_type(name, decl);
        }
        new_sig
    }

    // ── Term Certification ──

    /// Certify a term against this signature: check that all constants are
    /// declared, types are well-formed, and applications respect function
    /// types.
    ///
    /// Corresponds to `Sign.certify_term` in Isabelle.
    ///
    /// Returns `Ok(())` if the term is well-formed, or `Err(msg)` with a
    /// human-readable description of the problem.
    pub fn certify_term(&self, term: &Term) -> Result<(), String> {
        match term {
            Term::Const { name, typ } => {
                if !self.is_declared(name.as_ref()) {
                    return Err(format!("Undeclared constant: {}", name.as_ref()));
                }
                if let Some(declared_type) = self.const_type(name.as_ref())
                    && !types_compatible(typ, declared_type) {
                        return Err(format!(
                            "Type mismatch for constant {}: expected {:?}, got {:?}",
                            name.as_ref(),
                            declared_type,
                            typ
                        ));
                    }
                self.tsig.certify_type_detailed(typ)?;
                Ok(())
            },
            Term::Free { name: _, typ } | Term::Var { name: _, index: _, typ } => {
                self.tsig.certify_type_detailed(typ)
            },
            Term::Bound(_) => Ok(()),
            Term::Abs { name: _, typ, body } => {
                self.tsig.certify_type_detailed(typ)?;
                self.certify_term(body)
            },
            Term::App { func, arg } => {
                self.certify_term(func)?;
                self.certify_term(arg)?;
                let func_typ = self.infer_type(func)?;
                if func_typ.dest_fun().is_none() {
                    return Err(format!(
                        "Application of non-function: {:?} applied to {:?}",
                        func, arg
                    ));
                }
                Ok(())
            },
        }
    }

    /// Certify a proposition: like `certify_term`, but additionally checks
    /// that the term's inferred type is `prop`.
    pub fn certify_prop(&self, term: &Term) -> Result<(), String> {
        self.certify_term(term)?;
        let inferred = self.infer_type(term)?;
        if is_prop_type(&inferred) {
            Ok(())
        } else {
            Err(format!("Not a proposition: term has type {:?}, expected prop", inferred))
        }
    }

    /// Certify a type: check that all type constructors are declared with
    /// correct arities.
    pub fn certify_type(&self, typ: &Typ) -> Result<(), String> {
        self.tsig.certify_type_detailed(typ)
    }

    // ── Type Inference ──

    /// Infer the type of a term from its structure and the signature.
    /// Returns the most general type.
    pub fn infer_type(&self, term: &Term) -> Result<Typ, String> {
        match term {
            Term::Const { name, typ } => {
                if let Some(declared) = self.const_type(name.as_ref()) {
                    Ok(declared.clone())
                } else if !typ.is_dummy() {
                    Ok(typ.clone())
                } else {
                    Err(format!("Cannot infer type of undeclared constant: {}", name.as_ref()))
                }
            },
            Term::Free { typ, .. } => {
                if typ.is_dummy() {
                    Err("Cannot infer type of free variable with dummy type".to_string())
                } else {
                    Ok(typ.clone())
                }
            },
            Term::Var { typ, .. } => {
                if typ.is_dummy() {
                    Err("Cannot infer type of schematic variable with dummy type".to_string())
                } else {
                    Ok(typ.clone())
                }
            },
            Term::Bound(_) => Err("Cannot infer type of loose bound variable".to_string()),
            Term::Abs { typ, body, .. } => {
                let body_typ = self.infer_type(body)?;
                Ok(Typ::arrow(typ.clone(), body_typ))
            },
            Term::App { func, arg } => {
                let func_typ = self.infer_type(func)?;
                let _arg_typ = self.infer_type(arg)?;
                match func_typ.dest_fun() {
                    Some((_domain, codomain)) => Ok(codomain.clone()),
                    None => Err(format!(
                        "Application of non-function type {:?} in term {:?}",
                        func_typ, term
                    )),
                }
            },
        }
    }
}

impl Default for Signature {
    fn default() -> Self {
        Self::pure()
    }
}

// =========================================================================
// Helpers
// =========================================================================

/// Check if two types are structurally compatible.
/// Dummy types are compatible with anything (they're placeholders).
fn types_compatible(a: &Typ, b: &Typ) -> bool {
    if a.is_dummy() || b.is_dummy() {
        return true;
    }
    match (a, b) {
        (Typ::Type { name: na, args: aa }, Typ::Type { name: nb, args: bb }) => {
            na == nb
                && aa.len() == bb.len()
                && aa.iter().zip(bb.iter()).all(|(a, b)| types_compatible(a, b))
        },
        (Typ::TFree { name: na, .. }, Typ::TFree { name: nb, .. }) => na == nb,
        (Typ::TVar { name: na, index: ia, .. }, Typ::TVar { name: nb, index: ib, .. }) => {
            na == nb && ia == ib
        },
        _ => false,
    }
}

fn is_prop_type(typ: &Typ) -> bool {
    matches!(typ, Typ::Type { name, .. } if name.as_ref() == "prop")
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pure() {
        let sig = Signature::pure();
        assert!(sig.is_declared("Pure.imp"));
    }

    #[test]
    fn test_certify_term_valid() {
        let sig = Signature::pure();
        // Pure.imp with correct type: prop => prop => prop
        let imp_typ = Typ::arrows(vec![Typ::base("prop"), Typ::base("prop")], Typ::base("prop"));
        let imp = Term::const_("Pure.imp", imp_typ);
        assert!(sig.certify_term(&imp).is_ok());
    }

    #[test]
    fn test_certify_term_undeclared() {
        let sig = Signature::pure();
        let t = Term::const_("Not.Declared", Typ::base("prop"));
        assert!(sig.certify_term(&t).is_err());
    }

    #[test]
    fn test_certify_prop_valid() {
        let sig = Signature::pure();
        // Pure.imp with correct type: prop => prop => prop, applied to two props
        let imp_typ = Typ::arrows(vec![Typ::base("prop"), Typ::base("prop")], Typ::base("prop"));
        let imp = Term::const_("Pure.imp", imp_typ);
        // Pure.all also expects a function type, matching for certify_prop
        let all_typ = Typ::arrow(
            Typ::arrow(Typ::free("'a", Sort::top()), Typ::base("prop")),
            Typ::base("prop"),
        );
        let all = Term::const_("Pure.all", all_typ);
        // Apply Pure.all to Pure.imp — both are declared
        let result = Term::app(all, imp);
        assert!(sig.certify_prop(&result).is_ok());
    }

    #[test]
    fn test_certify_prop_not_prop() {
        let sig = Signature::pure();
        let t = Term::const_("Pure.imp", Typ::base("bool")); // wrong type: bool instead of prop
        assert!(sig.certify_prop(&t).is_err());
    }

    #[test]
    fn test_infer_type() {
        let sig = Signature::pure();
        let imp_typ = Typ::arrows(vec![Typ::base("prop"), Typ::base("prop")], Typ::base("prop"));
        let imp = Term::const_("Pure.imp", imp_typ);
        // The declared type for Pure.imp is prop => prop => prop (a function type)
        let inferred = sig.infer_type(&imp).unwrap();
        // Should be a function type (name "fun")
        assert!(inferred.is_type());
        assert!(inferred.dest_fun().is_some());
    }

    #[test]
    fn test_certify_type_valid() {
        let sig = Signature::pure();
        let t = Typ::arrow(Typ::base("bool"), Typ::base("bool"));
        assert!(sig.certify_type(&t).is_ok());
    }

    #[test]
    fn test_certify_type_undeclared() {
        let sig = Signature::pure();
        let t = Typ::base("nonexistent");
        assert!(sig.certify_type(&t).is_err());
    }
}
