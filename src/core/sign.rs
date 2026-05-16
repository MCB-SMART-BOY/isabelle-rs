//! Signature — the gatekeeper for type-checking.
use std::collections::HashMap;
use super::types::{ClassAlgebra, Sort, Typ, Symbol};

#[derive(Clone, Debug)]
pub enum TypeDecl { Logical { arity: usize }, Abbreviation { rhs: Typ }, Nonterminal }

#[derive(Clone, Debug)]
pub struct TypeSignature {
    types: HashMap<Symbol, TypeDecl>,
    algebra: ClassAlgebra,
    #[allow(dead_code)]
    logical_types: Vec<Symbol>,
}
impl TypeSignature {
    pub fn empty() -> Self { TypeSignature { types: HashMap::new(), algebra: ClassAlgebra::empty(), logical_types: Vec::new() } }
    pub fn add_type(&mut self, name: impl Into<Symbol>, decl: TypeDecl) { self.types.insert(name.into(), decl); }
    pub fn certify_typ(&self, typ: &Typ) -> bool {
        match typ {
            Typ::Type { name, args } => {
                if let Some(decl) = self.types.get(name) {
                    let expected = match decl { TypeDecl::Logical { arity } => *arity, _ => args.len() };
                    args.len() == expected && args.iter().all(|a| self.certify_typ(a))
                } else { false }
            }
            _ => true,
        }
    }
    pub fn algebra(&self) -> &ClassAlgebra { &self.algebra }
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

#[derive(Clone, Debug)]
pub struct ConstDecl { pub name: Symbol, pub typ: Typ }

#[derive(Clone, Debug)]
pub struct Signature { consts: HashMap<Symbol, ConstDecl>, tsig: TypeSignature }

impl Signature {
    pub fn empty() -> Self { Signature { consts: HashMap::new(), tsig: TypeSignature::default() } }
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
    pub fn declare(&mut self, name: impl Into<Symbol>, typ: Typ) { let n = name.into(); self.consts.insert(n.clone(), ConstDecl { name: n, typ }); }
    pub fn const_type(&self, name: &str) -> Option<&Typ> { self.consts.get(name).map(|d| &d.typ) }
    pub fn is_declared(&self, name: &str) -> bool { self.consts.contains_key(name) }
    pub fn tsig(&self) -> &TypeSignature { &self.tsig }
    pub fn extend(&self) -> Signature { self.clone() }
    pub fn consts(&self) -> impl Iterator<Item = &ConstDecl> { self.consts.values() }
    pub fn const_count(&self) -> usize { self.consts.len() }
}
impl Default for Signature { fn default() -> Self { Self::pure() } }

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn test_pure() { let sig = Signature::pure(); assert!(sig.is_declared("Pure.imp")); }
}
