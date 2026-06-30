//! Morphisms: systematic transformations of terms, types, theorems, and contexts.
//!
//! Corresponds to `src/Pure/morphism.ML`.
//!
//! A morphism is a bundle of functions that transform logical entities
//! (terms, types, facts, theorems) in a consistent way. Morphisms are
//! the foundation of:
//!
//! - **Locale interpretation**: instantiating locale parameters and assumptions
//! - **Theory extension**: adding definitions, axioms, theorems
//! - **Proof context**: instantiating schematic variables, applying substitutions
//! - **Type class instantiation**: mapping class operations to concrete types
//!
//! ## Composition
//!
//! Morphisms compose via `$` (operator composition):
//!   `morph2 $ morph1` applies morph1 then morph2
//!
//! ## Key operations
//!
//! ```text
//! morphism.term(t)      → transformed term
//! morphism.typ(T)       → transformed type
//! morphism.fact("name") → get named fact through morphism
//! morphism.thm(thm)     → transform theorem
//! ```
//!
//! ## Common morphisms
//!
//! - **identity**: no transformation (used as default)
//! - **term_morphism(f)**: only transforms terms
//! - **typ_morphism(f)**: only transforms types
//! - **subst_morphism(subst)**: applies a substitution

use std::sync::Arc;

use super::{term::Term, theory::Theory, thm::Thm, types::Typ};

// =========================================================================
// Morphism
// =========================================================================

/// A morphism bundles transformations for terms, types, and facts.
///
/// Each transformation is optional: if `None`, the entity passes through unchanged.
#[derive(Clone)]
pub struct Morphism {
    /// Term transformation: `Term → Term`.
    pub term_fn: Option<Arc<dyn Fn(&Term) -> Term + Send + Sync>>,
    /// Type transformation: `Typ → Typ`.
    pub typ_fn: Option<Arc<dyn Fn(&Typ) -> Typ + Send + Sync>>,
    /// Fact lookup override: `name → fact`.
    pub fact_fn: Option<Arc<dyn Fn(&str) -> Option<Arc<Thm>> + Send + Sync>>,
    /// Theorem transformation: `Thm → Thm`.
    pub thm_fn: Option<Arc<dyn Fn(&Thm) -> Thm + Send + Sync>>,
    /// Binding name transformation.
    pub binding_fn: Option<Arc<dyn Fn(&str) -> String + Send + Sync>>,
}

impl std::fmt::Debug for Morphism {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Morphism")
            .field("term_fn", &self.term_fn.is_some())
            .field("typ_fn", &self.typ_fn.is_some())
            .field("fact_fn", &self.fact_fn.is_some())
            .field("thm_fn", &self.thm_fn.is_some())
            .field("binding_fn", &self.binding_fn.is_some())
            .finish()
    }
}

impl Morphism {
    // ── Construction ──

    /// The identity morphism — no transformation.
    pub fn identity() -> Self {
        Morphism { term_fn: None, typ_fn: None, fact_fn: None, thm_fn: None, binding_fn: None }
    }

    /// A morphism that only transforms terms.
    pub fn term_morphism(f: impl Fn(&Term) -> Term + Send + Sync + 'static) -> Self {
        let mut m = Morphism::identity();
        m.term_fn = Some(Arc::new(f));
        m
    }

    /// A morphism that only transforms types.
    pub fn typ_morphism(f: impl Fn(&Typ) -> Typ + Send + Sync + 'static) -> Self {
        let mut m = Morphism::identity();
        m.typ_fn = Some(Arc::new(f));
        m
    }

    /// A morphism from a term substitution (maps schematic variables to terms).
    /// This is the most common morphism for locale instantiation.
    pub fn subst_morphism(subst: Vec<(Term, Term)>) -> Self {
        let subst = Arc::new(subst);
        let s = Arc::clone(&subst);
        Morphism::term_morphism(move |t| subst_term(&s, t))
    }

    /// A morphism from a type substitution (maps type variables to types).
    pub fn typ_subst_morphism(subst: Vec<(String, Typ)>) -> Self {
        let subst = Arc::new(subst);
        let s = Arc::clone(&subst);
        Morphism::typ_morphism(move |t| subst_typ(&s, t))
    }

    /// A morphism that only provides fact lookup.
    pub fn fact_morphism(f: impl Fn(&str) -> Option<Arc<Thm>> + Send + Sync + 'static) -> Self {
        let mut m = Morphism::identity();
        m.fact_fn = Some(Arc::new(f));
        m
    }

    /// A morphism that transforms theorems.
    pub fn thm_morphism(f: impl Fn(&Thm) -> Thm + Send + Sync + 'static) -> Self {
        let mut m = Morphism::identity();
        m.thm_fn = Some(Arc::new(f));
        m
    }

    // ── Application ──

    /// Apply morphism to a term.
    pub fn term(&self, t: &Term) -> Term {
        match &self.term_fn {
            Some(f) => f(t),
            None => t.clone(),
        }
    }

    /// Apply morphism to a type.
    pub fn typ(&self, t: &Typ) -> Typ {
        match &self.typ_fn {
            Some(f) => f(t),
            None => t.clone(),
        }
    }

    /// Apply morphism to an optional type.
    pub fn typ_opt(&self, t: Option<&Typ>) -> Option<Typ> {
        t.map(|t| self.typ(t))
    }

    /// Apply morphism to a theorem.
    pub fn thm(&self, thm: &Thm) -> Thm {
        match &self.thm_fn {
            Some(f) => f(thm),
            None => thm.clone(),
        }
    }

    /// Look up a fact through the morphism.
    pub fn fact(&self, name: &str) -> Option<Arc<Thm>> {
        match &self.fact_fn {
            Some(f) => f(name),
            None => None,
        }
    }

    /// Apply morphism to a binding name.
    pub fn binding(&self, name: &str) -> String {
        match &self.binding_fn {
            Some(f) => f(name),
            None => name.to_string(),
        }
    }

    /// Apply morphism to a theory's signature.
    pub fn theory(&self, thy: Arc<Theory>) -> Arc<Theory> {
        // Theory transformation through morphism is complex.
        // For now, we simply return the theory unchanged.
        // Full morphism of theory signature requires rebuilding
        // the signature with transformed constant types.
        thy
    }

    // ── Composition ──

    /// Compose two morphisms: `self $ other` applies `other` first, then `self`.
    ///
    /// ```text
    /// (m2 $ m1).term(t) = m2.term(m1.term(t))
    /// ```
    pub fn compose(&self, other: &Morphism) -> Morphism {
        let term_fn = compose_fn(&self.term_fn, &other.term_fn);
        let typ_fn = compose_fn(&self.typ_fn, &other.typ_fn);
        let thm_fn = compose_fn(&self.thm_fn, &other.thm_fn);

        // Fact lookup: try other's fact_fn first, then self's
        let fact_fn = compose_fact_fn(&self.fact_fn, &other.fact_fn);

        // Binding: self after other
        let binding_fn = compose_str_fn(&self.binding_fn, &other.binding_fn);

        Morphism { term_fn, typ_fn, fact_fn, thm_fn, binding_fn }
    }
}

impl Default for Morphism {
    fn default() -> Self {
        Morphism::identity()
    }
}

// =========================================================================
// Composition helpers
// =========================================================================

/// Compose two optional functions: `g ∘ f` (f first, then g).
fn compose_fn<T: 'static + Send + Sync>(
    g: &Option<Arc<dyn Fn(&T) -> T + Send + Sync>>,
    f: &Option<Arc<dyn Fn(&T) -> T + Send + Sync>>,
) -> Option<Arc<dyn Fn(&T) -> T + Send + Sync>> {
    match (g, f) {
        (None, None) => None,
        (Some(g), None) => Some(Arc::clone(g)),
        (None, Some(f)) => Some(Arc::clone(f)),
        (Some(g), Some(f)) => {
            let g = Arc::clone(g);
            let f = Arc::clone(f);
            Some(Arc::new(move |x: &T| g(&f(x))))
        },
    }
}

/// Compose fact lookup functions: try `f` first, then `g`.
fn compose_fact_fn(
    g: &Option<Arc<dyn Fn(&str) -> Option<Arc<Thm>> + Send + Sync>>,
    f: &Option<Arc<dyn Fn(&str) -> Option<Arc<Thm>> + Send + Sync>>,
) -> Option<Arc<dyn Fn(&str) -> Option<Arc<Thm>> + Send + Sync>> {
    match (g, f) {
        (None, None) => None,
        (Some(g), None) => Some(Arc::clone(g)),
        (None, Some(f)) => Some(Arc::clone(f)),
        (Some(g), Some(f)) => {
            let g = Arc::clone(g);
            let f = Arc::clone(f);
            Some(Arc::new(move |name: &str| f(name).or_else(|| g(name))))
        },
    }
}

/// Compose string functions.
fn compose_str_fn(
    g: &Option<Arc<dyn Fn(&str) -> String + Send + Sync>>,
    f: &Option<Arc<dyn Fn(&str) -> String + Send + Sync>>,
) -> Option<Arc<dyn Fn(&str) -> String + Send + Sync>> {
    match (g, f) {
        (None, None) => None,
        (Some(g), None) => Some(Arc::clone(g)),
        (None, Some(f)) => Some(Arc::clone(f)),
        (Some(g), Some(f)) => {
            let g = Arc::clone(g);
            let f = Arc::clone(f);
            Some(Arc::new(move |s: &str| g(&f(s))))
        },
    }
}

// =========================================================================
// Compound morphism
// =========================================================================

/// A composite morphism that applies term, type, and thm transformations.
/// This is the most common pattern when instantiating locale parameters.
#[derive(Clone, Debug)]
pub struct CompositeMorphism {
    pub morph: Morphism,
    /// Export morphism: transforms from local to global context.
    pub export: Option<Box<CompositeMorphism>>,
}

impl CompositeMorphism {
    pub fn new(morph: Morphism) -> Self {
        CompositeMorphism { morph, export: None }
    }

    /// Compose with another composite morphism.
    pub fn compose(&self, other: &CompositeMorphism) -> CompositeMorphism {
        CompositeMorphism {
            morph: self.morph.compose(&other.morph),
            export: match (&self.export, &other.export) {
                (Some(e1), Some(e2)) => Some(Box::new(e1.compose(e2))),
                (Some(e), None) => Some(e.clone()),
                (None, Some(e)) => Some(e.clone()),
                (None, None) => None,
            },
        }
    }

    /// Apply the morphism to a term, then export.
    pub fn term(&self, t: &Term) -> Term {
        let t = self.morph.term(t);
        match &self.export {
            Some(e) => e.term(&t),
            None => t,
        }
    }

    /// Apply the morphism to a theorem, then export.
    pub fn thm(&self, thm: &Thm) -> Thm {
        let thm = self.morph.thm(thm);
        match &self.export {
            Some(e) => e.thm(&thm),
            None => thm,
        }
    }
}

// =========================================================================
// Substitution implementation
// =========================================================================

/// Apply a term substitution: replace schematic variables with their bindings.
fn subst_term(subst: &[(Term, Term)], t: &Term) -> Term {
    // Simple one-pass substitution. For full substitution with bound
    // variable handling, see `core/term_subst.rs`.
    let mut result = t.clone();
    for (var, replacement) in subst {
        result = subst_single(&result, var, replacement);
    }
    result
}

/// Substitute a single variable occurrence.
fn subst_single(t: &Term, var: &Term, replacement: &Term) -> Term {
    match t {
        Term::Var { name: n1, index: i1, typ: t1 } => match var {
            Term::Var { name: n2, index: i2, typ: t2 } => {
                if n1 == n2 && i1 == i2 && t1 == t2 {
                    replacement.clone()
                } else {
                    t.clone()
                }
            },
            _ => t.clone(),
        },
        Term::Free { name: n1, typ: t1, .. } => match var {
            Term::Free { name: n2, typ: t2, .. } => {
                if n1 == n2 && t1 == t2 {
                    replacement.clone()
                } else {
                    t.clone()
                }
            },
            _ => t.clone(),
        },
        Term::Abs { name, typ, body } => {
            Term::abs(name.clone(), typ.clone(), subst_single(body, var, replacement))
        },
        Term::App { func, arg } => {
            Term::app(subst_single(func, var, replacement), subst_single(arg, var, replacement))
        },
        _ => t.clone(),
    }
}

/// Apply a type substitution: replace type variables with their bindings.
fn subst_typ(subst: &[(String, Typ)], t: &Typ) -> Typ {
    match t {
        Typ::TVar { name, index, .. } => {
            let key = format!("{}.{}", name.as_ref(), index);
            for (var_name, replacement) in subst {
                if *var_name == key || *var_name == name.as_ref() {
                    return replacement.clone();
                }
            }
            t.clone()
        },
        Typ::TFree { name, .. } => {
            for (var_name, replacement) in subst {
                if *var_name == name.as_ref() {
                    return replacement.clone();
                }
            }
            t.clone()
        },
        Typ::Type { name, args } => {
            Typ::apply(name.clone(), args.iter().map(|a| subst_typ(subst, a)).collect())
        },
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identity_morphism() {
        let m = Morphism::identity();
        let t = Term::free("x", Typ::base("bool"));
        assert_eq!(m.term(&t), t);
    }

    #[test]
    fn test_term_morphism() {
        let m = Morphism::term_morphism(|t| match t {
            Term::Free { name, .. } if name.as_ref() == "x" => {
                Term::const_("True", Typ::base("bool"))
            },
            _ => t.clone(),
        });

        let x = Term::free("x", Typ::base("bool"));
        let result = m.term(&x);
        assert!(matches!(result, Term::Const { name, .. } if name.as_ref() == "True"));

        let y = Term::free("y", Typ::base("bool"));
        let result = m.term(&y);
        assert_eq!(result, y);
    }

    #[test]
    fn test_typ_morphism() {
        let m = Morphism::typ_morphism(|t| match t {
            Typ::TFree { name, .. } if name.as_ref() == "'a" => Typ::base("nat"),
            _ => t.clone(),
        });

        let a = Typ::free("'a", super::super::types::Sort::top());
        let result = m.typ(&a);
        assert!(matches!(result, Typ::Type { name, .. } if name.as_ref() == "nat"));
    }

    #[test]
    fn test_compose() {
        let m1 = Morphism::term_morphism(|t| match t {
            Term::Free { name, .. } if name.as_ref() == "x" => Term::free("y", Typ::base("bool")),
            _ => t.clone(),
        });

        let m2 = Morphism::term_morphism(|t| match t {
            Term::Free { name, .. } if name.as_ref() == "y" => Term::free("z", Typ::base("bool")),
            _ => t.clone(),
        });

        let composed = m2.compose(&m1);
        let x = Term::free("x", Typ::base("bool"));
        let result = composed.term(&x);
        assert!(matches!(result, Term::Free { name, .. } if name.as_ref() == "z"));
    }

    #[test]
    fn test_subst_morphism() {
        let var = Term::var("?x", 0, Typ::base("bool"));
        let replacement = Term::const_("True", Typ::base("bool"));
        let m = Morphism::subst_morphism(vec![(var.clone(), replacement.clone())]);

        let result = m.term(&var);
        assert!(matches!(result, Term::Const { name, .. } if name.as_ref() == "True"));
    }

    #[test]
    fn test_fact_morphism() {
        use crate::core::thm::{CTerm, ThmKernel};

        let fact_thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(Term::const_(
            "P",
            Typ::base("bool"),
        ))));

        let m = Morphism::fact_morphism(move |name: &str| {
            if name == "my_fact" { Some(Arc::clone(&fact_thm)) } else { None }
        });

        assert!(m.fact("my_fact").is_some());
        assert!(m.fact("nonexistent").is_none());
    }

    #[test]
    fn test_typ_subst_morphism() {
        let m = Morphism::typ_subst_morphism(vec![("'a".to_string(), Typ::base("nat"))]);

        let a = Typ::free("'a", super::super::types::Sort::top());
        let result = m.typ(&a);
        assert!(matches!(result, Typ::Type { name, .. } if name.as_ref() == "nat"));
    }

    #[test]
    fn test_morphism_thread_safety() {
        // Verify morphisms can be sent across threads
        let m = Morphism::identity();
        let m2 = m.clone();
        std::thread::spawn(move || {
            let t = Term::free("x", Typ::base("bool"));
            assert_eq!(m2.term(&t), t);
        })
        .join()
        .unwrap();
    }
}
