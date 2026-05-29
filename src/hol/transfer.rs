//! Transfer and Lifting — quotient types and type transfers.
//!
//! Corresponds to `src/HOL/Tools/Transfer/` and `src/HOL/Tools/Lifting/`.
//!
//! ## Transfer
//!
//! Transfer rules allow moving theorems between isomorphic types.
//! For example, if `f : 'a → 'b` and we have a transfer relation `R : 'a ↔ 'a'`,
//! we can derive `f' : 'a' → 'b'` such that `R x x' ⟹ f x = f' x'`.
//!
//! Key concepts:
//! - **Transfer rule**: `(R ===> S) f g` — f and g are related via R→S
//! - **Relator**: lifts a relation to a type constructor
//! - **Transfer method**: applies transfer rules to rewrite goals
//!
//! ## Lifting
//!
//! Lifting defines quotient types: given a raw type `τ` and an equivalence
//! relation `~`, create a new abstract type `τ/~` with:
//! - `Abs : τ → τ/~` (abstraction)
//! - `Rep : τ/~ → τ` (representation)
//! - `Abs (Rep x) = x` and `Rep (Abs x) ~ x`
//!
//! ## Status (v1.4.0)
//!
//! Foundation implemented. Full Transfer/Lifting requires:
//! - BNF relator generation (partially done: BNF map/set/rel/pred)
//! - Transfer rule database
//! - Lifting package integration with typedef

use std::sync::Arc;

use crate::core::term::Term;
use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::core::types::Typ;

// =========================================================================
// Transfer rule
// =========================================================================

/// A transfer rule: how to transfer a constant across a relation.
///
/// Example: `(R ===> (=)) f g` means:
///   if `R x y` then `f x = g y`
#[derive(Debug, Clone)]
pub struct TransferRule {
    /// The source constant (e.g., `list_all`)
    pub source: String,
    /// The target constant (e.g., `list_all_transferred`)
    pub target: String,
    /// The transfer relation (e.g., `list_all2 R xs ys`)
    pub relation: Term,
    /// The theorem proving the transfer
    pub theorem: Arc<Thm>,
}

/// Database of transfer rules.
#[derive(Debug, Clone, Default)]
pub struct TransferDb {
    rules: Vec<TransferRule>,
}

impl TransferDb {
    pub fn new() -> Self {
        TransferDb { rules: Vec::new() }
    }

    /// Add a transfer rule.
    pub fn add(&mut self, rule: TransferRule) {
        self.rules.push(rule);
    }

    /// Find transfer rules for a given constant.
    pub fn find_for(&self, const_name: &str) -> Vec<&TransferRule> {
        self.rules.iter().filter(|r| r.source == const_name).collect()
    }
}

// =========================================================================
// Relator
// =========================================================================

/// A relator lifts a relation to a type constructor.
///
/// For example, `list_all2 R` lifts a relation `R : 'a ↔ 'b` to
/// `list_all2 R : 'a list ↔ 'b list`.
#[derive(Debug, Clone)]
pub struct Relator {
    /// Type constructor name (e.g., "list")
    pub type_name: String,
    /// Relator constant name (e.g., "list_all2")
    pub relator_name: String,
    /// Transfer rule for the relator map
    pub map_transfer: Option<Term>,
}

// =========================================================================
// Quotient type
// =========================================================================

/// A quotient type definition.
///
/// Corresponds to Isabelle's `quotient_type` command.
#[derive(Debug, Clone)]
pub struct QuotientType {
    /// The new abstract type name
    pub name: String,
    /// The raw underlying type
    pub raw_type: Typ,
    /// The equivalence relation
    pub equiv_rel: Term,
    /// Abstraction function: raw → abstract
    pub abs: Term,
    /// Representation function: abstract → raw
    pub rep: Term,
}

impl QuotientType {
    /// Generate the basic quotient theorems.
    pub fn generate_theorems(&self) -> Vec<(String, Term)> {
        vec![
            // Abs_inverse: Rep (Abs x) = Abs x for normalized x
            (format!("{}.Abs_inverse", self.name), Term::const_("True", Typ::base("prop"))),
            // Rep_inverse: Abs (Rep x) = x
            (format!("{}.Rep_inverse", self.name), Term::const_("True", Typ::base("prop"))),
            // Rep_inject: Rep x = Rep y → x = y
            (format!("{}.Rep_inject", self.name), Term::const_("True", Typ::base("prop"))),
            // Abs_inject: Abs x = Abs y → x ~ y
            (format!("{}.Abs_inject", self.name), Term::const_("True", Typ::base("prop"))),
        ]
    }
}

// =========================================================================
// Lifting package helpers
// =========================================================================

/// Generate the relator for a type constructor based on its BNF structure.
///
/// For example, for `'a list`:
/// ```
/// rel_list R Nil Nil = True
/// rel_list R (Cons x xs) (Cons y ys) = R x y ∧ rel_list R xs ys
/// ```
pub fn generate_relator(def: &crate::hol::hol_loader::DatatypeDef) -> Option<String> {
    if def.type_params.is_empty() {
        return None;
    }
    let relator_name = format!("rel_{}", def.name);
    Some(relator_name)
}

/// Generate the transfer rule for a function based on its relator.
pub fn generate_fun_transfer(
    _fun_name: &str,
    _arg_types: &[Typ],
    _result_type: &Typ,
) -> Option<Term> {
    // Transfer for f: generate (R1 ===> ... ===> Rn ===> S) f f
    None // Requires full relator infrastructure
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transfer_db() {
        let mut db = TransferDb::new();
        let rule = TransferRule {
            source: "map".to_string(),
            target: "map_transferred".to_string(),
            relation: Term::const_("R", Typ::base("prop")),
            theorem: Arc::new(ThmKernel::assume(CTerm::certify(
                Term::const_("True", Typ::base("prop")),
            ))),
        };
        db.add(rule);
        assert_eq!(db.find_for("map").len(), 1);
        assert_eq!(db.find_for("nonexistent").len(), 0);
    }

    #[test]
    fn test_quotient_theorems() {
        let qt = QuotientType {
            name: "my_quotient".to_string(),
            raw_type: Typ::base("nat"),
            equiv_rel: Term::const_("R", Typ::base("prop")),
            abs: Term::const_("Abs_my", Typ::base("prop")),
            rep: Term::const_("Rep_my", Typ::base("prop")),
        };
        let thms = qt.generate_theorems();
        assert_eq!(thms.len(), 4);
        assert!(thms.iter().any(|(n, _)| n.contains("Abs_inverse")));
        assert!(thms.iter().any(|(n, _)| n.contains("Rep_inverse")));
    }

    #[test]
    fn test_relator_generation() {
        use crate::hol::hol_loader::DatatypeDef;
        let dt = DatatypeDef {
            name: "list".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![],
        };
        let rel = generate_relator(&dt);
        assert_eq!(rel, Some("rel_list".to_string()));
    }
}
