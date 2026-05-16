//! Structured error types for Isabelle-rs.
//!
//! Replaces ad-hoc String/panic with typed errors throughout.
//! Uses `thiserror` for ergonomic error derivation.

use thiserror::Error;

/// Top-level Isabelle error.
#[derive(Error, Debug)]
pub enum IsabelleError {
    /// Kernel error — a bug in the trusted core.
    #[error("kernel error: {0}")]
    Kernel(#[from] KernelError),

    /// Type system error.
    #[error("type error: {0}")]
    Type(#[from] TypeError),

    /// Proof error — proof search failure.
    #[error("proof error: {0}")]
    Proof(#[from] ProofError),

    /// I/O error.
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),

    /// Parse error.
    #[error("parse error at {pos}: {msg}")]
    Parse { msg: String, pos: usize },

    /// Configuration error.
    #[error("config: {0}")]
    Config(String),
}

/// Kernel errors — invariant violations in the trusted core.
#[derive(Error, Debug)]
pub enum KernelError {
    /// Not an equality where one was expected.
    #[error("not an equality: {0:?}")]
    NotEquality(crate::core::term::Term),

    /// Not an implication where one was expected.
    #[error("not an implication: {0:?}")]
    NotImplication(crate::core::term::Term),

    /// Undeclared constant.
    #[error("undeclared constant: {0}")]
    UndeclaredConstant(String),

    /// Type mismatch.
    #[error("type mismatch: expected {expected:?}, got {actual:?}")]
    TypeMismatch {
        expected: crate::core::types::Typ,
        actual: crate::core::types::Typ,
    },

    /// Occurs check failed.
    #[error("occurs check: {var} occurs in {term:?}")]
    OccursCheck { var: String, term: crate::core::term::Term },

    /// Hypothesis not found.
    #[error("hypothesis not found in assumptions")]
    HypothesisNotFound,

    /// Free variable in hypotheses during forall_intr.
    #[error("free var '{name}' in hypotheses for forall_intr")]
    FreeVarInHypotheses { name: String },

    /// Beta conversion applied to non-redex.
    #[error("beta_conversion: {0}")]
    BetaConversion(String),
}

/// Type system errors.
#[derive(Error, Debug)]
pub enum TypeError {
    #[error("type {0:?} not declared in signature")]
    UndeclaredType(String),
    #[error("arity mismatch for {name}: expected {expected}, got {actual}")]
    ArityMismatch { name: String, expected: usize, actual: usize },
    #[error("sort mismatch: cannot satisfy {0:?}")]
    SortMismatch(crate::core::types::Sort),
}

/// Proof errors.
#[derive(Error, Debug)]
pub enum ProofError {
    #[error("no unifier found")]
    NoUnifier,
    #[error("search bound exceeded ({0})")]
    SearchBound(usize),
    #[error("tactic failed")]
    TacticFailed,
    #[error("method not found: {0}")]
    MethodNotFound(String),
}

/// Convenience Result type.
pub type Result<T> = std::result::Result<T, IsabelleError>;
