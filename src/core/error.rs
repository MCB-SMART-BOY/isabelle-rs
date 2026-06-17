//! Structured error types for Isabelle-rs.
//!
//! Follows Rust compiler error style: error codes, source locations, suggestions.
//! Uses `thiserror` for ergonomic error derivation.
//!
//! # Error Code Ranges
//!
//! | Range | Category |
//! |-------|----------|
//! | E0001-E0099 | Kernel errors (trusted core invariants) |
//! | E0100-E0199 | Type system errors |
//! | E0200-E0299 | Proof search errors |
//! | E0300-E0399 | Parse errors |
//! | E0400-E0499 | I/O and configuration errors |

use thiserror::Error;

// ============================================================================
// Top-level error
// ============================================================================

/// Top-level Isabelle error with Rust-style formatting.
#[derive(Error, Debug)]
pub enum IsabelleError {
    /// Kernel error — a bug in the trusted core.
    #[error("{0}")]
    Kernel(#[from] KernelError),

    /// Type system error.
    #[error("{0}")]
    Type(#[from] TypeError),

    /// Proof error — proof search failure.
    #[error("{0}")]
    Proof(#[from] ProofError),

    /// Parse error.
    #[error("{0}")]
    Parse(#[from] ParseError),

    /// I/O error.
    #[error("{0}")]
    Io(#[from] std::io::Error),

    /// Configuration error.
    #[error("configuration error: {0}")]
    Config(String),
}

impl IsabelleError {
    /// Return the error code for this error.
    pub fn code(&self) -> &'static str {
        match self {
            IsabelleError::Kernel(e) => e.code(),
            IsabelleError::Type(e) => e.code(),
            IsabelleError::Proof(e) => e.code(),
            IsabelleError::Parse(e) => e.code(),
            IsabelleError::Io(_) => "E0400",
            IsabelleError::Config(_) => "E0401",
        }
    }

    /// Return a help message if available.
    pub fn help(&self) -> Option<&'static str> {
        match self {
            IsabelleError::Kernel(e) => e.help(),
            IsabelleError::Type(e) => e.help(),
            IsabelleError::Proof(e) => e.help(),
            IsabelleError::Parse(e) => e.help(),
            IsabelleError::Io(_) => Some("check file permissions and path"),
            IsabelleError::Config(_) => Some("check your theory configuration"),
        }
    }
}

// ============================================================================
// Kernel errors (E0001-E0099)
// ============================================================================

/// Kernel errors — invariant violations in the trusted core.
#[derive(Error, Debug)]
pub enum KernelError {
    /// E0001: Not an equality where one was expected.
    #[error(
        "E0001: expected an equality `t ≡ u`\n  \
         found: `{0:?}`\n  \
         = help: use `Pure::dest_equals` or `Pure::dest_equals_with_type` to check first"
    )]
    NotEquality(crate::core::term::Term),

    /// E0002: Not an implication where one was expected.
    #[error(
        "E0002: expected an implication `A ==> B`\n  \
         found: `{0:?}`\n  \
         = help: use `Pure::dest_implies` to extract premise and conclusion"
    )]
    NotImplication(crate::core::term::Term),

    /// E0003: Undeclared constant.
    #[error(
        "E0003: undeclared constant `{0}`\n  \
         = help: declare the constant with `consts` or `axiomatization` before use"
    )]
    UndeclaredConstant(String),

    /// E0004: Type mismatch.
    #[error(
        "E0004: type mismatch\n  \
         expected: `{expected:?}`\n  \
         found:    `{actual:?}`\n  \
         = help: check the term construction or use `CTerm::certify_typed`"
    )]
    TypeMismatch { expected: crate::core::types::Typ, actual: crate::core::types::Typ },

    /// E0005: Occurs check failed — infinite type.
    #[error(
        "E0005: occurs check failed\n  \
         variable `{var}` occurs in `{term:?}`\n  \
         = help: this would create an infinite type; check your unification constraints"
    )]
    OccursCheck { var: String, term: crate::core::term::Term },

    /// E0006: Hypothesis not found in assumptions.
    #[error(
        "E0006: hypothesis not found in assumptions\n  \
         = help: the proposition you're trying to use as an assumption is not in the hypothesis list"
    )]
    HypothesisNotFound,

    /// E0007: Middle terms not alpha-equivalent in transitive.
    #[error(
        "E0007: middle terms are not alpha-equivalent\n  \
         in `transitive`: `t ≡ u` and `u ≡ v` must share the SAME `u`\n  \
         = help: check that the middle term is exactly identical, including bound variable names"
    )]
    MidTermsNotEquiv,

    /// E0008: Antecedent does not match in implies_elim.
    #[error(
        "E0008: antecedent mismatch in `==>` elimination\n  \
         = help: the major premise's antecedent must match the minor premise's proposition"
    )]
    AntecedentMismatch,

    /// E0009: Not a forall proposition.
    #[error(
        "E0009: expected a forall proposition `!!x. P x`\n  \
         found: `{0:?}`\n  \
         = help: use `Pure::dest_all` to check the term structure first"
    )]
    NotForall(crate::core::term::Term),

    /// E0010: Free variable in hypotheses during forall_intr.
    #[error(
        "E0010: free variable `{name}` appears in hypotheses\n  \
         = help: rename the bound variable or remove the hypothesis containing `{name}`"
    )]
    FreeVarInHypotheses { name: String },

    /// E0011: Beta conversion applied to non-redex.
    #[error(
        "E0011: beta conversion failed for `{0}`\n  \
         = help: the term is not a beta-redex `(λx. t) u`"
    )]
    BetaConversion(String),

    /// E0012: Not a function type.
    #[error(
        "E0012: not a function type\n  \
         found: `{0:?}`\n  \
         = help: `combination` requires a function type `A => B` for the first argument"
    )]
    NotFunctionType(crate::core::types::Typ),

    /// E0013: Dummy type found where proper type required.
    #[error(
        "E0013: dummy type in operation `{op}`\n  \
         = help: use `CTerm::term_type()` or `Pure::dest_equals_with_type()` to get the actual type\n  \
         = note: `Typ::dummy()` is forbidden in kernel inference rules"
    )]
    DummyType { op: &'static str },
}

impl KernelError {
    pub fn code(&self) -> &'static str {
        match self {
            KernelError::NotEquality(_) => "E0001",
            KernelError::NotImplication(_) => "E0002",
            KernelError::UndeclaredConstant(_) => "E0003",
            KernelError::TypeMismatch { .. } => "E0004",
            KernelError::OccursCheck { .. } => "E0005",
            KernelError::HypothesisNotFound => "E0006",
            KernelError::MidTermsNotEquiv => "E0007",
            KernelError::AntecedentMismatch => "E0008",
            KernelError::NotForall(_) => "E0009",
            KernelError::FreeVarInHypotheses { .. } => "E0010",
            KernelError::BetaConversion(_) => "E0011",
            KernelError::NotFunctionType(_) => "E0012",
            KernelError::DummyType { .. } => "E0013",
        }
    }

    pub fn help(&self) -> Option<&'static str> {
        match self {
            KernelError::TypeMismatch { .. } => {
                Some("ensure the types of your terms match before combining them")
            },
            KernelError::HypothesisNotFound => {
                Some("use `assume` to add the proposition to the context first")
            },
            _ => None,
        }
    }
}

// ============================================================================
// Type errors (E0100-E0199)
// ============================================================================

/// Type system errors.
#[derive(Error, Debug)]
pub enum TypeError {
    /// E0100: Type not declared.
    #[error(
        "E0100: type `{0}` not declared\n  \
         = help: declare the type with `typedecl {0}` or import a theory that declares it"
    )]
    UndeclaredType(String),

    /// E0101: Type arity mismatch.
    #[error(
        "E0101: arity mismatch for type constructor `{name}`\n  \
         expected {expected} type argument(s), got {actual}\n  \
         = help: check that you're applying the correct number of type arguments"
    )]
    ArityMismatch { name: String, expected: usize, actual: usize },

    /// E0102: Sort mismatch.
    #[error(
        "E0102: sort constraint not satisfied\n  \
         required: `{0:?}`\n  \
         = help: add the necessary type class constraint or use a more general type"
    )]
    SortMismatch(crate::core::types::Sort),
}

impl TypeError {
    pub fn code(&self) -> &'static str {
        match self {
            TypeError::UndeclaredType(_) => "E0100",
            TypeError::ArityMismatch { .. } => "E0101",
            TypeError::SortMismatch(_) => "E0102",
        }
    }

    pub fn help(&self) -> Option<&'static str> {
        match self {
            TypeError::UndeclaredType(_) => {
                Some("type declarations are typically found in theory header or HOL.thy")
            },
            TypeError::ArityMismatch { .. } => {
                Some("check the type constructor's declaration for its expected arity")
            },
            _ => None,
        }
    }
}

// ============================================================================
// Proof errors (E0200-E0299)
// ============================================================================

/// Proof errors.
#[derive(Error, Debug)]
pub enum ProofError {
    /// E0200: No unifier found.
    #[error(
        "E0200: no unifier found\n  \
         = help: the goal pattern doesn't match any known rule; try a different proof method"
    )]
    NoUnifier,

    /// E0201: Search bound exceeded.
    #[error(
        "E0201: search bound exceeded (depth = {0})\n  \
         = help: increase the bound or break the goal into smaller subgoals"
    )]
    SearchBound(usize),

    /// E0202: Tactic failed.
    #[error(
        "E0202: tactic failed\n  \
         = help: try a different tactic (auto, blast, simp, rule, induct, cases)"
    )]
    TacticFailed,

    /// E0203: Method not found.
    #[error(
        "E0203: proof method `{0}` not found\n  \
         = help: available methods: auto, blast, fast, best, safe, simp, \
         induct, cases, rule, erule, drule, frule, metis, meson, arith, \
         iprover, subst, unfold, fold, assumption, coinduct, coinduction, \
         try, try0, skip, fail"
    )]
    MethodNotFound(String),
}

impl ProofError {
    pub fn code(&self) -> &'static str {
        match self {
            ProofError::NoUnifier => "E0200",
            ProofError::SearchBound(_) => "E0201",
            ProofError::TacticFailed => "E0202",
            ProofError::MethodNotFound(_) => "E0203",
        }
    }

    pub fn help(&self) -> Option<&'static str> {
        match self {
            ProofError::NoUnifier => {
                Some("check that the theorem's conclusion matches the goal pattern")
            },
            ProofError::SearchBound(_) => {
                Some("consider using `auto` which has adaptive depth limits")
            },
            ProofError::MethodNotFound(_) => {
                Some("use `try` or `try0` to automatically find a working method")
            },
            _ => None,
        }
    }
}

// ============================================================================
// Parse errors (E0300-E0399)
// ============================================================================

/// Parse errors with source location.
#[derive(Error, Debug)]
#[error(
    "E0300: parse error at line {line}, column {col}\n  \
     {msg}\n  \
     = help: check syntax; expected a well-formed Isabelle term or command"
)]
pub struct ParseError {
    pub msg: String,
    pub line: usize,
    pub col: usize,
}

impl ParseError {
    pub fn code(&self) -> &'static str {
        "E0300"
    }
    pub fn help(&self) -> Option<&'static str> {
        None
    }
}

// ============================================================================
// Convenience Result type
// ============================================================================

/// Convenience Result type for Isabelle-rs.
pub type Result<T> = std::result::Result<T, IsabelleError>;
