//! Isabelle/Isar — the structured proof language.
//!
//! Corresponds to `src/Pure/Isar/` in the Isabelle distribution.
//!
//! ## Architecture
//!
//! ```text
//! isar/
//! ├── token.rs       — Lexer
//! ├── parse.rs       — Parser combinators
//! ├── proof.rs       — Proof state machine
//! ├── method.rs      — Proof method system
//! ├── proof_context.rs — Isar proof context
//! ├── toplevel.rs    — Toplevel command loop
//! └── term_parser.rs — Term/type parser + pretty printer
//! ```

pub mod args;
pub mod attrib;
pub mod keyword;
pub mod linarith;
pub mod method;
pub mod outer_syntax;
pub mod parse;
pub mod proof;
pub mod proof_context;
pub mod proof_state;
pub mod rule_cases;
pub mod spec;
pub mod term_parser;
pub mod token;
pub mod toplevel;

#[cfg(test)]
mod diag;

#[cfg(test)]
mod debug_tests;

#[cfg(test)]
mod hol_diag;
