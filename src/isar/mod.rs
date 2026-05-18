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

pub mod token;
pub mod parse;
pub mod proof;
pub mod method;
pub mod proof_state;
pub mod proof_context;
pub mod toplevel;
pub mod term_parser;
