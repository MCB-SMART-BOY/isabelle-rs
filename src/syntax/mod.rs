//! Syntax system — Rowan CST-based incremental parsing.
//!
//! ## Architecture (V3)
//!
//! ```text
//! syntax/
//! ├── parser.rs         — Earley/Pratt parser (incremental)
//! ├── ast.rs            — Abstract syntax tree types
//! └── syntax_phases.rs  — Syntax phase pipeline (parse → AST → term)
//! ```
//!
//! ## Design
//!
//! Isabelle's syntax is extensible: users can declare new notation.
//! The V3 syntax system uses Rowan (lossless concrete syntax tree)
//! for incremental re-parsing on every keystroke.
//!
//! ## Current Status
//!
//! Stub — the existing Isar tokenizer/parser in `isar/` serves as
//! the current implementation. This module will hold the rowan-based
//! incremental parser when integrated.

pub mod parser;
pub mod ast;
pub mod syntax_phases;
