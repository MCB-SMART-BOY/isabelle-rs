//! Isabelle-rs: A modern reimplementation of the Isabelle proof assistant in Rust.
//!
//! ## Library structure
//!
//! - `core` — Trusted LCF kernel (types, terms, theorems, unification, tactics)
//! - `isar` — Isar proof engine (methods, state machine, term parser)
//! - `hol` — HOL object logic (theory loading, BNF, Ctr_Sugar, Transfer)
//! - `theory` — Theory processing pipeline (loader, session builder, thy_header)
//! - `tools` — Proof automation (simp, metis, sledgehammer, tptp, reconstruct)
//! - `server` / `lsp` — LSP server (transport + 8 handlers)
//! - `session` — Session actor + FileWorker + Watchdog
//! - `syntax` — Rowan CST-based incremental parser + Pretty Printer
//! - `wasm` — WASM plugin system

// Allow dead code and unused variables/imports for API surface not yet integrated
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(unreachable_patterns)]
#![allow(unused_comparisons)]

pub mod core;
pub mod document;
pub mod fleche;
pub mod hol;
pub mod isar;
pub mod lsp;
pub mod server;
pub mod session;
pub mod syntax;
pub mod theory;
pub mod tools;
pub mod wasm;
