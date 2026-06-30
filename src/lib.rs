//! Isabelle-rs: a Rust research prototype of an Isabelle/Pure-inspired LCF kernel.
//!
//! ## Library structure
//!
//! - `kernel` — New strict kernel nucleus; no compatibility certification or dummy types
//! - `core` — Legacy LCF kernel path under migration (types, terms, theorems, tactics)
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
pub mod kernel;
pub mod lsp;
pub mod server;
pub mod session;
pub mod syntax;
pub mod theory;
pub mod tools;
pub mod wasm;
