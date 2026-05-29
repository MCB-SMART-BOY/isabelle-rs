//! Isabelle-rs: A modern reimplementation of the Isabelle proof assistant in Rust.
//!
//! ## Library structure
//!
//! - `kernel` — Trusted LCF kernel (types, terms, theorems)
//! - `session` — Session actor + FileWorker + Watchdog
//! - `isar` — Isar structured proof language
//! - `lsp` — LSP server (tower-based handlers)
//! - `syntax` — Rowan CST-based incremental parser
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
