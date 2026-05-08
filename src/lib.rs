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
//! - `theory` — Session management + cache
//! - `hol` — Higher-Order Logic loader
//! - `tools` — Proof automation

pub mod core;
pub mod kernel;
pub mod session;
pub mod isar;
pub mod lsp;
pub mod server;
pub mod document;
pub mod fleche;
pub mod syntax;
pub mod tools;
pub mod theory;
pub mod hol;
pub mod wasm;
