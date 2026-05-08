//! Flèche — language-agnostic incremental document checking.
//!
//! Named after Coq-lsp's Flèche engine, this module provides:
//! - Incremental re-checking on document edits
//! - Snapshot-based caching
//! - Async diagnostic reporting
//! - Pluggable command executors

pub mod engine;

pub use engine::Fleche;
