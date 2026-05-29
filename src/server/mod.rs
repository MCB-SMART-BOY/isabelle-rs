//! Isabelle-rs LSP Server.
//!
//! Implements the Language Server Protocol for Isabelle theory files.
//!
//! ## Architecture
//!
//! ```text
//! Editor (VSCode/Emacs/Vim)
//!     │
//!     │ LSP (JSON-RPC over stdio/TCP)
//!     ▼
//! ┌─────────────────┐
//! │  Transport      │  -- JSON-RPC wire protocol
//! │  (transport.rs) │
//! └────────┬────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │  Handler        │  -- Request dispatch, lifecycle
//! │  (handler.rs)   │
//! └────────┬────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │  Flèche         │  -- Incremental document checking
//! │  (../fleche/)   │
//! └────────┬────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │  Isabelle Core  │  -- Trusted kernel (types, terms, thms)
//! │  (../core/)     │
//! └─────────────────┘
//! ```
//!
//! ## LSP Protocol Support
//!
//! | Feature | Status |
//! |---------|--------|
//! | `initialize` / `shutdown` | ✅ |
//! | `textDocument/didOpen` / `didChange` / `didClose` / `didSave` | ✅ |
//! | `textDocument/publishDiagnostics` | ✅ |
//! | `textDocument/hover` | ✅ |
//! | `textDocument/completion` | 🚧 |
//! | `textDocument/definition` | 🚧 |
//! | `textDocument/documentSymbol` | 🚧 |
//! | `isabelle/proofGoals` (extension) | ✅ |
//!
//! ## References
//!
//! - LSP 3.17: <https://microsoft.github.io/language-server-protocol/>
//! - Lean 4 Server: <https://github.com/leanprover/lean4/tree/master/src/Lean/Server>
//! - Coq-lsp: <https://github.com/ejgallego/coq-lsp>

pub mod handler;
pub mod isabelle_ext;
pub mod lsp_types;
pub mod transport;

pub use handler::IsabelleServer;
