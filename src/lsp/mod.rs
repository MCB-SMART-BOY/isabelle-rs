//! LSP server — Language Server Protocol implementation.
//!
//! ## Architecture (V3 — tower Service stack)
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
//! │  Router         │  -- tower Service routing layer
//! │  (router.rs)    │
//! └────────┬────────┘
//!          │
//!     ┌────┴────┬─────────┬──────────┐
//!     ▼         ▼         ▼          ▼
//!  Hover    Completion  Definition  ProofGoals
//!  Service  Service     Service     Service
//!          │
//!          ▼
//! ┌─────────────────┐
//! │  Session        │  -- file workers + watchdog
//! │  (../session/)  │
//! └────────┬────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │  Isabelle Core  │  -- Trusted kernel
//! │  (../kernel/)   │
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
//! | `textDocument/semanticTokens` | ❌ |
//! | `$/isabelle/proofStateChanged` | 🚧 |
//! | `$/isabelle/commandProgress` | 🚧 |
//! | `isabelle/proofStep` / `isabelle/proofUndo` | ❌ |
//! | `isabelle/waitForChecking` | ❌ |

// Re-export from the existing server/ module
pub use crate::server::*;

// V3 modules
pub mod handlers;
pub mod router;
