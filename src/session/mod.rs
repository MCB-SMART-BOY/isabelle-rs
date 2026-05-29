//! Session management — per-file worker actors.
//!
//! ## Architecture (V3)
//!
//! ```text
//! Session
//!   ├── FileWorker (per .thy file)
//!   │   ├── Arena (isolated memory)
//!   │   ├── Document (snapshot-based)
//!   │   └── Toplevel (command loop)
//!   └── Watchdog (health monitoring)
//! ```
//!
//! Each file gets its own actor with an isolated Arena. This is the
//! key V3 improvement over V1's `Mutex<Document>` bottleneck.

pub mod file_worker;
pub mod session;
pub mod watchdog;

// Re-export document from existing location
pub use crate::document::document::Document;

pub use file_worker::FileWorker;
pub use session::Session;
pub use watchdog::Watchdog;
