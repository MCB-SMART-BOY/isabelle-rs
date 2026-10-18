//! Session management for `.thy` documents.
//!
//! A Session keeps independent document states behind a bounded, shared
//! compute queue. Built-in RealExecutor checks require a trusted worker path
//! passed to `Session::new_with_worker` and run in one reusable, killable child
//! process owned by the queue's worker thread. Custom CommandExecutor
//! implementations remain cooperative and in-process. Closing or reopening a
//! document invalidates responses from its previous lifetime.

mod actor;
pub mod file_worker;
pub mod watchdog;

// Re-export document from existing location
pub use actor::{Session, SessionError};
pub use file_worker::FileWorker;
pub use watchdog::Watchdog;

pub use crate::document::Document;
