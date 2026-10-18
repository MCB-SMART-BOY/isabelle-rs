//! Document model — the workspace for theory files.
//!
//! Manages open files, command parsing, and snapshot-based
//! incremental checking state.

mod model;

pub use model::{Command, CommandKind, Document, Node, Snapshot, UpdateResult};
