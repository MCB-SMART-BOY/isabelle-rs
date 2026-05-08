//! Watchdog — monitors FileWorker health.
//!
//! Inspired by Lean 4's Watchdog, this module:
//! - Pings workers periodically
//! - Detects crashed/hung workers
//! - Restarts workers from saved snapshots
//! - Reports worker status to the LSP client
//!
//! ## Design
//!
//! ```text
//! Watchdog
//!   ├── Heartbeat: ping every N ms
//!   ├── Crash detection: heartbeat timeout
//!   ├── Recovery: restart from last good snapshot
//!   └── Reporting: send diagnostics to client
//! ```

use std::time::{Duration, Instant};

// =========================================================================
// Worker status
// =========================================================================

/// The health status of a FileWorker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerStatus {
    /// Worker is alive and processing.
    Alive,
    /// Worker is idle (waiting for edits).
    Idle,
    /// Worker heartbeat timed out.
    Unresponsive,
    /// Worker has crashed.
    Crashed,
    /// Worker is restarting from snapshot.
    Restarting,
}

// =========================================================================
// Watchdog
// =========================================================================

/// Monitors the health of all FileWorkers in a session.
pub struct Watchdog {
    /// Heartbeat interval.
    interval: Duration,
    /// Last successful check time.
    _last_check: Instant,
}

impl Watchdog {
    /// Create a new watchdog with default heartbeat (1 second).
    pub fn new() -> Self {
        Watchdog {
            interval: Duration::from_secs(1),
            _last_check: Instant::now(),
        }
    }

    /// Create a watchdog with a custom heartbeat interval.
    pub fn with_interval(interval: Duration) -> Self {
        Watchdog {
            interval,
            _last_check: Instant::now(),
        }
    }

    /// Check a worker's status.
    ///
    /// Returns `Alive` if healthy, `Unresponsive` if heartbeat missed.
    pub fn check(&self, _last_heartbeat: Instant) -> WorkerStatus {
        // TODO: real heartbeat checking
        WorkerStatus::Alive
    }
}

impl Default for Watchdog {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_watchdog_creation() {
        let wd = Watchdog::new();
        assert_eq!(wd.check(Instant::now()), WorkerStatus::Alive);
    }
}
