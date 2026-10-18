//! Sanitized streaming strace capture; unsupported platforms fail explicitly.
#[cfg(target_os = "linux")]
mod unix;
#[cfg(target_os = "linux")]
pub use unix::{SYSCALLS, TraceCapture};

#[cfg(not(target_os = "linux"))]
mod unsupported {
    use crate::runner::StepError;
    use serde_json::Value;
    use std::ffi::OsString;
    use std::path::Path;

    pub const SYSCALLS: [&str; 4] = ["execve", "execveat", "open", "openat"];

    /// An unavailable observation channel outside Linux.
    pub struct TraceCapture;

    impl TraceCapture {
        pub fn new(_event_path: &Path) -> Result<Self, StepError> {
            Err(StepError::Input("reference strace observation requires Linux procfs".into()))
        }
        pub fn executable(&self) -> Result<&Path, StepError> {
            Err(StepError::Input("reference strace observation requires Linux procfs".into()))
        }
        pub fn wrap(&self, _command: &[OsString]) -> Result<Vec<OsString>, StepError> {
            Err(StepError::Input("reference strace observation requires Linux procfs".into()))
        }
        pub fn close_parent_writer(&mut self) -> Result<(), StepError> {
            Err(StepError::Input("reference strace observation requires Linux procfs".into()))
        }
        pub fn finish(self) -> Result<Value, StepError> {
            Err(StepError::Input("reference strace observation requires Linux procfs".into()))
        }
    }
}

#[cfg(not(target_os = "linux"))]
pub use unsupported::{SYSCALLS, TraceCapture};
