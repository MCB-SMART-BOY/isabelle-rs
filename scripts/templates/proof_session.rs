// Classification: design-only standalone template; not production code.
#![allow(dead_code)]

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SnapshotId(pub u64);

#[derive(Clone, Debug)]
pub struct CommandSpan(pub String);

#[derive(Clone, Debug)]
pub struct StateDiff;

#[derive(Clone, Debug)]
pub struct GoalView;

#[derive(Clone, Debug)]
pub struct Diagnostic;

#[derive(Clone, Debug)]
pub struct SessionError;

pub type Result<T> = std::result::Result<T, SessionError>;

/// Design template for the future session-layer boundary.
pub trait ProofSession {
    fn snapshot(&self) -> SnapshotId;
    fn apply_command(&mut self, span: CommandSpan) -> Result<StateDiff>;
    fn rollback(&mut self, snapshot: SnapshotId);
    fn goals(&self) -> Vec<GoalView>;
    fn diagnostics(&self) -> Vec<Diagnostic>;
}
