//! Native reminders for the configured editor hooks; no proof or commit authority.
use std::env;
use std::io::{self, Write};
use std::path::Path;
use std::process::{Command, Stdio};

use crate::runner::{StepError, io_error};

const SOURCE_CHANGE_THRESHOLD: usize = 10;
const EDITED_PATH_VARIABLE: &str = "CLAUDE_TOOL_FILE_PATH";

pub enum HookEvent {
    PreEdit,
    PostEdit,
}

impl HookEvent {
    pub fn parse(args: &[String]) -> Result<Self, StepError> {
        match args {
            [event] if event == "pre-edit" => Ok(Self::PreEdit),
            [event] if event == "post-edit" => Ok(Self::PostEdit),
            _ => Err(StepError::Input("hook requires exactly pre-edit or post-edit".into())),
        }
    }
}

fn read_edited_path() -> Result<String, StepError> {
    match env::var(EDITED_PATH_VARIABLE) {
        Ok(path) => Ok(path),
        Err(env::VarError::NotPresent) => Ok(String::new()),
        Err(error) => Err(StepError::Input(format!("read {EDITED_PATH_VARIABLE}: {error}"))),
    }
}

fn count_changed_sources(directory: &Path) -> Result<usize, StepError> {
    let operation = format!("count changed src files in {}", directory.display());
    let output = Command::new("git")
        .current_dir(directory)
        .args(["diff", "--name-only", "-z", "HEAD", "--", "src/"])
        .stderr(Stdio::inherit())
        .output()
        .map_err(|source| io_error(&operation, source))?;
    if !output.status.success() {
        return Err(StepError::Exit { operation, status: output.status });
    }
    Ok(output.stdout.iter().filter(|&&byte| byte == 0).count())
}

fn report_changed_sources(directory: &Path) -> Result<(), StepError> {
    let count = count_changed_sources(directory)?;
    if count <= SOURCE_CHANGE_THRESHOLD {
        return Ok(());
    }
    writeln!(
        io::stdout().lock(),
        "[doc-sync] {count} src files changed. Docs may be stale. Use /sync-docs to update docs/ and .claude/"
    )
    .map_err(|source| io_error("write documentation sync reminder", source))
}

pub fn run(event: HookEvent, directory: &Path) -> Result<(), StepError> {
    let path = read_edited_path()?;
    match event {
        HookEvent::PreEdit => writeln!(io::stdout().lock(), "Editing file: {path}")
            .map_err(|source| io_error("write edited path reminder", source)),
        HookEvent::PostEdit if path.starts_with("src/") => report_changed_sources(directory),
        HookEvent::PostEdit => Ok(()),
    }
}
