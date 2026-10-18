use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

use super::super::{artifacts, common, prepare};
use crate::runner::{StepError, io_error};
use prepare::{SETTINGS, failure};

pub(super) fn require_prepared(
    repository: &Path,
    workspace: &Path,
) -> Result<(Value, String, String), StepError> {
    let path = workspace.join("prepared.json");
    let report = common::read_json(&path)?;
    for key in
        ["source_root", "git_commit", "archive_sha256", "git_archive_sha256", "settings_sha256"]
    {
        if !report[key].is_string() {
            return Err(failure("parse preparation manifest", &path, "invalid fields"));
        }
    }
    for key in ["schema", "archive_members"] {
        if !report[key].is_number() {
            return Err(failure("parse preparation manifest", &path, "invalid fields"));
        }
    }
    if !report["source_files"].is_array() || !report["components"].is_array() {
        return Err(failure("parse preparation manifest", &path, "invalid fields"));
    }
    let source = Path::new(
        report["source_root"]
            .as_str()
            .ok_or_else(|| failure("parse preparation manifest", &path, "source path missing"))?,
    );
    prepare::require_clean_source(source, repository)?;
    prepare::archive_git_source(source, workspace)?;
    if report["schema"] != 1 || report["git_commit"] != common::COMMIT {
        return Err(failure("verify preparation", &path, "wrong schema or source revision"));
    }
    prepare::verify_cached_archive(workspace, &report)?;
    prepare::verify_cached_source(workspace, source, &report)?;
    let components =
        prepare::read_components(&workspace.join("fixed-source"), &workspace.join("distribution"))?;
    if !report["components"].as_array().is_some_and(|values| {
        values.len() == components.len()
            && values
                .iter()
                .zip(&components)
                .all(|(actual, expected)| actual.as_str() == Some(expected.as_str()))
    }) {
        return Err(failure("verify components", workspace, "component inventory differs"));
    }
    let component_text = prepare::verify_configuration(workspace, &components)?;
    prepare::check_legacy_configuration(workspace, &component_text)?;
    if report["settings_sha256"] != common::digest_bytes(SETTINGS.as_bytes()) {
        return Err(failure("verify startup settings", workspace, "settings digest changed"));
    }
    Ok((report, common::digest_file(&path)?, component_text))
}

const REQUIRED_BUILD_LINES: [&str; 6] = [
    "Building Pure ...",
    "Finished Pure (",
    "Building HOL ...",
    "HOL: theory Tools.Code_Generator",
    "HOL: theory HOL.HOL",
    "Finished HOL (",
];

pub(super) fn require_rebuilt_sessions(run: &Path) -> Result<(), StepError> {
    let output = String::from_utf8_lossy(
        &fs::read(run.join("stdout.log"))
            .map_err(|e| io_error(format!("read build stdout {}", run.display()), e))?,
    )
    .into_owned();
    if !REQUIRED_BUILD_LINES.iter().all(|line| output.contains(line)) {
        return Err(failure("verify fresh HOL rebuild", run, "missing session lifecycle"));
    }
    let heaps = run.join("home/.isabelle/p0-reference/heaps");
    for session in ["Pure", "HOL"] {
        let mut matches = Vec::new();
        for entry in fs::read_dir(&heaps)
            .map_err(|e| io_error(format!("read heaps {}", heaps.display()), e))?
        {
            let entry = entry.map_err(|e| io_error("list heap platform", e))?;
            let path = entry.path().join(session);
            if path.exists() {
                common::require_regular(&path)?;
                matches.push(path);
            }
        }
        if matches.len() != 1
            || fs::metadata(&matches[0]).map_err(|e| io_error("stat heap", e))?.len() == 0
        {
            return Err(failure("verify fresh HOL heaps", &heaps, "Pure/HOL heaps missing"));
        }
    }
    Ok(())
}

pub(super) fn require_build_run(
    build_run: &Path,
    workspace: &Path,
    prepared_sha256: &str,
    component_text: &str,
) -> Result<(), StepError> {
    if !build_run.is_absolute() || build_run.parent() != Some(workspace.join("runs").as_path()) {
        return Err(failure("select inventory build", build_run, "explicit run path required"));
    }
    artifacts::require_managed_directory(build_run, workspace)?;
    let result = common::read_json(&build_run.join("result.json"))?;
    let command = common::read_json(&build_run.join("command.json"))?;
    if !result["trace"].is_object() {
        return Err(failure("parse build trace", build_run, "missing trace summary"));
    }
    if result["operation"] != "build"
        || result["exit_code"] != 0
        || !result["interruption"].is_null()
        || result["trace"]["complete"] != true
    {
        return Err(failure("select inventory build", build_run, "no successful build"));
    }
    if result["prepared_sha256"] != prepared_sha256
        || command["arguments"] != serde_json::json!(super::build_options())
    {
        return Err(failure("select inventory build", build_run, "build inputs or options differ"));
    }
    for (name, key) in [
        ("stdout.log", "stdout_sha256"),
        ("command.json", "command_sha256"),
        ("events.jsonl", "events_sha256"),
    ] {
        let path = build_run.join(name);
        if result[key] != common::digest_file(&path)? {
            return Err(failure(
                "verify recorded build artifact",
                &path,
                "artifact identity changed or absent; run a fresh reference build",
            ));
        }
    }
    require_rebuilt_sessions(build_run)?;
    artifacts::verify_build_inputs(build_run, &result, SETTINGS, component_text)
}

pub(super) fn require_tools() -> Result<(PathBuf, PathBuf), StepError> {
    if !cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        return Err(StepError::Input("reference runtime requires Linux x86_64".into()));
    }
    for path in [
        "/nix",
        "/run/current-system/sw/bin/bash",
        "/run/current-system/sw/bin/env",
        "/run/current-system/sw/share/nix-ld/lib/ld.so",
        "/run/current-system/sw/share/nix-ld/lib",
        "/lib64/ld-linux-x86-64.so.2",
    ] {
        if !Path::new(path).exists() {
            return Err(failure("check NixOS sandbox prerequisite", Path::new(path), "missing"));
        }
    }
    let bwrap = prepare::find_tool("bwrap").ok_or_else(|| {
        failure("check sandbox prerequisite", Path::new("bwrap"), "not installed")
    })?;
    let strace = prepare::find_tool("strace").ok_or_else(|| {
        failure("check observation prerequisite", Path::new("strace"), "not installed")
    })?;
    Ok((bwrap.canonicalize().map_err(|e| io_error("resolve bwrap", e))?, strace))
}

pub(super) fn make_run_directory(workspace: &Path, operation: &str) -> Result<PathBuf, StepError> {
    let runs = workspace.join("runs");
    prepare::ensure_directory(&runs)?;
    artifacts::require_managed_directory(&runs, workspace)?;
    let run = tempfile::Builder::new()
        .prefix(&format!("{operation}-"))
        .tempdir_in(&runs)
        .map_err(|e| io_error(format!("create {operation} run in {}", runs.display()), e))?;
    Ok(run.keep())
}

pub(super) fn make_build_home(run: &Path, component_text: &str) -> Result<(), StepError> {
    let config = run.join("home/.isabelle/p0-reference/etc");
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = fs::DirBuilder::new();
        builder.recursive(true).mode(0o700);
        builder
            .create(&config)
            .map_err(|e| io_error(format!("create build home {}", config.display()), e))?;
    }
    #[cfg(not(unix))]
    fs::create_dir_all(&config)
        .map_err(|e| io_error(format!("create build home {}", config.display()), e))?;
    prepare::exclusive_text(&config.join("settings"), SETTINGS)?;
    prepare::exclusive_text(&config.join("components"), component_text)?;
    for name in ["tmp", "generated-classes", "generated-demo"] {
        prepare::ensure_directory(&run.join(name))?;
    }
    Ok(())
}
