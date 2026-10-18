mod heap;
pub use heap::{heap_tree_sha256, pure_heap_sha256, stage_pure_heap};
mod snapshot;
pub use snapshot::source_tree_sha256;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use rusqlite::{Connection, OpenFlags};
use serde_json::{Map, Value, json};

use super::common;
use super::prepare::{failure, read_text};
use crate::runner::{StepError, io_error};

pub const INPUT_MANIFEST: &str = "build-inputs.json";
const BUILD_INPUT_ROOTS: [&str; 3] = ["home", "generated-classes", "generated-demo"];
const SESSIONS: [&str; 2] = ["Pure", "HOL"];

#[cfg(unix)]
pub fn require_managed_directory(path: &Path, root: &Path) -> Result<(), StepError> {
    let relative = path
        .strip_prefix(root)
        .map_err(|_| failure("verify managed directory", path, "outside run root"))?;
    let mut current = root.to_path_buf();
    verify_owned_directory(&current)?;
    for part in relative.components() {
        current.push(part);
        verify_owned_directory(&current)?;
    }
    Ok(())
}

#[cfg(unix)]
fn verify_owned_directory(path: &Path) -> Result<(), StepError> {
    use std::os::unix::fs::MetadataExt;
    let metadata = fs::symlink_metadata(path)
        .map_err(|e| io_error(format!("inspect managed directory {}", path.display()), e))?;
    if !metadata.file_type().is_dir()
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.mode() & 0o022 != 0
    {
        return Err(failure(
            "verify managed directory",
            path,
            "owned directory without symlinks or shared write permission required",
        ));
    }
    Ok(())
}

#[cfg(not(unix))]
pub fn require_managed_directory(_path: &Path, _root: &Path) -> Result<(), StepError> {
    Err(StepError::Input("managed reference build inputs require Unix ownership".into()))
}

#[cfg(unix)]
fn record_input_path(
    run: &Path,
    parent: &Path,
    path: &Path,
    entries: &mut Vec<Value>,
) -> Result<(), StepError> {
    use std::os::unix::fs::MetadataExt;
    let metadata = fs::symlink_metadata(path)
        .map_err(|e| io_error(format!("inspect build input {}", path.display()), e))?;
    if metadata.file_type().is_symlink() {
        return Err(failure("record build input", path, "symlinks are not reusable inputs"));
    }
    if !metadata.file_type().is_file() && !metadata.file_type().is_dir() {
        return Err(failure("record build input", path, "unsupported file type"));
    }
    if metadata.uid() != unsafe { libc::geteuid() } || metadata.mode() & 0o022 != 0 {
        return Err(failure("record build input", path, "unowned or shared-writable input"));
    }
    if metadata.is_dir() && path != parent {
        return Ok(());
    }
    let relative = path
        .strip_prefix(run)
        .map_err(|_| failure("record build input", path, "outside run root"))?;
    let mut entry = json!({"path":relative.to_string_lossy(),"mode":metadata.mode() & 0o7777,"kind":if metadata.is_file() {"file"} else {"directory"}});
    if metadata.is_file() {
        entry["sha256"] = Value::String(common::digest_file(path)?);
    }
    entries.push(entry);
    Ok(())
}

#[cfg(unix)]
fn collect_input_tree(
    run: &Path,
    directory: &Path,
    entries: &mut Vec<Value>,
) -> Result<(), StepError> {
    require_managed_directory(directory, run)?;
    let mut stack = vec![directory.to_path_buf()];
    while let Some(parent) = stack.pop() {
        let mut children = fs::read_dir(&parent)
            .map_err(|e| io_error(format!("enumerate build inputs {}", parent.display()), e))?
            .map(|entry| {
                entry.map_err(|e| {
                    io_error(format!("enumerate build inputs {}", parent.display()), e)
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        children.sort_by_key(fs::DirEntry::file_name);
        let mut paths = vec![parent.clone()];
        paths.extend(children.iter().map(fs::DirEntry::path));
        for path in paths {
            record_input_path(run, &parent, &path, entries)?;
        }
        for child in children.into_iter().rev() {
            if child
                .file_type()
                .map_err(|e| {
                    io_error(format!("inspect build input {}", child.path().display()), e)
                })?
                .is_dir()
            {
                stack.push(child.path());
            }
        }
    }
    Ok(())
}

#[cfg(not(unix))]
fn collect_input_tree(
    _run: &Path,
    _directory: &Path,
    _entries: &mut Vec<Value>,
) -> Result<(), StepError> {
    Err(StepError::Input("reference build input collection requires Unix".into()))
}

pub fn collect_build_inputs(run: &Path) -> Result<Value, StepError> {
    let mut entries = Vec::new();
    for name in BUILD_INPUT_ROOTS {
        collect_input_tree(run, &run.join(name), &mut entries)?;
    }
    entries.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    Ok(json!({"schema_version":1,"entries":entries}))
}

pub fn verify_build_inputs(
    run: &Path,
    result: &Value,
    settings: &str,
    components: &str,
) -> Result<(), StepError> {
    let config = run.join("home/.isabelle/p0-reference/etc");
    require_managed_directory(&config, run)?;
    let actual = fs::read_dir(&config)
        .map_err(|e| io_error(format!("enumerate build startup inputs {}", config.display()), e))?
        .map(|entry| {
            entry.map(|e| e.file_name()).map_err(|e| io_error("enumerate startup config", e))
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    let expected = BTreeSet::from(["settings".into(), "components".into()]);
    if actual != expected {
        return Err(failure(
            "verify build startup inputs",
            &config,
            "unexpected configuration files",
        ));
    }
    for (name, content) in [("settings", settings), ("components", components)] {
        let path = config.join(name);
        if read_text(&path)? != content {
            return Err(failure("verify build startup input", &path, "contents changed"));
        }
    }
    let manifest = run.join(INPUT_MANIFEST);
    if result["build_inputs_sha256"] != common::digest_file(&manifest)? {
        return Err(failure(
            "verify build input manifest",
            &manifest,
            "identity changed or absent",
        ));
    }
    if common::read_json(&manifest)? != collect_build_inputs(run)? {
        return Err(failure("verify reusable build inputs", run, "input tree changed since build"));
    }
    Ok(())
}

fn find_session_database(run: &Path, session: &str) -> Result<PathBuf, StepError> {
    let heaps = run.join("home/.isabelle/p0-reference/heaps");
    require_managed_directory(&heaps, run)?;
    let mut databases = Vec::new();
    for entry in fs::read_dir(&heaps)
        .map_err(|e| io_error(format!("enumerate heaps {}", heaps.display()), e))?
    {
        let entry = entry.map_err(|e| io_error("enumerate heap platform", e))?;
        let platform = entry.path();
        require_managed_directory(&platform, run)?;
        let candidate = platform.join("log").join(format!("{session}.db"));
        if fs::symlink_metadata(&candidate).is_ok() {
            require_managed_directory(&platform.join("log"), run)?;
            common::require_regular(&candidate)?;
            databases.push(candidate);
        }
    }
    if databases.len() != 1 {
        return Err(failure(
            "find built session database",
            Path::new(session),
            "expected exactly one database",
        ));
    }
    Ok(databases.remove(0))
}

fn open_immutable_database(database: &Path) -> Result<Connection, StepError> {
    // Immutable mode prevents SQLite from creating journals or mutating evidence during reuse.
    let uri = format!(
        "file:{}?mode=ro&immutable=1",
        database.to_string_lossy().replace('%', "%25").replace('?', "%3F").replace('#', "%23")
    );
    Connection::open_with_flags(uri, OpenFlags::SQLITE_OPEN_READ_ONLY | OpenFlags::SQLITE_OPEN_URI)
        .map_err(|e| {
            io_error(
                format!("read built source mapping {}", database.display()),
                std::io::Error::other(e),
            )
        })
}

fn read_session_sources(
    database: &Path,
    session: &str,
) -> Result<BTreeMap<String, Value>, StepError> {
    let connection = open_immutable_database(database)?;
    let mut query = connection.prepare("SELECT session_name, theory_name, compressed, body FROM isabelle_exports WHERE name = ?1")
        .map_err(|e| io_error(format!("prepare source mapping {}", database.display()), std::io::Error::other(e)))?;
    let rows = query
        .query_map(["PIDE/files"], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, Vec<u8>>(3)?,
            ))
        })
        .map_err(|e| {
            io_error(
                format!("query built source mapping {}", database.display()),
                std::io::Error::other(e),
            )
        })?;
    let mut mapping = BTreeMap::new();
    for row in rows {
        let (actual, theory, compressed, body) = row.map_err(|e| {
            io_error(
                format!("decode built source mapping {}", database.display()),
                std::io::Error::other(e),
            )
        })?;
        if actual != session || compressed != 0 {
            return Err(failure(
                "decode built source mapping",
                database,
                "unexpected export encoding",
            ));
        }
        let text = String::from_utf8(body).map_err(|source| StepError::Utf8 {
            operation: format!("decode PIDE/files for {theory} in {}", database.display()),
            source,
        })?;
        let files = text.lines().collect::<Vec<_>>();
        if files.is_empty() || mapping.contains_key(&theory) {
            return Err(failure(
                "decode built source mapping",
                Path::new(&theory),
                "empty or duplicate mapping",
            ));
        }
        mapping.insert(theory, json!({"session":session,"source":files[0],"files":files}));
    }
    Ok(mapping)
}

pub fn read_build_source_map(run: &Path) -> Result<Value, StepError> {
    let mut mapping = Map::new();
    for session in SESSIONS {
        for (theory, entry) in read_session_sources(&find_session_database(run, session)?, session)?
        {
            if mapping.insert(theory, entry).is_some() {
                return Err(failure(
                    "merge built source mappings",
                    Path::new(session),
                    "duplicate theory identity",
                ));
            }
        }
    }
    Ok(Value::Object(mapping))
}
