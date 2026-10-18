//! Stable relative-path/byte Merkle identity for the exact loaded Pure heap tree.
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::super::compare;
use crate::runner::{StepError, io_error};

const MAX_HEAP_FILE_BYTES: u64 = 8 * 1024 * 1024 * 1024;
const HASH_BUFFER_BYTES: usize = 64 * 1024;

fn hash_heap_file(path: &Path) -> Result<(u64, sha2::digest::Output<Sha256>), StepError> {
    let mut file = compare::open_checked_file(path, MAX_HEAP_FILE_BYTES)?;
    let mut hash = Sha256::new();
    let mut size = 0u64;
    let mut buffer = [0u8; HASH_BUFFER_BYTES];
    loop {
        let count =
            file.read(&mut buffer).map_err(|source| io_error("read Pure heap bytes", source))?;
        if count == 0 {
            break;
        }
        size += count as u64;
        if size > MAX_HEAP_FILE_BYTES {
            return Err(StepError::Input("Pure heap file exceeds limit".into()));
        }
        hash.update(&buffer[..count]);
    }
    Ok((size, hash.finalize()))
}

const MAX_HEAP_ENTRIES: usize = 100_000;
fn copy_heap_file(source: &Path, destination: &Path) -> Result<(), StepError> {
    let mut input = compare::open_checked_file(source, MAX_HEAP_FILE_BYTES)?;
    let mut output =
        OpenOptions::new().write(true).create_new(true).open(destination).map_err(|cause| {
            io_error(format!("create isolated Pure heap {}", destination.display()), cause)
        })?;
    let length = std::io::copy(&mut input, &mut output).map_err(|cause| {
        io_error(format!("copy isolated Pure heap {}", source.display()), cause)
    })?;
    if length > MAX_HEAP_FILE_BYTES {
        return Err(StepError::Input("Pure heap exceeds approved file bound".into()));
    }
    output.flush().map_err(|cause| io_error("flush isolated Pure heap", cause))
}

fn pure_platform(build: &Path) -> Result<PathBuf, StepError> {
    let original = build.join("home/.isabelle/p0-reference/heaps");
    let mut platforms =
        fs::read_dir(&original).map_err(|cause| io_error("inspect built Pure heap", cause))?;
    let platform = platforms
        .next()
        .ok_or_else(|| StepError::Input("missing built Pure heap platform".into()))?
        .map_err(|cause| io_error("read Pure heap platform", cause))?;
    if platforms.next().is_some()
        || !platform
            .file_type()
            .map_err(|cause| io_error("inspect Pure heap platform", cause))?
            .is_dir()
    {
        return Err(StepError::Input("ambiguous or invalid Pure heap platform".into()));
    }
    Ok(platform.path())
}

pub fn pure_heap_sha256(build: &Path) -> Result<String, StepError> {
    let source = pure_platform(build)?;
    let (heap_size, heap) = hash_heap_file(&source.join("Pure"))?;
    let (db_size, db) = hash_heap_file(&source.join("log/Pure.db"))?;
    let platform = source
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| StepError::Input("non-UTF8 Pure platform".into()))?;
    let mut tree = Sha256::new();
    for (name, size, hash) in [
        (format!("{platform}/Pure"), heap_size, heap),
        (format!("{platform}/log/Pure.db"), db_size, db),
    ] {
        tree.update((name.len() as u64).to_be_bytes());
        tree.update(name.as_bytes());
        tree.update(size.to_be_bytes());
        tree.update(hash);
    }
    Ok(format!("{:x}", tree.finalize()))
}

pub fn stage_pure_heap(build: &Path, inventory: &Path) -> Result<String, StepError> {
    let source = pure_platform(build)?;
    let target = inventory.join("pure-heap");
    let target_platform = target.join(
        source.file_name().ok_or_else(|| StepError::Input("Pure platform name absent".into()))?,
    );
    fs::create_dir_all(target_platform.join("log"))
        .map_err(|cause| io_error("create isolated Pure heap directories", cause))?;
    copy_heap_file(&source.join("Pure"), &target_platform.join("Pure"))?;
    copy_heap_file(&source.join("log/Pure.db"), &target_platform.join("log/Pure.db"))?;
    let expected = pure_heap_sha256(build)?;
    let actual = heap_tree_sha256(&target)?;
    if expected != actual {
        return Err(StepError::Input("isolated Pure heap differs from built bytes".into()));
    }
    Ok(actual)
}

fn walk_tree(root: &Path, directory: &Path, files: &mut Vec<PathBuf>) -> Result<(), StepError> {
    for entry in
        fs::read_dir(directory).map_err(|source| io_error("enumerate Pure heap", source))?
    {
        let entry = entry.map_err(|source| io_error("read Pure heap entry", source))?;
        let path = entry.path();
        let kind = entry.file_type().map_err(|source| io_error("stat Pure heap entry", source))?;
        if kind.is_dir() {
            walk_tree(root, &path, files)?;
        } else if kind.is_file() {
            files.push(path);
        } else {
            return Err(StepError::Input(format!(
                "Pure heap has unsupported link or device: {}",
                path.display()
            )));
        }
        if files.len() > MAX_HEAP_ENTRIES {
            return Err(StepError::Input(format!(
                "Pure heap exceeds tree entry limit: {}",
                root.display()
            )));
        }
    }
    Ok(())
}

pub fn heap_tree_sha256(root: &Path) -> Result<String, StepError> {
    let mut files = Vec::new();
    walk_tree(root, root, &mut files)?;
    files.sort();
    let mut tree = Sha256::new();
    for file in files {
        let relative = file
            .strip_prefix(root)
            .map_err(|_| StepError::Input("heap path escapes root".into()))?;
        let name =
            relative.to_str().ok_or_else(|| StepError::Input("non-UTF8 Pure heap name".into()))?;
        let (size, leaf) = hash_heap_file(&file)?;
        tree.update((name.len() as u64).to_be_bytes());
        tree.update(name.as_bytes());
        tree.update(size.to_be_bytes());
        tree.update(leaf);
    }
    Ok(format!("{:x}", tree.finalize()))
}
