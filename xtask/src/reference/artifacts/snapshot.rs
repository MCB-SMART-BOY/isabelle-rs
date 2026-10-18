//! Source snapshot Merkle identity includes all files and symlink targets, not only loaded ML.
use std::fs;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::super::compare;
use crate::runner::{StepError, io_error};

const MAX_ENTRIES: usize = 200_000;
const MAX_FILE_BYTES: u64 = 8 * 1024 * 1024 * 1024;

fn collect_paths(root: &Path, directory: &Path, paths: &mut Vec<PathBuf>) -> Result<(), StepError> {
    for entry in fs::read_dir(directory)
        .map_err(|source| io_error("enumerate immutable source tree", source))?
    {
        let entry = entry.map_err(|source| io_error("read immutable source entry", source))?;
        let path = entry.path();
        let kind = entry
            .file_type()
            .map_err(|source| io_error("inspect immutable source entry", source))?;
        if !(kind.is_dir() || kind.is_file() || kind.is_symlink()) {
            return Err(StepError::Input(format!(
                "special file in source snapshot: {}",
                path.display()
            )));
        }
        paths.push(path.clone());
        if paths.len() > MAX_ENTRIES {
            return Err(StepError::Input(format!(
                "source snapshot exceeds entry bound: {}",
                root.display()
            )));
        }
        if kind.is_dir() {
            collect_paths(root, &path, paths)?;
        }
    }
    Ok(())
}

pub fn source_tree_sha256(root: &Path) -> Result<String, StepError> {
    let mut paths = Vec::new();
    collect_paths(root, root, &mut paths)?;
    paths.sort();
    let mut hash = Sha256::new();
    for path in paths {
        let relative =
            path.strip_prefix(root).map_err(|_| StepError::Input("source escaped root".into()))?;
        let name =
            relative.to_str().ok_or_else(|| StepError::Input("non-UTF8 source path".into()))?;
        let kind = fs::symlink_metadata(&path)
            .map_err(|source| io_error("inspect immutable source object", source))?
            .file_type();
        let (tag, bytes) = if kind.is_dir() {
            (b'd', Vec::new())
        } else if kind.is_symlink() {
            let target = fs::read_link(&path)
                .map_err(|source| io_error("read immutable source link", source))?;
            (b'l', target.as_os_str().as_encoded_bytes().to_vec())
        } else if kind.is_file() {
            (b'f', compare::digest_checked_file(&path, MAX_FILE_BYTES)?.into_bytes())
        } else {
            return Err(StepError::Input("source object became special".into()));
        };
        hash.update([tag]);
        hash.update((name.len() as u64).to_be_bytes());
        hash.update(name.as_bytes());
        hash.update((bytes.len() as u64).to_be_bytes());
        hash.update(bytes);
    }
    Ok(base16ct::lower::encode_string(&hash.finalize()))
}
