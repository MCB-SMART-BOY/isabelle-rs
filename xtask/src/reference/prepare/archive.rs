use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::Read;
use std::path::{Component, Path, PathBuf};

use flate2::read::GzDecoder;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use tar::{Archive, EntryType};

use super::failure;
use crate::runner::{StepError, io_error};

const MAX_MEMBERS: usize = 200_000;
const MAX_EXPANDED_BYTES: u64 = 8 * 1024 * 1024 * 1024;
const HASH_BUFFER_BYTES: usize = 64 * 1024;
const MAX_GLOBAL_METADATA_BYTES: u64 = 64 * 1024;

#[derive(Clone)]
struct Member {
    name: PathBuf,
    kind: EntryType,
    link: Option<PathBuf>,
    digest: Option<String>,
}

fn archive_reader(path: &Path, gzip: bool) -> Result<Archive<Box<dyn Read>>, StepError> {
    let file =
        File::open(path).map_err(|e| io_error(format!("open archive {}", path.display()), e))?;
    let reader: Box<dyn Read> = if gzip { Box::new(GzDecoder::new(file)) } else { Box::new(file) };
    Ok(Archive::new(reader))
}

fn normalize(path: &Path, base: &Path, root: &str) -> Result<PathBuf, StepError> {
    let mut parts = Vec::new();
    for component in base.join(path).components() {
        match component {
            Component::CurDir => {},
            Component::Normal(p) => parts.push(p.to_os_string()),
            Component::ParentDir if !parts.is_empty() => {
                parts.pop();
            },
            _ => return Err(failure("preflight tar member", path, "unsafe path")),
        }
    }
    let result: PathBuf = parts.into_iter().collect();
    if result.as_os_str().is_empty()
        || (!root.is_empty() && result != Path::new(root) && !result.starts_with(root))
    {
        return Err(failure("preflight tar member", path, "outside archive root"));
    }
    Ok(result)
}

fn read_member_link(
    entry: &tar::Entry<'_, Box<dyn Read>>,
    name: &Path,
    kind: EntryType,
    root: &str,
) -> Result<Option<PathBuf>, StepError> {
    let mut link = entry
        .link_name()
        .map_err(|e| io_error(format!("read link {}", name.display()), e))?
        .map(|p| p.into_owned());
    if (kind.is_symlink() || kind.is_hard_link()) && link.is_none() {
        return Err(failure("preflight archive", name, "link target required"));
    }
    if let Some(target) = &link {
        if target.is_absolute() {
            return Err(failure("preflight tar member", name, "absolute link"));
        }
        if target.to_str().is_none() {
            return Err(failure("preflight tar member", name, "non-UTF-8 link target"));
        }
        let base =
            if kind.is_symlink() { name.parent().unwrap_or(Path::new("")) } else { Path::new("") };
        let normalized = normalize(target, base, root)?;
        if kind.is_hard_link() {
            link = Some(normalized);
        }
    }
    Ok(link)
}

fn hash_member(entry: &mut impl Read, name: &Path) -> Result<String, StepError> {
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; HASH_BUFFER_BYTES];
    loop {
        let count = entry
            .read(&mut buffer)
            .map_err(|e| io_error(format!("hash tar member {}", name.display()), e))?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    Ok(base16ct::lower::encode_string(&hasher.finalize()))
}

fn validate_member_links(members: &[Member]) -> Result<(), StepError> {
    let symlinks: HashSet<_> =
        members.iter().filter(|m| m.kind.is_symlink()).map(|m| m.name.as_path()).collect();
    for member in members {
        if member.name.ancestors().skip(1).any(|ancestor| symlinks.contains(ancestor)) {
            return Err(failure("preflight archive", &member.name, "symlink ancestor"));
        }
    }
    let regular: HashSet<_> = members
        .iter()
        .filter(|member| member.digest.is_some())
        .map(|member| member.name.as_path())
        .collect();
    for member in members.iter().filter(|member| member.kind.is_hard_link()) {
        let target = member
            .link
            .as_ref()
            .ok_or_else(|| failure("preflight archive", &member.name, "hardlink missing target"))?;
        if !regular.contains(target.as_path()) {
            return Err(failure(
                "preflight archive",
                &member.name,
                "hardlink does not target a regular member",
            ));
        }
    }
    Ok(())
}

fn consume_global_metadata(
    entry: &mut tar::Entry<'_, Box<dyn Read>>,
    archive: &Path,
) -> Result<bool, StepError> {
    if !entry.header().entry_type().is_pax_global_extensions() {
        return Ok(false);
    }
    if entry.size() > MAX_GLOBAL_METADATA_BYTES {
        return Err(failure("preflight PAX metadata", archive, "global header exceeds policy"));
    }
    let extensions = entry
        .pax_extensions()
        .map_err(|e| io_error(format!("decode global PAX metadata {}", archive.display()), e))?
        .ok_or_else(|| failure("preflight PAX metadata", archive, "missing global records"))?;
    for extension in extensions {
        let extension = extension
            .map_err(|e| io_error(format!("decode global PAX record {}", archive.display()), e))?;
        // Git's global comment describes provenance, not a filesystem member.
        // Reject unimplemented overrides rather than silently ignoring path/size semantics.
        if extension.key_bytes() != b"comment" {
            return Err(failure("preflight PAX metadata", archive, "unsupported global attribute"));
        }
    }
    Ok(true)
}

fn inspect(path: &Path, gzip: bool, root: &str) -> Result<Vec<Member>, StepError> {
    let mut archive = archive_reader(path, gzip)?;
    let mut members = Vec::new();
    let mut names = HashSet::new();
    let mut expanded = 0u64;
    let entries =
        archive.entries().map_err(|e| io_error(format!("list archive {}", path.display()), e))?;
    for (index, entry) in entries.enumerate() {
        let mut entry =
            entry.map_err(|e| io_error(format!("read archive {}", path.display()), e))?;
        if index >= MAX_MEMBERS {
            return Err(failure("preflight archive", path, "too many members"));
        }
        expanded = expanded
            .checked_add(entry.size())
            .ok_or_else(|| failure("preflight archive", path, "size overflow"))?;
        if expanded > MAX_EXPANDED_BYTES {
            return Err(failure("preflight archive", path, "expanded size exceeds policy"));
        }
        if consume_global_metadata(&mut entry, path)? {
            continue;
        }
        let raw = entry
            .path()
            .map_err(|e| io_error(format!("decode archive member {}", path.display()), e))?;
        let raw = raw.into_owned();
        if raw.to_str().is_none() {
            return Err(failure("preflight tar member", &raw, "non-UTF-8 member path"));
        }
        if raw.is_absolute() || raw.components().any(|p| matches!(p, Component::ParentDir)) {
            return Err(failure("preflight tar member", &raw, "unsafe path"));
        }
        let name = normalize(&raw, Path::new(""), root)?;
        if !names.insert(name.clone()) {
            return Err(failure("preflight archive", &name, "duplicate member"));
        }
        let kind = entry.header().entry_type();
        if !(kind.is_file() || kind.is_dir() || kind.is_symlink() || kind.is_hard_link()) {
            return Err(failure("preflight archive", &name, "unsupported member type"));
        }
        let link = read_member_link(&entry, &name, kind, root)?;
        let digest = if kind.is_file() { Some(hash_member(&mut entry, &name)?) } else { None };
        members.push(Member { name, kind, link, digest });
    }
    validate_member_links(&members)?;
    Ok(members)
}

fn extract(path: &Path, gzip: bool, destination: &Path) -> Result<(), StepError> {
    let parent =
        destination.parent().ok_or_else(|| failure("extract archive", destination, "no parent"))?;
    let stage = tempfile::Builder::new()
        .prefix(".reference-extract-")
        .tempdir_in(parent)
        .map_err(|e| io_error(format!("stage archive near {}", destination.display()), e))?;
    let mut archive = archive_reader(path, gzip)?;
    let entries =
        archive.entries().map_err(|e| io_error(format!("list archive {}", path.display()), e))?;
    for entry in entries {
        let mut entry =
            entry.map_err(|e| io_error(format!("read archive {}", path.display()), e))?;
        if consume_global_metadata(&mut entry, path)? {
            continue;
        }
        let member = entry
            .path()
            .map_err(|e| io_error(format!("decode archive {}", path.display()), e))?
            .into_owned();
        if !entry.unpack_in(stage.path()).map_err(|e| {
            io_error(format!("extract {} from {}", member.display(), path.display()), e)
        })? {
            return Err(failure("extract archive", &member, "member escaped destination"));
        }
    }
    fs::rename(stage.path(), destination)
        .map_err(|e| io_error(format!("publish archive at {}", destination.display()), e))?;
    let _ = stage.keep();
    Ok(())
}

fn reject_unexpected_members(
    expected: &HashSet<PathBuf>,
    destination: &Path,
    allowed_empty: &[&str],
) -> Result<(), StepError> {
    let mut stack = vec![destination.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in
            fs::read_dir(&dir).map_err(|e| io_error(format!("enumerate {}", dir.display()), e))?
        {
            let entry = entry.map_err(|e| io_error(format!("enumerate {}", dir.display()), e))?;
            let path = entry.path();
            let relative = path
                .strip_prefix(destination)
                .map_err(|_| failure("verify extraction", &path, "outside destination"))?;
            let kind = entry
                .file_type()
                .map_err(|e| io_error(format!("inspect {}", path.display()), e))?;
            if !expected.contains(relative)
                && !(allowed_empty.iter().any(|allowed| relative == Path::new(allowed))
                    && kind.is_dir()
                    && fs::read_dir(&path)
                        .map_err(|e| io_error(format!("enumerate {}", path.display()), e))?
                        .next()
                        .is_none())
            {
                return Err(failure("verify extraction", relative, "unexpected member"));
            }
            if kind.is_dir() {
                stack.push(path);
            }
        }
    }
    Ok(())
}

fn compare(
    members: &[Member],
    destination: &Path,
    allowed_empty: &[&str],
) -> Result<(), StepError> {
    let mut expected = HashSet::new();
    let regular: HashMap<_, _> = members
        .iter()
        .filter_map(|m| m.digest.as_ref().map(|digest| (m.name.as_path(), digest)))
        .collect();
    for member in members {
        expected.insert(member.name.clone());
        let path = destination.join(&member.name);
        let metadata = fs::symlink_metadata(&path)
            .map_err(|e| io_error(format!("verify extracted {}", path.display()), e))?;
        let file_type = metadata.file_type();
        let valid = if member.kind.is_dir() {
            file_type.is_dir()
        } else if member.kind.is_symlink() {
            let target = member.link.as_ref().ok_or_else(|| {
                failure("verify extracted symlink", &path, "missing expected target")
            })?;
            file_type.is_symlink()
                && fs::read_link(&path)
                    .map_err(|e| io_error(format!("read link {}", path.display()), e))?
                    == *target
        } else {
            file_type.is_file()
        };
        if !valid {
            return Err(failure("verify extracted member", &path, "missing or wrong type"));
        }
        let digest = if member.kind.is_hard_link() {
            let target = member.link.as_ref().ok_or_else(|| {
                failure("verify extracted hardlink", &path, "missing expected target")
            })?;
            regular.get(target.as_path()).copied()
        } else {
            member.digest.as_ref()
        };
        if let Some(digest) = digest
            && crate::reference::common::digest_file(&path)? != digest.as_str()
        {
            return Err(failure("verify extracted file", &path, "missing or changed bytes"));
        }
    }
    reject_unexpected_members(&expected, destination, allowed_empty)
}

pub(crate) fn verify_tree(
    archive: &Path,
    destination: &Path,
    gzip: bool,
    root: &str,
    allowed_empty: &[&str],
) -> Result<(usize, Value), StepError> {
    inspect_tree(archive, destination, gzip, root, allowed_empty, true)
}

pub(super) fn verify_existing_tree(
    archive: &Path,
    destination: &Path,
    gzip: bool,
    root: &str,
    allowed_empty: &[&str],
) -> Result<(usize, Value), StepError> {
    inspect_tree(archive, destination, gzip, root, allowed_empty, false)
}

fn inspect_tree(
    archive: &Path,
    destination: &Path,
    gzip: bool,
    root: &str,
    allowed_empty: &[&str],
    should_extract: bool,
) -> Result<(usize, Value), StepError> {
    let members = inspect(archive, gzip, root)?;
    if should_extract && !destination.exists() && fs::symlink_metadata(destination).is_err() {
        extract(archive, gzip, destination)?;
    }
    if !fs::symlink_metadata(destination)
        .map_err(|e| io_error(format!("inspect {}", destination.display()), e))?
        .file_type()
        .is_dir()
    {
        return Err(failure("verify extracted root", destination, "ordinary directory required"));
    }
    compare(&members, destination, allowed_empty)?;
    let files = members
        .iter()
        .filter_map(|m| {
            m.digest
                .as_ref()
                .map(|digest| json!({"path": m.name.to_string_lossy(), "sha256": digest}))
        })
        .collect::<Vec<_>>();
    Ok((members.len(), Value::Array(files)))
}

pub(super) fn verify_source_links(archive: &Path, source: &Path) -> Result<(), StepError> {
    for member in inspect(archive, false, "")? {
        let path = source.join(&member.name);
        if member.kind.is_symlink() {
            let expected = member.link.ok_or_else(|| {
                failure("verify Gitlink source link", &path, "missing expected target")
            })?;
            if fs::read_link(&path)
                .map_err(|e| io_error(format!("verify source symlink {}", path.display()), e))?
                != expected
            {
                return Err(failure("verify Gitlink source link", &path, "target differs"));
            }
        } else if let Some(digest) = member.digest
            && crate::reference::common::digest_file(&path)? != digest
        {
            return Err(failure("verify Gitlink source bytes", &path, "archive differs"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
