//! Reference-only file identities and strict input handling; never proof authority.

use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use serde_json::{Map, Value};
use sha2::{Digest, Sha256};

use crate::runner::{StepError, io_error};

pub const COMMIT: &str = "765fb2460a57eb46e8490283241ad46f1fac857f";
const HASH_BUFFER_BYTES: usize = 64 * 1024;
const SOURCE_PREFIXES: [&str; 3] = ["$ISABELLE_HOME/", "/work/fixed-source/", "~~/"];

pub fn require(condition: bool, message: impl Into<String>) -> Result<(), StepError> {
    if condition { Ok(()) } else { Err(StepError::Input(message.into())) }
}

pub fn field<'a>(value: &'a Value, key: &str) -> Result<&'a Value, StepError> {
    value.get(key).ok_or_else(|| StepError::Input(format!("missing field: {key}")))
}

pub fn as_array<'a>(value: &'a Value, context: &str) -> Result<&'a Vec<Value>, StepError> {
    value.as_array().ok_or_else(|| StepError::Input(format!("{context}: expected array")))
}

pub fn as_object<'a>(value: &'a Value, context: &str) -> Result<&'a Map<String, Value>, StepError> {
    value.as_object().ok_or_else(|| StepError::Input(format!("{context}: expected object")))
}

pub fn as_str<'a>(value: &'a Value, context: &str) -> Result<&'a str, StepError> {
    value.as_str().ok_or_else(|| StepError::Input(format!("{context}: expected string")))
}

pub fn require_fields(value: &Value, fields: &[&str], context: &str) -> Result<(), StepError> {
    let object = as_object(value, context)?;
    require(
        object.len() == fields.len() && fields.iter().all(|key| object.contains_key(*key)),
        format!("{context}: expected exactly {}", fields.join(", ")),
    )
}

pub fn require_regular(path: &Path) -> Result<(), StepError> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|source| io_error(format!("inspect reference file {}", path.display()), source))?;
    require(
        metadata.is_file() && !metadata.file_type().is_symlink(),
        format!("{}: ordinary regular file required", path.display()),
    )
}

pub fn open_regular(path: &Path) -> Result<File, StepError> {
    require_regular(path)?;
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW);
    }
    let file = options
        .open(path)
        .map_err(|source| io_error(format!("open reference file {}", path.display()), source))?;
    let metadata = file.metadata().map_err(|source| {
        io_error(format!("inspect opened reference file {}", path.display()), source)
    })?;
    require(metadata.is_file(), format!("{}: opened object is not regular", path.display()))?;
    Ok(file)
}

pub fn digest_bytes(bytes: &[u8]) -> String {
    base16ct::lower::encode_string(&Sha256::digest(bytes))
}

pub fn digest_file(path: &Path) -> Result<String, StepError> {
    let mut file = open_regular(path)?;
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; HASH_BUFFER_BYTES];
    loop {
        let count = file.read(&mut buffer).map_err(|source| {
            io_error(format!("hash reference file {}", path.display()), source)
        })?;
        if count == 0 {
            return Ok(base16ct::lower::encode_string(&hasher.finalize()));
        }
        hasher.update(&buffer[..count]);
    }
}

pub fn resolve_source_path(symbolic: &str, source_root: &Path) -> Result<PathBuf, StepError> {
    let relative = SOURCE_PREFIXES
        .iter()
        .find_map(|prefix| symbolic.strip_prefix(prefix))
        .ok_or_else(|| StepError::Input(format!("unexpected official source path {symbolic:?}")))?;
    require(
        !relative.is_empty()
            && !relative.starts_with('/')
            && !relative.contains('\0')
            && relative.split('/').all(|part| part != "." && part != ".."),
        format!("unsafe source path {symbolic:?}"),
    )?;
    let root = source_root.canonicalize().map_err(|source| {
        io_error(format!("resolve source root {}", source_root.display()), source)
    })?;
    let resolved = root
        .join(relative)
        .canonicalize()
        .map_err(|source| io_error(format!("resolve fixed source {symbolic:?}"), source))?;
    require(resolved.starts_with(&root), format!("source escapes fixed root: {symbolic:?}"))?;
    Ok(resolved)
}

pub fn read_json(path: &Path) -> Result<Value, StepError> {
    let file = open_regular(path)?;
    decode_json_reader(std::io::BufReader::new(file), &format!("read JSON {}", path.display()))
}

pub fn decode_json(bytes: &[u8], context: &str) -> Result<Value, StepError> {
    decode_json_reader(bytes, context)
}

fn decode_json_reader(reader: impl Read, name: &str) -> Result<Value, StepError> {
    isabelle_evidence::decode_json_reader(reader, name).map_err(|error| match error {
        isabelle_evidence::EvidenceError::Json { name, source } => {
            StepError::Json { operation: name, source }
        },
        isabelle_evidence::EvidenceError::Input(detail) => StepError::Input(detail),
    })
}

pub fn write_json_exclusive(path: &Path, value: &Value) -> Result<(), StepError> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(path)
        .map_err(|source| io_error(format!("create JSON evidence {}", path.display()), source))?;
    serde_json::to_writer_pretty(&mut file, value).map_err(|source| StepError::Json {
        operation: format!("serialize JSON evidence {}", path.display()),
        source,
    })?;
    file.write_all(b"\n")
        .map_err(|source| io_error(format!("finish JSON evidence {}", path.display()), source))
}
