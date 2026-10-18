//! Live Isabelle theory import graph. Source text is read once through the restricted host;
//! the same retained bytes are used for the digest and for subsequent execution.
use std::collections::BTreeMap;
use std::path::{Component, Path, PathBuf};

use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::ml::host::files::{HostIoError, RestrictedHost};
use crate::ml::host::lifecycle::TaskLease;
use crate::theory::thy_header::{TheoryHeader, parse_header};

/// The approved nine roots, in source-independent build order.
pub const NATIVE_ROOTS: [&str; 9] = [
    "HOL.HOL",
    "HOL.Orderings",
    "HOL.Set",
    "HOL.Nat",
    "HOL.List",
    "HOL.Fun",
    "HOL.Product_Type",
    "HOL.Sum_Type",
    "HOL.Option",
];

/// A theory's real source and its original header, available to the later execution stage.
#[derive(Debug)]
pub struct SourceTheory {
    pub name: String,
    pub path: PathBuf,
    pub header: TheoryHeader,
    /// Original normalized import edges, not the canonical logical owner parents.
    pub parents: Vec<String>,
    pub sha256: String,
    text: String,
}

impl SourceTheory {
    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn bytes(&self) -> &[u8] {
        self.text.as_bytes()
    }
}

/// Dependencies are topological: a node occurs exactly once after all its parents.
#[derive(Debug)]
pub struct NativeSourceGraph {
    roots: Vec<String>,
    theories: Vec<SourceTheory>,
}

impl NativeSourceGraph {
    pub fn roots(&self) -> &[String] {
        &self.roots
    }

    pub fn theories(&self) -> &[SourceTheory] {
        &self.theories
    }

    /// Load the fixed nine roots, never deriving them from a frozen report or ML data.
    pub fn load_fixed(host: &RestrictedHost, lease: &TaskLease) -> Result<Self, SourceGraphError> {
        Self::load(host, lease, &NATIVE_ROOTS)
    }

    /// Resolve caller-selected roots for independent structural checks. Production uses `load_fixed`.
    pub fn load(
        host: &RestrictedHost,
        lease: &TaskLease,
        roots: &[&str],
    ) -> Result<Self, SourceGraphError> {
        if roots.is_empty() {
            return Err(SourceGraphError::EmptyRoots);
        }
        let mut builder = GraphBuilder {
            host,
            lease,
            seen: BTreeMap::new(),
            active: BTreeMap::new(),
            theories: Vec::new(),
        };
        for &root in roots {
            let path = resolve_root(root)?;
            builder.visit(root, path)?;
        }
        Ok(Self {
            roots: roots.iter().map(|root| (*root).to_owned()).collect(),
            theories: builder.theories,
        })
    }
}

/// Invalid source graphs are user-fixable; host permission/lifecycle failures retain their cause.
#[derive(Debug, Error)]
pub enum SourceGraphError {
    #[error("native source graph requires at least one root")]
    EmptyRoots,
    #[error("unsupported theory name or session {name:?}")]
    InvalidName { name: String },
    #[error("theory import {import:?} in {from} escapes its configured source session")]
    Escape { from: String, import: String },
    #[error("missing source for {name} at {path}: {source}")]
    Missing {
        name: String,
        path: PathBuf,
        #[source]
        source: Box<HostIoError>,
    },
    #[error("reading source for {name} at {path}: {source}")]
    Read {
        name: String,
        path: PathBuf,
        #[source]
        source: Box<HostIoError>,
    },
    #[error("decoding source for {name} at {path}: {source}")]
    Utf8 {
        name: String,
        path: PathBuf,
        #[source]
        source: std::string::FromUtf8Error,
    },
    #[error("parsing header for {name} at {path}: {detail}")]
    Header { name: String, path: PathBuf, detail: String },
    #[error("theory name mismatch for {name} at {path}: declared {declared}")]
    HeaderName { name: String, path: PathBuf, declared: String },
    #[error("theory {name} resolves to both {first} and {second}")]
    Conflict { name: String, first: PathBuf, second: PathBuf },
    #[error("cyclic theory imports: {chain:?}")]
    Cycle { chain: Vec<String> },
}

struct GraphBuilder<'a> {
    host: &'a RestrictedHost,
    lease: &'a TaskLease,
    seen: BTreeMap<String, PathBuf>,
    active: BTreeMap<String, usize>,
    theories: Vec<SourceTheory>,
}

struct PendingSource {
    theory: SourceTheory,
    next_import: usize,
}

impl GraphBuilder<'_> {
    fn visit(&mut self, name: &str, path: PathBuf) -> Result<(), SourceGraphError> {
        let mut stack = Vec::new();
        self.push_source(name, path, &mut stack)?;
        while let Some(mut frame) = stack.pop() {
            if let Some(import) = frame.theory.header.imports.get(frame.next_import) {
                let (parent, parent_path) =
                    resolve_import(&frame.theory.name, &frame.theory.path, import)?;
                frame.next_import += 1;
                frame.theory.parents.push(parent.clone());
                stack.push(frame);
                self.push_source(&parent, parent_path, &mut stack)?;
            } else {
                self.active.remove(&frame.theory.name);
                self.theories.push(frame.theory);
            }
        }
        Ok(())
    }

    fn push_source(
        &mut self,
        name: &str,
        path: PathBuf,
        stack: &mut Vec<PendingSource>,
    ) -> Result<(), SourceGraphError> {
        if let Some(first) = self.seen.get(name) {
            if first != &path {
                return Err(SourceGraphError::Conflict {
                    name: name.to_owned(),
                    first: first.clone(),
                    second: path,
                });
            }
            if let Some(&start) = self.active.get(name) {
                let mut chain: Vec<_> =
                    stack[start..].iter().map(|frame| frame.theory.name.clone()).collect();
                chain.push(name.to_owned());
                return Err(SourceGraphError::Cycle { chain });
            }
            return Ok(());
        }
        let theory = self.read_source(name, path.clone())?;
        self.seen.insert(name.to_owned(), path);
        self.active.insert(name.to_owned(), stack.len());
        stack.push(PendingSource { theory, next_import: 0 });
        Ok(())
    }

    fn read_source(&self, name: &str, path: PathBuf) -> Result<SourceTheory, SourceGraphError> {
        let bytes = self.host.read_source(self.lease, &path).map_err(|source| {
            if matches!(&source, HostIoError::Io { source, .. } if source.kind() == std::io::ErrorKind::NotFound) {
                SourceGraphError::Missing {
                    name: name.to_owned(), path: path.clone(), source: Box::new(source),
                }
            } else {
                SourceGraphError::Read {
                    name: name.to_owned(), path: path.clone(), source: Box::new(source),
                }
            }
        })?;
        let text = String::from_utf8(bytes).map_err(|source| SourceGraphError::Utf8 {
            name: name.to_owned(),
            path: path.clone(),
            source,
        })?;
        let header = parse_header(&text).map_err(|detail| SourceGraphError::Header {
            name: name.to_owned(),
            path: path.clone(),
            detail,
        })?;
        if header.name != base_name(name) {
            return Err(SourceGraphError::HeaderName {
                name: name.to_owned(),
                path,
                declared: header.name,
            });
        }
        let sha256 = format!("{:x}", Sha256::digest(text.as_bytes()));
        let parents = Vec::with_capacity(header.imports.len());
        Ok(SourceTheory { name: name.to_owned(), path, header, parents, sha256, text })
    }
}

fn base_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

fn source_session(name: &str) -> Result<&'static str, SourceGraphError> {
    if name == "Pure" {
        return Ok("Pure");
    }
    if name.starts_with("HOL.") {
        return Ok("HOL");
    }
    if name.starts_with("Tools.") {
        return Ok("Tools");
    }
    Err(SourceGraphError::InvalidName { name: name.to_owned() })
}

fn resolve_root(name: &str) -> Result<PathBuf, SourceGraphError> {
    let session = source_session(name)?;
    let base = base_name(name);
    if !is_theory_component(base) || (name != "Pure" && name.matches('.').count() != 1) {
        return Err(SourceGraphError::InvalidName { name: name.to_owned() });
    }
    Ok(PathBuf::from("src").join(session).join(format!("{base}.thy")))
}

fn is_theory_component(component: &str) -> bool {
    !component.is_empty()
        && component.chars().all(|character| character.is_ascii_alphanumeric() || character == '_')
}

fn resolve_import(
    from: &str,
    from_path: &Path,
    import: &str,
) -> Result<(String, PathBuf), SourceGraphError> {
    if import == "Pure" || import.starts_with("HOL.") || import.starts_with("Tools.") {
        return Ok((import.to_owned(), resolve_root(import)?));
    }
    let session = source_session(from)?;
    let relative = Path::new(import);
    let base = relative.file_name().and_then(|part| part.to_str()).unwrap_or("");
    if !is_theory_component(base)
        || import.contains('.') && !import.starts_with("./") && !import.starts_with("../")
    {
        return Err(SourceGraphError::InvalidName { name: import.to_owned() });
    }
    let parent = format!("{session}.{base}");
    let directory = from_path.parent().ok_or_else(|| SourceGraphError::Escape {
        from: from.to_owned(),
        import: import.to_owned(),
    })?;
    let raw = directory.join(relative).with_extension("thy");
    let path = normalize_import_path(&raw).ok_or_else(|| SourceGraphError::Escape {
        from: from.to_owned(),
        import: import.to_owned(),
    })?;
    if !path.starts_with(Path::new("src").join(session)) {
        return Err(SourceGraphError::Escape { from: from.to_owned(), import: import.to_owned() });
    }
    Ok((parent, path))
}

fn normalize_import_path(path: &Path) -> Option<PathBuf> {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Normal(value) => normalized.push(value),
            Component::CurDir => {},
            Component::ParentDir if normalized.pop() => {},
            _ => return None,
        }
    }
    Some(normalized)
}
