//! Replayable, process-supervised diagnostics for the legacy HOL verifier.
//! This manifest records inputs only; it never grants theorem authority.

use std::{
    collections::{HashMap, HashSet},
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    path::{Component, Path, PathBuf},
    time::Instant,
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{
    hol_loader::{HolTheoremDb, ParsedLemma, parse_lemmas_with_loc, parse_theory_header},
    theory_graph::{TheoryGraph, TheoryNode},
};
use crate::isar::method::{
    AUTO_LIMIT, LemmaVerification, PROOF_SEARCH_BUDGET, classify_verify_result, verify_lemma,
};

const MANIFEST_VERSION: u32 = 2;
const DEFAULT_AUTO_LIMIT: usize = 100;
const MAX_AUTO_LIMIT: usize = 10_000;
const PROOF_BUDGET: usize = 200;
const WORKER_THREADS: usize = 1;
/// Stack reserved for the sole legacy diagnostic computation worker.
pub const DIAGNOSTIC_STACK_BYTES: usize = 256 * 1024 * 1024;
const MAX_SOURCE_BYTES: u64 = 16 * 1024 * 1024;
const MAX_MANIFEST_BYTES: u64 = 8 * 1024 * 1024;
const MAX_SCAN_BYTES: u64 = 2 * 1024 * 1024 * 1024;
const MAX_SCAN_FILES: usize = 20_000;
const MAX_SCAN_ENTRIES: usize = 100_000;
const MAX_PRELOAD: usize = 200;
const MAX_NAME_BYTES: usize = 256;
const CONTEXT_POLICY: &str = "no_fallback";

/// An invalid user-supplied input or an operational failure, with its original cause.
#[derive(Debug, Error)]
pub enum DiagnosticError {
    /// Invalid CLI input, manifest, source identity, or replay budget (user-fixable).
    #[error("invalid diagnostic input: {0}")]
    Input(String),
    /// Reading an input file failed (user-fixable).
    #[error("failed to read diagnostic input {path}: {source}")]
    InputIo {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// Parsing an input manifest failed (user-fixable).
    #[error("failed to parse diagnostic manifest {path}: {source}")]
    Manifest {
        path: PathBuf,
        #[source]
        source: serde_json::Error,
    },
    /// The manifest already exists; create_new must not overwrite it (user-fixable).
    #[error("diagnostic manifest already exists at {path}: {source}")]
    ManifestExists {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// The theory graph could not be scanned (operational failure).
    #[error("failed to scan theory root {path}: {source}")]
    Scan {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// The graph could not be ordered (operational failure).
    #[error("failed to order theories: {0}")]
    Graph(String),
    /// A source parser panicked (operational failure, not a proof result).
    #[error("failed to parse theory source {path}: parser panicked")]
    Parser { path: PathBuf },
    /// A database or verifier operation panicked (fatal diagnostic failure).
    #[error("diagnostic {phase} computation panicked")]
    Computation { phase: &'static str },
    /// An output or manifest write failed (operational failure).
    #[error("failed to write diagnostic output {path}: {source}")]
    OutputIo {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// Serializing an output record failed (operational failure).
    #[error("failed to serialize diagnostic event: {0}")]
    Serialize(#[from] serde_json::Error),
}

impl DiagnosticError {
    pub fn is_input(&self) -> bool {
        matches!(
            self,
            Self::Input(_)
                | Self::InputIo { .. }
                | Self::Manifest { .. }
                | Self::ManifestExists { .. }
        )
    }
}

#[derive(Debug, Clone)]
pub enum ManifestMode {
    Create(PathBuf),
    Replay(PathBuf),
}

#[derive(Debug)]
pub struct DiagnosticRequest {
    pub source_root: PathBuf,
    pub context_root: PathBuf,
    pub theory: String,
    pub lemma: String,
    pub mode: ManifestMode,
    pub auto_limit: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceEntry {
    theory: String,
    path: PathBuf,
    sha256: String,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct OverrideSelection {
    discarded: SourceEntry,
    selected: SourceEntry,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    version: u32,
    proof_authority: bool,
    source_root: PathBuf,
    context_root: PathBuf,
    context_policy: String,
    theory: String,
    lemma: String,
    auto_limit: usize,
    proof_search_budget: usize,
    worker_threads: usize,
    worker_stack_bytes: usize,
    source_overrides: Vec<OverrideSelection>,
    sources: Vec<SourceEntry>,
    context_sources: Vec<SourceEntry>,
    context_overrides: Vec<OverrideSelection>,
    target: SourceEntry,
}

#[derive(Default, Serialize)]
struct Timings {
    bootstrap_ms: u128,
    scan_ms: u128,
    load_ms: u128,
    builtins_ms: u128,
    parse_ms: u128,
    search_ms: u128,
    classify_ms: u128,
}

#[derive(Serialize)]
struct PhaseEvent<'a> {
    event: &'static str,
    phase: &'static str,
    status: &'static str,
    theory: Option<&'a str>,
    lemma: Option<&'a str>,
    elapsed_ms: u128,
}

fn emit_event<T: Serialize>(out: &mut impl Write, event: &T) -> Result<(), DiagnosticError> {
    serde_json::to_writer(&mut *out, event)?;
    out.write_all(b"\n")
        .and_then(|_| out.flush())
        .map_err(|source| DiagnosticError::OutputIo { path: PathBuf::from("stdout"), source })
}

fn emit_phase(
    out: &mut impl Write,
    phase: &'static str,
    status: &'static str,
    theory: Option<&str>,
    lemma: Option<&str>,
    elapsed_ms: u128,
) -> Result<(), DiagnosticError> {
    emit_event(out, &PhaseEvent { event: "phase", phase, status, theory, lemma, elapsed_ms })
}

fn validate_name(kind: &str, name: &str) -> Result<(), DiagnosticError> {
    // Legacy header keys may include quotes; these are labels, never path components.
    if name.is_empty() || name.len() > MAX_NAME_BYTES || name.chars().any(char::is_control) {
        return Err(DiagnosticError::Input(format!("invalid {kind} identifier {name:?}")));
    }
    Ok(())
}

fn validate_budget(budget: usize) -> Result<(), DiagnosticError> {
    if !(1..=MAX_AUTO_LIMIT).contains(&budget) {
        return Err(DiagnosticError::Input(format!(
            "auto-limit must be between 1 and {MAX_AUTO_LIMIT}"
        )));
    }
    Ok(())
}

fn read_bounded(path: &Path, cap: u64) -> Result<Vec<u8>, DiagnosticError> {
    let file = File::open(path)
        .map_err(|source| DiagnosticError::InputIo { path: path.into(), source })?;
    let mut bytes = Vec::new();
    file.take(cap + 1)
        .read_to_end(&mut bytes)
        .map_err(|source| DiagnosticError::InputIo { path: path.into(), source })?;
    if bytes.len() as u64 > cap {
        return Err(DiagnosticError::Input(format!(
            "{} exceeds {}-byte limit",
            path.display(),
            cap
        )));
    }
    Ok(bytes)
}

fn resolve_source(root: &Path, relative: &Path) -> Result<PathBuf, DiagnosticError> {
    if relative.as_os_str().is_empty()
        || relative.components().any(|c| !matches!(c, Component::Normal(_)))
        || relative.extension().is_none_or(|ext| ext != "thy")
    {
        return Err(DiagnosticError::Input(format!(
            "invalid root-relative theory path {}",
            relative.display()
        )));
    }
    let path = root.join(relative);
    let canonical = fs::canonicalize(&path)
        .map_err(|source| DiagnosticError::InputIo { path: path.clone(), source })?;
    if !canonical.starts_with(root) || !canonical.is_file() {
        return Err(DiagnosticError::Input(format!(
            "theory path escapes source root or is not a file: {}",
            relative.display()
        )));
    }
    Ok(canonical)
}

fn compute_source_hash(bytes: &[u8]) -> String {
    base16ct::lower::encode_string(&Sha256::digest(bytes))
}

fn make_entry(root: &Path, theory: &str, path: &Path) -> Result<SourceEntry, DiagnosticError> {
    let canonical = fs::canonicalize(path)
        .map_err(|source| DiagnosticError::InputIo { path: path.into(), source })?;
    let relative = canonical.strip_prefix(root).map_err(|_| {
        DiagnosticError::Input(format!("theory {theory} escapes source root: {}", path.display()))
    })?;
    let bytes = read_bounded(&canonical, MAX_SOURCE_BYTES)?;
    Ok(SourceEntry {
        theory: theory.into(),
        path: relative.into(),
        sha256: compute_source_hash(&bytes),
    })
}

fn verify_entry(root: &Path, entry: &SourceEntry) -> Result<(PathBuf, String), DiagnosticError> {
    validate_name("theory", &entry.theory)?;
    if entry.sha256.len() != 64 || !entry.sha256.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err(DiagnosticError::Input(format!("invalid SHA256 for {}", entry.theory)));
    }
    let path = resolve_source(root, &entry.path)?;
    let bytes = read_bounded(&path, MAX_SOURCE_BYTES)?;
    if compute_source_hash(&bytes) != entry.sha256 {
        return Err(DiagnosticError::Input(format!(
            "source hash changed: {}",
            entry.path.display()
        )));
    }
    let source = String::from_utf8(bytes).map_err(|source| {
        DiagnosticError::Input(format!("invalid UTF-8 in {}: {source}", entry.path.display()))
    })?;
    if parse_theory_header(&source).is_none_or(|(name, _)| name != entry.theory) {
        return Err(DiagnosticError::Input(format!(
            "theory identity changed: {}",
            entry.path.display()
        )));
    }
    Ok((path, source))
}

fn validate_entries(
    root: &Path,
    entries: &[SourceEntry],
    label: &str,
) -> Result<(), DiagnosticError> {
    if entries.is_empty() || entries.len() > MAX_SCAN_FILES {
        return Err(DiagnosticError::Input(format!("empty or oversized {label} list")));
    }
    let mut names = HashSet::new();
    let mut paths = HashSet::new();
    for entry in entries {
        validate_name("theory", &entry.theory)?;
        let path = resolve_source(root, &entry.path)?;
        if !names.insert(&entry.theory) || !paths.insert(path) {
            return Err(DiagnosticError::Input(format!(
                "duplicate {label} theory or source: {}",
                entry.theory
            )));
        }
    }
    Ok(())
}

fn is_same_entry(left: &SourceEntry, right: &SourceEntry) -> bool {
    left.theory == right.theory && left.path == right.path && left.sha256 == right.sha256
}

fn validate_overrides(
    root: &Path,
    selected: &[SourceEntry],
    overrides: &[OverrideSelection],
) -> Result<(), DiagnosticError> {
    if overrides.len() > MAX_SCAN_FILES {
        return Err(DiagnosticError::Input("oversized duplicate-theory selection list".into()));
    }
    let mut replaced: HashMap<&str, &SourceEntry> = HashMap::new();
    for pair in overrides {
        if pair.discarded.theory != pair.selected.theory
            || pair.discarded.path == pair.selected.path
        {
            return Err(DiagnosticError::Input("invalid duplicate-theory selection".into()));
        }
        verify_entry(root, &pair.discarded)?;
        if let Some(previous) = replaced.insert(&pair.discarded.theory, &pair.selected)
            && !is_same_entry(previous, &pair.discarded)
        {
            return Err(DiagnosticError::Input("disconnected duplicate-theory selection".into()));
        }
    }
    for (name, winner) in replaced {
        if !selected.iter().any(|entry| entry.theory == name && is_same_entry(entry, winner)) {
            return Err(DiagnosticError::Input(format!(
                "duplicate-theory winner disagrees: {name}"
            )));
        }
    }
    Ok(())
}

fn validate_manifest(
    root: &Path,
    context_root: &Path,
    manifest: &Manifest,
    request: &DiagnosticRequest,
) -> Result<(), DiagnosticError> {
    if manifest.version != MANIFEST_VERSION
        || manifest.proof_authority
        || manifest.theory != request.theory
        || manifest.lemma != request.lemma
        || manifest.proof_search_budget != PROOF_BUDGET
        || manifest.worker_threads != WORKER_THREADS
        || manifest.worker_stack_bytes != DIAGNOSTIC_STACK_BYTES
    {
        return Err(DiagnosticError::Input(
            "manifest version or target disagrees with request".into(),
        ));
    }
    if manifest.source_root.as_path() != root
        || manifest.context_root.as_path() != context_root
        || manifest.context_policy != CONTEXT_POLICY
    {
        return Err(DiagnosticError::Input(
            "manifest source or context root/policy disagrees with request".into(),
        ));
    }
    validate_budget(manifest.auto_limit)?;
    if request.auto_limit.is_some_and(|limit| limit != manifest.auto_limit) {
        return Err(DiagnosticError::Input("auto-limit conflicts with replay manifest".into()));
    }
    if manifest.sources.is_empty() || manifest.sources.len() > MAX_PRELOAD {
        return Err(DiagnosticError::Input("manifest has empty or oversized preload list".into()));
    }
    validate_entries(root, &manifest.sources, "preload")?;
    validate_entries(context_root, &manifest.context_sources, "bootstrap")?;
    let mut source_selected = manifest.sources.clone();
    source_selected.push(manifest.target.clone());
    validate_overrides(root, &source_selected, &manifest.source_overrides)?;
    validate_overrides(context_root, &manifest.context_sources, &manifest.context_overrides)?;
    if manifest.target.theory != manifest.theory {
        return Err(DiagnosticError::Input("target theory does not match manifest target".into()));
    }
    resolve_source(root, &manifest.target.path)?;
    if manifest.sources.iter().any(|entry| {
        (entry.theory == manifest.target.theory || entry.path == manifest.target.path)
            && !is_same_entry(entry, &manifest.target)
    }) {
        return Err(DiagnosticError::Input("target conflicts with preloaded source".into()));
    }
    Ok(())
}

fn scan_theory(
    root: &Path,
    graph: &mut TheoryGraph,
    overrides: &mut Vec<OverrideSelection>,
) -> Result<(), DiagnosticError> {
    let mut dirs = vec![root.to_path_buf()];
    let (mut entries, mut files, mut total) = (0usize, 0usize, 0u64);
    while let Some(dir) = dirs.pop() {
        for entry in fs::read_dir(&dir)
            .map_err(|source| DiagnosticError::Scan { path: dir.clone(), source })?
        {
            let entry =
                entry.map_err(|source| DiagnosticError::Scan { path: dir.clone(), source })?;
            let path = entry.path();
            entries += 1;
            if entries > MAX_SCAN_ENTRIES {
                return Err(DiagnosticError::Input(format!(
                    "source scan exceeds {MAX_SCAN_ENTRIES} entries"
                )));
            }
            let kind = entry
                .file_type()
                .map_err(|source| DiagnosticError::Scan { path: path.clone(), source })?;
            if kind.is_symlink() {
                return Err(DiagnosticError::Input(format!(
                    "symlink in source scan: {}",
                    path.display()
                )));
            }
            if kind.is_dir() {
                dirs.push(path);
                continue;
            }
            if path.extension().is_none_or(|ext| ext != "thy") {
                continue;
            }
            if !kind.is_file() {
                return Err(DiagnosticError::Input(format!(
                    "non-regular theory source: {}",
                    path.display()
                )));
            }
            files += 1;
            if files > MAX_SCAN_FILES {
                return Err(DiagnosticError::Input(format!(
                    "source scan exceeds {MAX_SCAN_FILES} theory files"
                )));
            }
            let bytes = read_scanned_source(root, &path)?;
            total = total.saturating_add(bytes.len() as u64);
            if total > MAX_SCAN_BYTES {
                return Err(DiagnosticError::Input(format!(
                    "source scan exceeds {MAX_SCAN_BYTES} bytes"
                )));
            }
            insert_theory(root, graph, overrides, path, bytes)?;
        }
    }
    Ok(())
}

fn read_scanned_source(root: &Path, path: &Path) -> Result<Vec<u8>, DiagnosticError> {
    let canonical = fs::canonicalize(path)
        .map_err(|source| DiagnosticError::InputIo { path: path.into(), source })?;
    if !canonical.starts_with(root) {
        return Err(DiagnosticError::Input(format!(
            "theory escapes source root: {}",
            path.display()
        )));
    }
    read_bounded(&canonical, MAX_SOURCE_BYTES)
}

fn insert_theory(
    root: &Path,
    graph: &mut TheoryGraph,
    overrides: &mut Vec<OverrideSelection>,
    path: PathBuf,
    bytes: Vec<u8>,
) -> Result<(), DiagnosticError> {
    let source = String::from_utf8(bytes).map_err(|cause| {
        DiagnosticError::Input(format!("invalid UTF-8 in {}: {cause}", path.display()))
    })?;
    // TheoryGraph::scan skips sources with no parseable header; duplicate names overwrite.
    let Some((name, imports)) = parse_theory_header(&source) else {
        return Ok(());
    };
    validate_name("theory", &name)?;
    if let Some(previous) = graph.nodes.get(&name) {
        overrides.push(OverrideSelection {
            discarded: make_entry(root, &name, &previous.path)?,
            selected: make_entry(root, &name, &path)?,
        });
    }
    graph.nodes.insert(
        name.clone(),
        TheoryNode { name, path, imports, loaded: false, theorems: Vec::new(), lemmas: Vec::new() },
    );
    Ok(())
}

fn capture_sources(
    root: &Path,
) -> Result<(TheoryGraph, Vec<String>, Vec<OverrideSelection>), DiagnosticError> {
    let mut graph = TheoryGraph::new();
    let mut overrides = Vec::new();
    scan_theory(root, &mut graph, &mut overrides)?;
    let order = graph.topological_sort().map_err(DiagnosticError::Graph)?;
    Ok((graph, order, overrides))
}

fn ordered_entries(
    root: &Path,
    graph: &TheoryGraph,
    order: &[String],
) -> Result<Vec<SourceEntry>, DiagnosticError> {
    order
        .iter()
        .map(|name| {
            let node = graph
                .nodes
                .get(name)
                .ok_or_else(|| DiagnosticError::Graph(format!("missing scanned theory {name}")))?;
            make_entry(root, name, &node.path)
        })
        .collect()
}

fn create_manifest(
    root: &Path,
    context_root: &Path,
    request: &DiagnosticRequest,
) -> Result<Manifest, DiagnosticError> {
    let (graph, order, all_source_overrides) = capture_sources(root)?;
    let sources = ordered_entries(root, &graph, &order[..order.len().min(MAX_PRELOAD)])?;
    let node = graph.nodes.get(&request.theory).ok_or_else(|| {
        DiagnosticError::Input(format!(
            "target theory not found in source scan: {}",
            request.theory
        ))
    })?;
    let target = make_entry(root, &request.theory, &node.path)?;
    let source_overrides = all_source_overrides
        .into_iter()
        .filter(|pair| {
            sources.iter().any(|entry| entry.theory == pair.selected.theory)
                || pair.selected.theory == request.theory
        })
        .collect();
    let (context_graph, context_order, context_overrides) = capture_sources(context_root)?;
    let context_sources = ordered_entries(context_root, &context_graph, &context_order)?;
    let manifest = Manifest {
        version: MANIFEST_VERSION,
        proof_authority: false,
        source_root: root.into(),
        context_root: context_root.into(),
        context_policy: CONTEXT_POLICY.into(),
        theory: request.theory.clone(),
        lemma: request.lemma.clone(),
        auto_limit: request.auto_limit.unwrap_or(DEFAULT_AUTO_LIMIT),
        proof_search_budget: PROOF_BUDGET,
        worker_threads: WORKER_THREADS,
        worker_stack_bytes: DIAGNOSTIC_STACK_BYTES,
        sources,
        source_overrides,
        context_sources,
        context_overrides,
        target,
    };
    validate_manifest(root, context_root, &manifest, request)?;
    Ok(manifest)
}

fn get_manifest(
    root: &Path,
    context_root: &Path,
    request: &DiagnosticRequest,
) -> Result<Manifest, DiagnosticError> {
    match &request.mode {
        ManifestMode::Create(path) => {
            let manifest = create_manifest(root, context_root, request)?;
            let bytes = serde_json::to_vec_pretty(&manifest)?;
            if bytes.len() as u64 >= MAX_MANIFEST_BYTES {
                return Err(DiagnosticError::Input(format!(
                    "manifest exceeds {MAX_MANIFEST_BYTES}-byte limit"
                )));
            }
            let mut file =
                OpenOptions::new().write(true).create_new(true).open(path).map_err(|source| {
                    if source.kind() == io::ErrorKind::AlreadyExists {
                        DiagnosticError::ManifestExists { path: path.clone(), source }
                    } else {
                        DiagnosticError::OutputIo { path: path.clone(), source }
                    }
                })?;
            file.write_all(&bytes)
                .and_then(|_| file.write_all(b"\n"))
                .and_then(|_| file.flush())
                .map_err(|source| DiagnosticError::OutputIo { path: path.clone(), source })?;
            Ok(manifest)
        },
        ManifestMode::Replay(path) => {
            let bytes = read_bounded(path, MAX_MANIFEST_BYTES)?;
            let manifest = serde_json::from_slice(&bytes)
                .map_err(|source| DiagnosticError::Manifest { path: path.clone(), source })?;
            validate_manifest(root, context_root, &manifest, request)?;
            Ok(manifest)
        },
    }
}

fn parse_source(path: &Path, source: &str) -> Result<Vec<ParsedLemma>, DiagnosticError> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        parse_lemmas_with_loc(source, &path.to_string_lossy())
    }))
    .map_err(|_| DiagnosticError::Parser { path: path.into() })
}

fn with_diagnostic_phase<T>(
    phase: &'static str,
    work: impl FnOnce() -> T,
) -> Result<T, DiagnosticError> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(work))
        .map_err(|_| DiagnosticError::Computation { phase })
}

fn extend_bootstrap(
    db: &mut HolTheoremDb,
    type_env: &mut crate::core::types::TypeEnv,
    path: &Path,
    source: &str,
) -> Result<(), DiagnosticError> {
    let mut lemmas = parse_source(path, source)?;
    let file_env = HolTheoremDb::build_type_env(source);
    type_env.consts.extend(file_env.consts);
    type_env.types.extend(file_env.types);
    db.checked_definitions.extend(HolTheoremDb::build_checked_definition_sources(source, type_env));
    for lemma in &mut lemmas {
        lemma.type_annotate(type_env);
    }
    db.extend(&lemmas);
    Ok(())
}

fn bootstrap_sources(
    root: &Path,
    manifest: &Manifest,
    out: &mut impl Write,
) -> Result<HolTheoremDb, DiagnosticError> {
    with_diagnostic_phase("bootstrap", || {
        let mut db = HolTheoremDb::new();
        let mut type_env = crate::core::types::TypeEnv::new();
        for entry in &manifest.context_sources {
            emit_phase(out, "bootstrap", "start", Some(&entry.theory), None, 0)?;
            let start = Instant::now();
            let (path, source) = verify_entry(root, entry)?;
            extend_bootstrap(&mut db, &mut type_env, &path, &source)?;
            emit_phase(
                out,
                "bootstrap",
                "finish",
                Some(&entry.theory),
                None,
                start.elapsed().as_millis(),
            )?;
        }
        emit_phase(out, "bootstrap_builtins", "start", None, None, 0)?;
        let start = Instant::now();
        HolTheoremDb::add_builtins(&mut db);
        emit_phase(out, "bootstrap_builtins", "finish", None, None, start.elapsed().as_millis())?;
        db.type_env = type_env;
        // load_all_theories adds builtins again after graph.load_all installs its type environment.
        emit_phase(out, "bootstrap_builtins", "start", None, None, 0)?;
        let start = Instant::now();
        HolTheoremDb::add_builtins(&mut db);
        emit_phase(out, "bootstrap_builtins", "finish", None, None, start.elapsed().as_millis())?;
        Ok(db)
    })?
}

fn load_sources(
    root: &Path,
    manifest: &Manifest,
    bootstrap: &HolTheoremDb,
    out: &mut impl Write,
) -> Result<HolTheoremDb, DiagnosticError> {
    with_diagnostic_phase("load", || {
        let mut db = HolTheoremDb::new();
        for entry in &manifest.sources {
            emit_phase(out, "load", "start", Some(&entry.theory), None, 0)?;
            let start = Instant::now();
            let (path, source) = verify_entry(root, entry)?;
            let mut lemmas = parse_source(&path, &source)?;
            for lemma in &mut lemmas {
                lemma.type_annotate(&bootstrap.type_env);
            }
            db.extend(&lemmas);
            emit_phase(
                out,
                "load",
                "finish",
                Some(&entry.theory),
                None,
                start.elapsed().as_millis(),
            )?;
        }
        Ok(db)
    })?
}

fn find_target(root: &Path, manifest: &Manifest) -> Result<ParsedLemma, DiagnosticError> {
    let (path, source) = verify_entry(root, &manifest.target)?;
    parse_source(&path, &source)?
        .into_iter()
        .find(|lemma| lemma.name == manifest.lemma && lemma.proof_script.is_some())
        .ok_or_else(|| {
            DiagnosticError::Input(format!(
                "proof-bearing lemma {} not found in theory {}",
                manifest.lemma, manifest.theory
            ))
        })
}

fn verify_target(
    db: &HolTheoremDb,
    lemma: &ParsedLemma,
    limit: usize,
) -> Result<LemmaVerification, DiagnosticError> {
    AUTO_LIMIT.with(|cell| {
        let old = cell.replace(limit);
        PROOF_SEARCH_BUDGET.with(|cell| cell.set(PROOF_BUDGET));
        let result = with_diagnostic_phase("search", || verify_lemma(lemma, db));
        cell.set(old);
        result
    })
}

/// Run a single legacy verification under an external hard timeout and resource supervisor.
/// A successful process exit means the diagnostic completed, not that the proof succeeded.
pub fn run(request: &DiagnosticRequest, out: &mut impl Write) -> Result<(), DiagnosticError> {
    validate_name("theory", &request.theory)?;
    validate_name("lemma", &request.lemma)?;
    if let Some(limit) = request.auto_limit {
        validate_budget(limit)?;
    }
    let root = fs::canonicalize(&request.source_root)
        .map_err(|source| DiagnosticError::InputIo { path: request.source_root.clone(), source })?;
    if !root.is_dir() {
        return Err(DiagnosticError::Input(format!("not a source directory: {}", root.display())));
    }
    let context_root = fs::canonicalize(&request.context_root).map_err(|source| {
        DiagnosticError::InputIo { path: request.context_root.clone(), source }
    })?;
    if !context_root.is_dir() {
        return Err(DiagnosticError::Input(format!(
            "not a context directory: {}",
            context_root.display()
        )));
    }
    emit_event(
        out,
        &serde_json::json!({"event": "configuration",
        "source_root": root.as_path(), "context_root": context_root.as_path(), "context_policy": CONTEXT_POLICY,
        "proof_search_budget": PROOF_BUDGET, "worker_threads": WORKER_THREADS,
        "worker_stack_bytes": DIAGNOSTIC_STACK_BYTES}),
    )?;
    let mut timings = Timings::default();
    emit_phase(out, "scan", "start", Some(&request.theory), Some(&request.lemma), 0)?;
    let start = Instant::now();
    let manifest = get_manifest(&root, &context_root, request)?;
    timings.scan_ms = start.elapsed().as_millis();
    emit_phase(
        out,
        "scan",
        "finish",
        Some(&request.theory),
        Some(&request.lemma),
        timings.scan_ms,
    )?;
    run_manifest(&root, &context_root, &manifest, &mut timings, out)
}

fn run_manifest(
    root: &Path,
    context_root: &Path,
    manifest: &Manifest,
    timings: &mut Timings,
    out: &mut impl Write,
) -> Result<(), DiagnosticError> {
    emit_phase(out, "bootstrap", "start", None, None, 0)?;
    let start = Instant::now();
    let bootstrap = bootstrap_sources(context_root, manifest, out)?;
    timings.bootstrap_ms = start.elapsed().as_millis();
    emit_phase(out, "bootstrap", "finish", None, None, timings.bootstrap_ms)?;
    emit_phase(out, "load", "start", None, None, 0)?;
    let start = Instant::now();
    let mut db = load_sources(root, manifest, &bootstrap, out)?;
    timings.load_ms = start.elapsed().as_millis();
    emit_phase(out, "load", "finish", None, None, timings.load_ms)?;
    emit_phase(out, "builtins", "start", None, None, 0)?;
    let start = Instant::now();
    with_diagnostic_phase("builtins", || HolTheoremDb::add_builtins(&mut db))?;
    timings.builtins_ms = start.elapsed().as_millis();
    emit_phase(out, "builtins", "finish", None, None, timings.builtins_ms)?;
    emit_phase(out, "parse", "start", Some(&manifest.theory), Some(&manifest.lemma), 0)?;
    let start = Instant::now();
    let lemma = with_diagnostic_phase("parse", || find_target(root, manifest))??;
    db.bind_verification_source(&lemma);
    timings.parse_ms = start.elapsed().as_millis();
    emit_phase(
        out,
        "parse",
        "finish",
        Some(&manifest.theory),
        Some(&manifest.lemma),
        timings.parse_ms,
    )?;
    finish_diagnostic(&db, &lemma, manifest, timings, out)
}

fn finish_diagnostic(
    db: &HolTheoremDb,
    lemma: &ParsedLemma,
    manifest: &Manifest,
    timings: &mut Timings,
    out: &mut impl Write,
) -> Result<(), DiagnosticError> {
    emit_phase(out, "search", "start", Some(&manifest.theory), Some(&manifest.lemma), 0)?;
    let start = Instant::now();
    let verification = verify_target(db, lemma, manifest.auto_limit)?;
    timings.search_ms = start.elapsed().as_millis();
    emit_phase(
        out,
        "search",
        "finish",
        Some(&manifest.theory),
        Some(&manifest.lemma),
        timings.search_ms,
    )?;
    emit_phase(out, "classify", "start", Some(&manifest.theory), Some(&manifest.lemma), 0)?;
    let start = Instant::now();
    let label = classify_verify_result(&lemma.name, &verification).label();
    timings.classify_ms = start.elapsed().as_millis();
    emit_phase(
        out,
        "classify",
        "finish",
        Some(&manifest.theory),
        Some(&manifest.lemma),
        timings.classify_ms,
    )?;
    emit_event(
        out,
        &serde_json::json!({"event": "result", "diagnostic_completed": true,
        "proof_authority": false, "theory": manifest.theory, "lemma": manifest.lemma, "outcome": label,
        "auto_limit": manifest.auto_limit, "proof_search_budget": manifest.proof_search_budget,
        "worker_threads": manifest.worker_threads, "worker_stack_bytes": manifest.worker_stack_bytes,
        "timings": timings }),
    )
}
