//! Session builder — batch theory compilation with dependency resolution.
//!
//! This module ties together:
//! - `TheoryGraph` — dependency graph + topological sort
//! - `TheoryProcessor` — individual theory file processing
//! - `TheoryRegistry` — parent theory lookup
//!
//! The pipeline:
//! 1. Scan a directory for `.thy` files
//! 2. Parse headers to extract theory names and imports
//! 3. Build a dependency DAG
//! 4. Topological sort (respecting import order)
//! 5. Load each theory using `TheoryProcessor`, passing parent theories
//! 6. Register loaded theories in `TheoryRegistry`
//! 7. Report results (success count, theorem count, errors)

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::{Path, PathBuf},
    sync::Arc,
    time::Instant,
};

use crate::theory::{
    loader::{TheoryLoadError, TheoryProcessor},
    registry::TheoryRegistry,
    thy_header::parse_header,
    verify_classifier::{VerifyReport, VerifyResult, VerifyStatus},
};

// =========================================================================
// TheoryFile — metadata about a .thy file
// =========================================================================

/// Parsed header information from a .thy file.
#[derive(Debug, Clone)]
pub struct TheoryFile {
    /// Theory name
    pub name: String,
    /// File path
    pub path: PathBuf,
    /// Names of imported theories
    pub imports: Vec<String>,
}

impl TheoryFile {
    /// Parse the complete header; malformed files are not candidates for loading.
    pub fn parse(path: &Path) -> Result<Self, TheoryLoadError> {
        let source = std::fs::read_to_string(path).map_err(|source| TheoryLoadError::Io {
            path: path.to_path_buf(),
            source: Arc::new(source),
        })?;
        let header = parse_header(&source).map_err(|detail| TheoryLoadError::Header { detail })?;
        Ok(Self { name: header.name, path: path.to_path_buf(), imports: header.imports })
    }
}

// =========================================================================
// BuildResult — outcome of a session build
// =========================================================================

/// Result of building a session.
#[derive(Debug, Clone)]
pub struct BuildResult {
    /// Number of theories successfully loaded.
    pub loaded: usize,
    /// Total number of theories found.
    pub total: usize,
    /// Legacy `TransitionalStrictClosed` results registered in core theories.
    /// This is not a count of new-kernel `TrustedTheorem` values.
    pub theorems: usize,
    /// Number of failed theories.
    pub failed: usize,
    /// Per-file diagnostics including the source path and theory identity.
    pub error_messages: Vec<String>,
    /// Error from an incomplete directory enumeration; not counted as a theory.
    pub scan_error: Option<String>,
    /// List of loaded theory names.
    pub theory_names: Vec<String>,
}

impl BuildResult {
    pub fn is_success(&self) -> bool {
        self.failed == 0 && self.scan_error.is_none()
    }
}

fn classify_processing_error(
    error: &TheoryLoadError,
    attempted: usize,
    message: String,
) -> VerifyStatus {
    match error {
        TheoryLoadError::Io { .. } => VerifyStatus::IoError { message },
        TheoryLoadError::Header { .. }
        | TheoryLoadError::Lexical { .. }
        | TheoryLoadError::MissingEnd { .. }
        | TheoryLoadError::UnexpectedCommand { .. }
        | TheoryLoadError::MalformedCommand { .. } => {
            VerifyStatus::SyntaxError { message, attempted }
        },
        TheoryLoadError::MissingImports { .. }
        | TheoryLoadError::MissingImport { .. }
        | TheoryLoadError::ImportMerge { .. }
        | TheoryLoadError::UnresolvedDependencies { .. } => {
            VerifyStatus::DependencyError { message, attempted }
        },
        TheoryLoadError::UnsupportedHeaderDeclarations => {
            VerifyStatus::UnsupportedError { message, attempted }
        },
        TheoryLoadError::DuplicateTheory { .. } => {
            VerifyStatus::ConflictError { message, attempted }
        },
        TheoryLoadError::Declaration { .. } => VerifyStatus::TypeError { message, attempted },
        TheoryLoadError::Proof { .. } => VerifyStatus::ProofFailure { attempted },
        TheoryLoadError::ProcessingPanic { .. } | TheoryLoadError::TransactionConsumed => {
            VerifyStatus::InternalError { message }
        },
    }
}

fn format_failure(path: &Path, name: &str, error: &TheoryLoadError) -> String {
    format!("{} (theory `{name}`): {error}", path.display())
}

// =========================================================================
// SessionBuilder
// =========================================================================

/// Builds a session by loading all discovered .thy files.
pub struct SessionBuilder {
    registry: TheoryRegistry,
    discovered: BTreeSet<PathBuf>,
    files: HashMap<String, TheoryFile>,
    blocked: BTreeMap<PathBuf, (String, TheoryLoadError)>,
    order: Vec<String>,
    scan_errors: BTreeMap<PathBuf, String>,
    accept_all: bool,
}

impl SessionBuilder {
    pub fn new() -> Self {
        Self {
            registry: TheoryRegistry::new(),
            discovered: BTreeSet::new(),
            files: HashMap::new(),
            blocked: BTreeMap::new(),
            order: Vec::new(),
            scan_errors: BTreeMap::new(),
            accept_all: false,
        }
    }

    pub fn set_accept_all(&mut self, accept: bool) {
        self.accept_all = accept;
    }

    /// Counts distinct discovered paths, including unreadable and malformed theory files.
    pub fn scan(&mut self, dir: &Path) -> std::io::Result<usize> {
        let mut dirs = vec![dir.to_path_buf()];
        let mut seen_dirs = BTreeSet::new();
        let mut count = 0;
        while let Some(directory) = dirs.pop() {
            let entries = match std::fs::read_dir(&directory) {
                Ok(entries) => entries,
                Err(error) => {
                    self.scan_errors
                        .insert(dir.to_path_buf(), format!("{}: {error}", directory.display()));
                    return Err(error);
                },
            };
            let canonical_dir = directory.canonicalize().unwrap_or(directory.clone());
            if !seen_dirs.insert(canonical_dir) {
                continue;
            }
            for entry in entries {
                let entry = match entry {
                    Ok(entry) => entry,
                    Err(error) => {
                        self.scan_errors
                            .insert(dir.to_path_buf(), format!("{}: {error}", directory.display()));
                        return Err(error);
                    },
                };
                let path = entry.path();
                if path.is_dir() {
                    dirs.push(path);
                } else if path.extension().is_some_and(|ext| ext == "thy") {
                    let identity = path.canonicalize().unwrap_or(path);
                    count += usize::from(self.discovered.insert(identity));
                }
            }
        }
        self.scan_errors.remove(dir);
        self.resolve_dependencies();
        Ok(count)
    }

    /// Re-read all paths, so an earlier successful parent cannot satisfy a later build.
    fn prepare(&mut self) {
        self.files.clear();
        self.blocked.clear();
        self.order.clear();
        let mut claims: BTreeMap<String, Vec<TheoryFile>> = BTreeMap::new();
        for path in &self.discovered {
            match TheoryFile::parse(path) {
                Ok(file) => claims.entry(file.name.clone()).or_default().push(file),
                Err(error) => {
                    let name = path.file_stem().map_or_else(
                        || "<unknown>".to_string(),
                        |stem| stem.to_string_lossy().into_owned(),
                    );
                    self.blocked.insert(path.clone(), (name, error));
                },
            }
        }
        for (name, claimants) in claims {
            if name == "Pure" || claimants.len() != 1 {
                for file in claimants {
                    self.blocked.insert(
                        file.path,
                        (name.clone(), TheoryLoadError::DuplicateTheory { name: name.clone() }),
                    );
                }
            } else {
                // A single claimant is guaranteed by the preceding branch.
                let file = claimants.into_iter().next().expect("single claimant");
                self.files.insert(name, file);
            }
        }
        self.schedule();
    }

    /// Reject absent parents before sorting every edge of the remaining import DAG.
    fn reject_invalid_imports(&mut self) {
        loop {
            let mut rejected = Vec::new();
            for file in self.files.values() {
                let error = if file.imports.is_empty() {
                    Some(TheoryLoadError::MissingImports { theory: file.name.clone() })
                } else {
                    file.imports
                        .iter()
                        .find(|parent| {
                            parent.as_str() != "Pure" && !self.files.contains_key(*parent)
                        })
                        .map(|parent| TheoryLoadError::MissingImport {
                            theory: file.name.clone(),
                            import: parent.clone(),
                        })
                };
                if let Some(error) = error {
                    rejected.push((file.name.clone(), error));
                }
            }
            if rejected.is_empty() {
                return;
            }
            for (name, error) in rejected {
                if let Some(file) = self.files.remove(&name) {
                    self.blocked.insert(file.path, (name, error));
                }
            }
        }
    }

    fn schedule(&mut self) {
        self.reject_invalid_imports();
        let mut in_degree: BTreeMap<String, usize> = BTreeMap::new();
        let mut children: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (name, file) in &self.files {
            let parents: BTreeSet<_> =
                file.imports.iter().filter(|parent| parent.as_str() != "Pure").collect();
            in_degree.insert(name.clone(), parents.len());
            for parent in parents {
                children.entry(parent.clone()).or_default().push(name.clone());
            }
        }
        let mut ready: BTreeSet<String> = in_degree
            .iter()
            .filter(|(_, degree)| **degree == 0)
            .map(|(name, _)| name.clone())
            .collect();
        while let Some(name) = ready.pop_first() {
            if let Some(dependents) = children.get(&name) {
                // Each child was added from the same files map as in_degree.
                for child in dependents {
                    let degree = in_degree.get_mut(child).expect("scheduled child");
                    *degree -= 1;
                    if *degree == 0 {
                        ready.insert(child.clone());
                    }
                }
            }
            self.order.push(name);
        }
        for (name, degree) in in_degree {
            if degree != 0 {
                // Every unscheduled name was inserted into files before sorting.
                let file = self.files.remove(&name).expect("unscheduled theory");
                self.blocked.insert(
                    file.path,
                    (
                        name.clone(),
                        TheoryLoadError::UnresolvedDependencies {
                            theory: name,
                            imports: file.imports,
                        },
                    ),
                );
            }
        }
    }

    pub fn resolve_dependencies(&mut self) -> Vec<String> {
        self.prepare();
        self.order.clone()
    }

    fn build_one(&mut self, file: &TheoryFile) -> Result<(usize, usize), (TheoryLoadError, usize)> {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let source = std::fs::read_to_string(&file.path).map_err(|source| {
                (TheoryLoadError::Io { path: file.path.clone(), source: Arc::new(source) }, 0)
            })?;
            let mut processor = TheoryProcessor::for_theory(self.registry.clone(), &file.name);
            processor.accept_all = self.accept_all;
            let theory = processor.process_source(&source).map_err(|errors| {
                (
                    errors.into_iter().next().unwrap_or_else(|| TheoryLoadError::ProcessingPanic {
                        command: file.name.clone(),
                        line: 0,
                        detail: "processor failed without a diagnostic".to_string(),
                    }),
                    processor.lemma_count,
                )
            })?;
            let attempted = processor.lemma_count;
            let verified = processor.closed_theorem_count();
            if verified != attempted {
                return Err((
                    TheoryLoadError::ProcessingPanic {
                        command: file.name.clone(),
                        line: 0,
                        detail: format!(
                            "{attempted} lemma declarations but {verified} verified results"
                        ),
                    },
                    attempted,
                ));
            }
            self.registry.register(theory);
            Ok((verified, attempted))
        }));
        result.unwrap_or_else(|payload| {
            let detail = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|text| (*text).to_string()))
                .unwrap_or_else(|| "non-string panic payload".to_string());
            Err((
                TheoryLoadError::ProcessingPanic { command: file.name.clone(), line: 0, detail },
                0,
            ))
        })
    }

    pub fn build(&mut self) -> BuildResult {
        self.prepare();
        self.registry = TheoryRegistry::new();
        let mut result = BuildResult {
            loaded: 0,
            total: self.discovered.len(),
            theorems: 0,
            failed: 0,
            error_messages: self
                .blocked
                .iter()
                .map(|(path, (name, error))| format_failure(path, name, error))
                .collect(),
            scan_error: self.scan_error_message(),
            theory_names: Vec::new(),
        };
        for name in self.order.clone() {
            // prepare() leaves every scheduled name in files until the next build.
            let file = self.files.get(&name).expect("scheduled theory").clone();
            match self.build_one(&file) {
                Ok((verified, _)) => {
                    result.loaded += 1;
                    result.theorems += verified;
                    result.theory_names.push(name);
                },
                Err((error, _)) => {
                    result.error_messages.push(format_failure(&file.path, &name, &error))
                },
            }
        }
        result.failed = result.total - result.loaded;
        result
    }

    pub fn registry(&self) -> &TheoryRegistry {
        &self.registry
    }

    pub fn order(&self) -> &[String] {
        &self.order
    }

    fn scan_error_message(&self) -> Option<String> {
        (!self.scan_errors.is_empty())
            .then(|| self.scan_errors.values().cloned().collect::<Vec<_>>().join("; "))
    }

    pub fn build_with_classifier(&mut self) -> VerifyReport {
        self.prepare();
        self.registry = TheoryRegistry::new();
        let mut results = Vec::with_capacity(self.discovered.len());
        for (path, (name, error)) in &self.blocked {
            results.push(VerifyResult {
                name: name.clone(),
                path: path.clone(),
                status: classify_processing_error(error, 0, format_failure(path, name, error)),
                elapsed: Default::default(),
                theorem_count: 0,
            });
        }
        for name in self.order.clone() {
            // prepare() leaves every scheduled name in files until the next build.
            let file = self.files.get(&name).expect("scheduled theory").clone();
            let start = Instant::now();
            let outcome = self.build_one(&file);
            let elapsed = start.elapsed();
            let (status, theorem_count) = match outcome {
                Ok((verified, 0)) => (VerifyStatus::NoLemmas, verified),
                Ok((verified, attempted)) if verified == attempted => {
                    (VerifyStatus::FullSuccess { attempted }, verified)
                },
                Ok((_, attempted)) => (VerifyStatus::ProofFailure { attempted }, 0),
                Err((error, attempted)) => (
                    classify_processing_error(
                        &error,
                        attempted,
                        format_failure(&file.path, &name, &error),
                    ),
                    0,
                ),
            };
            results.push(VerifyResult { name, path: file.path, status, elapsed, theorem_count });
        }
        results.sort_by(|a, b| a.path.cmp(&b.path));
        let mut report = VerifyReport::new(results);
        report.scan_error = self.scan_error_message();
        report
    }
}

impl Default for SessionBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_processing_error_uses_error_variant_not_text() {
        let text = "proof-context certification syntax token".to_string();
        let proof = TheoryLoadError::Proof {
            line: 1,
            source: crate::isar::proof_result::GoalExportError::OpenSubgoals,
        };
        assert_eq!(
            classify_processing_error(&proof, 1, text.clone()),
            VerifyStatus::ProofFailure { attempted: 1 }
        );
        let header = TheoryLoadError::Header { detail: text.clone() };
        assert_eq!(
            classify_processing_error(&header, 0, text.clone()),
            VerifyStatus::SyntaxError { message: text, attempted: 0 }
        );
        let import =
            TheoryLoadError::MissingImport { theory: "Child".into(), import: "Parent".into() };
        assert_eq!(
            classify_processing_error(&import, 0, "Parent unavailable".into()),
            VerifyStatus::DependencyError { message: "Parent unavailable".into(), attempted: 0 }
        );
        assert_eq!(
            classify_processing_error(
                &TheoryLoadError::UnsupportedHeaderDeclarations,
                0,
                "header unsupported".into()
            ),
            VerifyStatus::UnsupportedError { message: "header unsupported".into(), attempted: 0 }
        );
        assert_eq!(
            classify_processing_error(
                &TheoryLoadError::DuplicateTheory { name: "Child".into() },
                0,
                "duplicate Child".into()
            ),
            VerifyStatus::ConflictError { message: "duplicate Child".into(), attempted: 0 }
        );
        assert_eq!(
            classify_processing_error(
                &TheoryLoadError::MalformedCommand { command: "lemma".into(), line: 2 },
                1,
                "malformed lemma".into()
            ),
            VerifyStatus::SyntaxError { message: "malformed lemma".into(), attempted: 1 }
        );
    }
}
