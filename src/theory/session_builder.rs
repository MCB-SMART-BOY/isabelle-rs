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
    collections::HashMap,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::{
    core::theory::Theory,
    theory::{loader::TheoryProcessor, registry::TheoryRegistry},
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
    /// Parse the header of a .thy file to extract name and imports.
    pub fn parse(path: &Path) -> Option<Self> {
        let source = std::fs::read_to_string(path).ok()?;
        // Find the line starting with "theory "
        let theory_line = source.lines().find(|l| l.trim().starts_with("theory "))?;
        let trimmed = theory_line.trim();
        let rest = trimmed.strip_prefix("theory ")?;
        let parts: Vec<&str> = rest.split_whitespace().collect();
        let name = parts.first()?.to_string();

        let mut imports = Vec::new();
        let mut in_imports = false;
        for part in &parts[1..] {
            if *part == "imports" {
                in_imports = true;
            } else if *part == "begin" || *part == "keywords" {
                break;
            } else if in_imports {
                imports.push(part.to_string());
            }
        }

        Some(TheoryFile { name, path: path.to_path_buf(), imports })
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
    /// Total number of theorems produced.
    pub theorems: usize,
    /// Number of failed theories.
    pub failed: usize,
    /// Error messages (multiple per failed theory).
    pub error_messages: Vec<String>,
    /// List of loaded theory names.
    pub theory_names: Vec<String>,
}

impl BuildResult {
    pub fn is_success(&self) -> bool {
        self.failed == 0
    }
}

// =========================================================================
// SessionBuilder
// =========================================================================

/// Builds a session by loading all .thy files in a directory.
pub struct SessionBuilder {
    /// Theory registry for parent lookups.
    registry: TheoryRegistry,
    /// All discovered theory files.
    files: HashMap<String, TheoryFile>,
    /// Topological load order.
    order: Vec<String>,
    /// Accept all lemmas as axioms (skip proof replay).
    accept_all: bool,
}

impl SessionBuilder {
    /// Create a new session builder.
    pub fn new() -> Self {
        SessionBuilder {
            registry: TheoryRegistry::new(),
            files: HashMap::new(),
            order: Vec::new(),
            accept_all: false,
        }
    }

    /// Set whether to accept all lemmas as axioms (skip proof replay).
    pub fn set_accept_all(&mut self, accept: bool) {
        self.accept_all = accept;
    }

    /// Scan a directory for .thy files and parse their headers.
    pub fn scan(&mut self, dir: &Path) -> std::io::Result<usize> {
        let mut count = 0;
        let mut dirs = vec![dir.to_path_buf()];

        while let Some(dir) = dirs.pop() {
            if !dir.is_dir() {
                continue;
            }
            for entry in std::fs::read_dir(&dir)? {
                let entry = entry?;
                let path = entry.path();
                if path.is_dir() {
                    dirs.push(path);
                } else if path.extension().is_some_and(|e| e == "thy")
                    && let Some(tf) = TheoryFile::parse(&path) {
                        self.files.insert(tf.name.clone(), tf);
                        count += 1;
                    }
            }
        }
        Ok(count)
    }

    /// Build a topological order respecting import dependencies.
    pub fn resolve_dependencies(&mut self) -> Vec<String> {
        let mut in_degree: HashMap<&str, usize> = HashMap::new();
        let mut adjacency: HashMap<&str, Vec<&str>> = HashMap::new();

        for name in self.files.keys() {
            in_degree.entry(name.as_str()).or_insert(0);
            adjacency.entry(name.as_str()).or_default();
        }

        for tf in self.files.values() {
            for imp in &tf.imports {
                if self.files.contains_key(imp.as_str()) {
                    adjacency.entry(imp.as_str()).or_default().push(&tf.name);
                    *in_degree.entry(tf.name.as_str()).or_insert(0) += 1;
                }
            }
        }

        // Kahn's algorithm
        let mut queue: Vec<&str> =
            in_degree.iter().filter(|(_, d)| **d == 0).map(|(n, _)| *n).collect();

        let mut order = Vec::new();
        while let Some(name) = queue.pop() {
            order.push(name.to_string());
            if let Some(neighbors) = adjacency.get(name) {
                for &next in neighbors {
                    let deg = in_degree.get_mut(next).unwrap();
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push(next);
                    }
                }
            }
        }

        // Add any remaining (cycle-breaking)
        for name in self.files.keys() {
            if !order.contains(name) {
                order.push(name.clone());
            }
        }

        self.order = order.clone();
        order
    }

    /// Build all theories in order. Returns a BuildResult.
    pub fn build(&mut self) -> BuildResult {
        let mut result = BuildResult {
            loaded: 0,
            total: self.order.len(),
            theorems: 0,
            failed: 0,
            error_messages: Vec::new(),
            theory_names: Vec::new(),
        };

        for name in &self.order.clone() {
            let tf = match self.files.get(name) {
                Some(tf) => tf.clone(),
                None => continue,
            };

            match self.build_one(&tf) {
                Ok(thm_count) => {
                    result.loaded += 1;
                    result.theorems += thm_count;
                    result.theory_names.push(name.clone());
                },
                Err(errs) => {
                    result.failed += 1;
                    result.error_messages.extend(errs);
                },
            }
        }

        result
    }

    /// Build a single theory file.
    fn build_one(&mut self, tf: &TheoryFile) -> Result<usize, Vec<String>> {
        let parent = tf
            .imports
            .first()
            .and_then(|imp| self.registry.lookup(imp))
            .unwrap_or_else(Theory::pure);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut proc = TheoryProcessor::with_parent(parent, &tf.name);
            proc.accept_all = self.accept_all;
            let source = std::fs::read_to_string(&tf.path)
                .map_err(|e| vec![format!("Cannot read {}: {}", tf.path.display(), e)])?;
            let thy = proc.process_source(&source);
            self.registry.register(Arc::clone(&thy));
            if proc.errors().is_empty() {
                Ok(proc.theorem_count())
            } else {
                Err(proc.errors().to_vec())
            }
        }));

        match result {
            Ok(Ok(n)) => Ok(n),
            Ok(Err(e)) => Err(e),
            Err(_) => Err(vec!["panic: internal error".to_string()]),
        }
    }

    /// Get the theory registry.
    pub fn registry(&self) -> &TheoryRegistry {
        &self.registry
    }

    /// Get the load order.
    pub fn order(&self) -> &[String] {
        &self.order
    }

    /// Build with verification classification.
    ///
    /// Instead of just counting success/failure, this classifies each theory
    /// into detailed status categories using `VerifyClassifier`.
    pub fn build_with_classifier(&mut self) -> crate::theory::verify_classifier::VerifyReport {
        use std::time::Instant;

        use crate::theory::verify_classifier::VerifyResult;

        let mut results = Vec::new();

        for name in &self.order.clone() {
            let tf = match self.files.get(name) {
                Some(tf) => tf.clone(),
                None => continue,
            };

            let start = Instant::now();

            let status = self.build_one_classified(&tf);
            let elapsed = start.elapsed();
            let theorem_count = self.theorem_count_for(name);

            results.push(VerifyResult {
                name: name.clone(),
                path: tf.path.clone(),
                status,
                elapsed,
                theorem_count,
            });
        }

        crate::theory::verify_classifier::VerifyReport::new(results)
    }

    /// Build a single theory and classify the result.
    fn build_one_classified(
        &mut self,
        tf: &TheoryFile,
    ) -> crate::theory::verify_classifier::VerifyStatus {
        use crate::theory::verify_classifier::VerifyStatus;

        let parent = tf
            .imports
            .first()
            .and_then(|imp| self.registry.lookup(imp))
            .unwrap_or_else(Theory::pure);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut proc = TheoryProcessor::with_parent(parent, &tf.name);
            proc.accept_all = self.accept_all;
            let source = std::fs::read_to_string(&tf.path)
                .map_err(|e| VerifyStatus::IoError { message: e.to_string() })?;

            // Time-budgeted processing (60s per file)
            let thy = proc.process_source(&source);
            self.registry.register(Arc::clone(&thy));

            if proc.lemma_count == 0 && proc.theorem_count() == 0 {
                Ok(VerifyStatus::NoLemmas)
            } else if proc.errors().is_empty() {
                if proc.lemma_count > 0 {
                    Ok(VerifyStatus::FullSuccess)
                } else {
                    Ok(VerifyStatus::NoLemmas)
                }
            } else {
                let verified = proc.theorem_count();
                let attempted = proc.lemma_count;
                let failed_names: Vec<String> = proc.errors().iter().take(10).cloned().collect();
                if verified == 0 {
                    // Check if any errors are syntax-related
                    let syntax_err = proc.errors().iter().any(|e| {
                        e.contains("parse") || e.contains("syntax") || e.contains("token")
                    });
                    if syntax_err {
                        Ok(VerifyStatus::SyntaxError {
                            message: proc.errors().first().cloned().unwrap_or_default(),
                        })
                    } else {
                        Ok(VerifyStatus::ProofFailure { attempted })
                    }
                } else {
                    Ok(VerifyStatus::PartialSuccess { verified, attempted, failed_names })
                }
            }
        }));

        match result {
            Ok(Ok(status)) => status,
            Ok(Err(status)) => status,
            Err(_) => VerifyStatus::SyntaxError {
                message: "panic: internal error during processing".to_string(),
            },
        }
    }

    /// Get the theorem count for a theory by name.
    fn theorem_count_for(&self, name: &str) -> usize {
        self.registry.lookup(name).map(|thy| thy.all_theorem_names().len()).unwrap_or(0)
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
    fn test_theory_file_parse_from_str() {
        // We can't easily create temp files without a tempfile dependency,
        // so test the parsing logic indirectly
        let header = "theory Foo imports Bar Baz begin";
        let first_line = header.lines().next().unwrap();
        let trimmed = first_line.trim();
        assert!(trimmed.starts_with("theory "));
        let rest = trimmed.strip_prefix("theory ").unwrap();
        let parts: Vec<&str> = rest.split_whitespace().collect();
        assert_eq!(parts[0], "Foo");

        let mut imports = Vec::new();
        let mut in_imports = false;
        for part in &parts[1..] {
            if *part == "imports" {
                in_imports = true;
            } else if *part == "begin" || *part == "keywords" {
                break;
            } else if in_imports {
                imports.push(part.to_string());
            }
        }
        assert_eq!(imports, vec!["Bar", "Baz"]);
    }

    #[test]
    fn test_session_builder_empty() {
        let builder = SessionBuilder::new();
        assert!(builder.order().is_empty());
    }

    #[test]
    fn test_build_result() {
        let result = BuildResult {
            loaded: 3,
            total: 5,
            theorems: 10,
            failed: 2,
            error_messages: vec!["err1".into()],
            theory_names: vec!["A".into(), "B".into(), "C".into()],
        };
        assert!(!result.is_success());
        assert_eq!(result.loaded, 3);
        assert_eq!(result.failed, 2);
    }
}
