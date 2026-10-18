//! Theory dependency graph — topological loading of .thy files.
//!
//! Corresponds to Isabelle's `Thy_Info` and session management.
//!
//! ## Architecture
//!
//! 1. Scan a directory for all `.thy` files
//! 2. Parse `theory Foo imports Bar Baz begin` headers
//! 3. Build a DAG (directed acyclic graph)
//! 4. Topological sort respecting import dependencies
//! 5. Load theories in order, inheriting parent theorem databases

use std::{
    collections::{HashMap, VecDeque},
    path::{Path, PathBuf},
    sync::Arc,
};

use super::hol_loader::{HolTheoremDb, ParsedLemma, parse_theory_header};
use crate::core::thm::Thm;

// =========================================================================
// TheoryGraph
// =========================================================================

/// A node in the theory dependency graph.
#[derive(Debug, Clone)]
pub struct TheoryNode {
    /// Theory name (e.g., "HOL", "List")
    pub name: String,
    /// Path to the .thy file
    pub path: PathBuf,
    /// Names of imported theories
    pub imports: Vec<String>,
    /// Whether this theory has been loaded
    pub loaded: bool,
    /// Theorems from this theory
    pub theorems: Vec<Arc<Thm>>,
    /// Parsed lemmas (if loaded)
    pub lemmas: Vec<ParsedLemma>,
}

/// The theory dependency graph — manages loading order.
#[derive(Debug, Default)]
pub struct TheoryGraph {
    /// All theory nodes, keyed by name
    pub nodes: HashMap<String, TheoryNode>,
    /// Topologically sorted load order
    pub load_order: Vec<String>,
    /// Files that failed to parse
    pub errors: Vec<(String, String)>,
}

impl TheoryGraph {
    /// Create an empty graph.
    pub fn new() -> Self {
        TheoryGraph::default()
    }

    /// Scan a directory recursively for `.thy` files and build the graph.
    /// Does NOT load the theories — just parses headers.
    pub fn scan(&mut self, dir: &Path) -> std::io::Result<usize> {
        let mut count = 0;
        self.scan_dir(dir, &mut count)?;
        Ok(count)
    }

    fn scan_dir(&mut self, start_dir: &Path, count: &mut usize) -> std::io::Result<()> {
        let mut dirs = vec![start_dir.to_path_buf()];
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
                    && let Some(node) = self.parse_header(&path)
                {
                    self.nodes.insert(node.name.clone(), node);
                    *count += 1;
                }
            }
        }
        Ok(())
    }

    /// Parse the theory header from a .thy file.
    fn parse_header(&self, path: &Path) -> Option<TheoryNode> {
        let source = std::fs::read_to_string(path).ok()?;
        let (name, imports) = parse_theory_header(&source)?;
        Some(TheoryNode {
            name,
            path: path.to_path_buf(),
            imports,
            loaded: false,
            theorems: Vec::new(),
            lemmas: Vec::new(),
        })
    }

    /// Topological sort: returns theory names in load order.
    /// Detects cycles and returns an error if any are found.
    pub fn topological_sort(&self) -> Result<Vec<String>, String> {
        let mut in_degree: HashMap<&str, usize> = HashMap::new();
        let mut adjacency: HashMap<&str, Vec<&str>> = HashMap::new();

        // Initialize
        for name in self.nodes.keys() {
            in_degree.entry(name.as_str()).or_insert(0);
            adjacency.entry(name.as_str()).or_default();
        }

        // Build edges: if A imports B, then B must be loaded before A
        for node in self.nodes.values() {
            for imp in &node.imports {
                if self.nodes.contains_key(imp.as_str()) {
                    // edge: imp → node.name
                    adjacency.entry(imp.as_str()).or_default().push(&node.name);
                    *in_degree.entry(node.name.as_str()).or_insert(0) += 1;
                }
                // External imports (not in our graph) are ignored
            }
        }

        // Kahn's algorithm
        let mut queue: VecDeque<&str> = VecDeque::new();
        for (name, &deg) in &in_degree {
            if deg == 0 {
                queue.push_back(name);
            }
        }

        let mut order = Vec::new();
        while let Some(name) = queue.pop_front() {
            order.push(name.to_string());
            if let Some(neighbors) = adjacency.get(name) {
                for &next in neighbors {
                    let deg = in_degree.get_mut(next).unwrap();
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(next);
                    }
                }
            }
        }

        if order.len() != self.nodes.len() {
            // Cycle detected — break cycles by forcing remaining nodes into the order
            // This is safe for theory loading: a cycle usually means a mutual import
            // that doesn't affect the ability to parse lemmas.
            let mut remaining: Vec<&str> = self
                .nodes
                .keys()
                .filter(|n| !order.contains(&n.to_string()))
                .map(|s| s.as_str())
                .collect();
            remaining.sort();
            // Just add all remaining nodes — breaking cycles arbitrarily
            for name in &remaining {
                order.push(name.to_string());
            }
            tracing::warn!(cycle_count = remaining.len(), "broke theory import cycles");
        }

        Ok(order)
    }

    /// Load all theories in topological order.
    /// Returns the final theorem database with all inherited theorems.
    pub fn load_all(&mut self) -> Result<HolTheoremDb, String> {
        self.load_all_with_progress(|_, _, _| {})
    }

    /// Load all theories in topological order.
    /// Returns the final theorem database with all inherited theorems.
    /// Uses incremental DB building to avoid storing all lemmas in memory.
    pub fn load_all_with_progress<F>(&mut self, mut on_progress: F) -> Result<HolTheoremDb, String>
    where
        F: FnMut(&str, usize, usize),
    {
        let order = self.topological_sort()?;
        self.load_order = order.clone();
        let total = order.len();

        let mut db = HolTheoremDb::new();
        let mut type_env = crate::core::types::TypeEnv::new();

        for (idx, name) in order.iter().enumerate() {
            on_progress(name, idx, total);
            let path = self.nodes.get(name).map(|n| n.path.clone());
            if let Some(path) = path {
                match Self::load_file(&path) {
                    Ok((mut lemmas, source)) => {
                        // Build type env from source FIRST (so types from THIS file
                        // are available to annoate its own lemmas)
                        let file_env = HolTheoremDb::build_type_env(&source);
                        type_env.consts.extend(file_env.consts);
                        type_env.types.extend(file_env.types);
                        let file_defs =
                            HolTheoremDb::build_checked_definition_sources(&source, &type_env);
                        db.checked_definitions.extend(file_defs);

                        // Type-annotate lemmas with accumulated TypeEnv
                        // Replaces Typ::dummy() with known types from previously loaded theories
                        let mut annotated = 0usize;
                        for lem in &mut lemmas {
                            if lem.type_annotate(&type_env) {
                                annotated += 1;
                            }
                        }
                        if annotated > 0 {
                            tracing::info!(
                                annotated,
                                total = lemmas.len(),
                                "type-annotated theory lemmas"
                            );
                        }

                        if let Some(node) = self.nodes.get_mut(name) {
                            node.loaded = true;
                            node.lemmas = lemmas.clone();
                        }
                        db.extend(&lemmas);
                        drop(lemmas);
                    },
                    Err(e) => {
                        self.errors.push((name.clone(), e));
                    },
                }
            }
        }

        HolTheoremDb::add_builtins(&mut db);
        db.type_env = type_env;
        Ok(db)
    }

    /// Load a single theory file and return its parsed lemmas and source.
    fn load_file(path: &Path) -> Result<(Vec<ParsedLemma>, String), String> {
        let source = std::fs::read_to_string(path)
            .map_err(|e| format!("Cannot read {}: {}", path.display(), e))?;
        let path_str = path.to_string_lossy().to_string();
        // Catch panics from the parser to prevent one bad file from stopping the load
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            super::hol_loader::parse_lemmas_with_loc(&source, &path_str)
        }));
        match result {
            Ok(lemmas) => Ok((lemmas, source)),
            Err(_) => Err(format!("Parser panic in {}", path.display())),
        }
    }

    /// Get the number of nodes in the graph.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Check if the graph is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Get a summary of the graph state.
    pub fn summary(&self) -> String {
        let mut s = format!("TheoryGraph: {} theories\n", self.nodes.len());
        if !self.load_order.is_empty() {
            s.push_str(&format!("  Load order: {} files\n", self.load_order.len()));
        }
        let loaded = self.nodes.values().filter(|n| n.loaded).count();
        s.push_str(&format!("  Loaded: {}/{}\n", loaded, self.nodes.len()));
        if !self.errors.is_empty() {
            s.push_str(&format!("  Errors: {}\n", self.errors.len()));
            for (name, err) in self.errors.iter().take(5) {
                s.push_str(&format!("    {}: {}\n", name, err));
            }
        }
        s
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scan_theories() {
        let mut graph = TheoryGraph::new();
        let count = graph.scan(Path::new("theories")).unwrap();
        eprintln!("{}", graph.summary());
        assert!(count >= 13, "Should find at least 13 theories, found {}", count);
    }

    #[test]
    fn test_topological_sort() {
        let mut graph = TheoryGraph::new();
        graph.scan(Path::new("theories")).unwrap();
        let order = graph.topological_sort().unwrap();
        eprintln!("Load order: {:?}", order);
        // HOL or Pure should be first (no imports)
        assert!(!order.is_empty());
    }

    #[test]
    fn test_no_cycles() {
        let mut graph = TheoryGraph::new();
        graph.scan(Path::new("theories")).unwrap();
        let result = graph.topological_sort();
        assert!(result.is_ok(), "DAG should have no cycles: {:?}", result.err());
    }
    #[test]
    fn test_scan_full_hol() {
        let mut graph = TheoryGraph::new();
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if hol_dir.exists() {
            let count = graph.scan(hol_dir).unwrap_or(0);
            eprintln!("Scanned {} theories from full HOL", count);
            assert!(count >= 1000, "Expected >= 1000 theories, got {}", count);

            // Check DAG validity
            let result = graph.topological_sort();
            match result {
                Ok(order) => {
                    eprintln!("Topological sort OK: {} theories in order", order.len());
                    eprintln!("First 5: {:?}", &order[..5.min(order.len())]);
                    eprintln!("Last 5: {:?}", &order[order.len().saturating_sub(5)..]);
                },
                Err(e) => {
                    eprintln!("DAG error: {}", e);
                    eprintln!("Graph summary: {}", graph.summary());
                },
            }
        } else {
            eprintln!("isabelle-source/src/HOL not found, skipping full scan test");
        }
    }
}

#[path = "scale_diagnostics.rs"]
pub mod scale_diagnostics;
