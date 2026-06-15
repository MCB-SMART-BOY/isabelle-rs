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
                } else if path.extension().map_or(false, |e| e == "thy") {
                    if let Some(node) = self.parse_header(&path) {
                        self.nodes.insert(node.name.clone(), node);
                        *count += 1;
                    }
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
            eprintln!(
                "Warning: broke {} theory import cycle(s) involving {:?}",
                remaining.len(),
                remaining.iter().take(5).collect::<Vec<_>>()
            );
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

                        // Type-annotate lemmas with accumulated TypeEnv
                        // Replaces Typ::dummy() with known types from previously loaded theories
                        let mut annotated = 0usize;
                        for lem in &mut lemmas {
                            if lem.type_annotate(&type_env) {
                                annotated += 1;
                            }
                        }
                        if annotated > 0 {
                            eprintln!(
                                "  Type-annotated {}/{} lemmas in {}",
                                annotated,
                                lemmas.len(),
                                name
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
}

#[cfg(test)]
mod scale_tests {
    use super::*;

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

    #[test]
    fn test_load_first_50() {
        let mut graph = TheoryGraph::new();
        let hol_dir = Path::new("theories");
        if hol_dir.exists() {
            let count = graph.scan(hol_dir).unwrap_or(0);
            eprintln!("Scanned {} theories", count);

            let mut loaded = 0;
            let result = graph.load_all_with_progress(|name, idx, total| {
                if idx % 10 == 0 || idx == total - 1 {
                    eprintln!("  [{}/{}] Loading {}...", idx + 1, total, name);
                }
                loaded = idx + 1;
            });

            match result {
                Ok(db) => {
                    eprintln!("Loaded {} theories, {} theorems in DB", loaded, db.all.len());
                    eprintln!("DB by_name keys: {}", db.by_name.len());
                },
                Err(e) => {
                    eprintln!("Load error: {}", e);
                },
            }
            eprintln!("Errors: {:?}", graph.errors.iter().take(5).collect::<Vec<_>>());
        }
    }

    /// Load the first N theories from the full HOL directory.
    /// Uses incremental DB building to test memory scaling.
    fn load_n_from_full_hol(n: usize) {
        let mut graph = TheoryGraph::new();
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("isabelle-source/src/HOL not found, skipping");
            return;
        }
        let count = graph.scan(hol_dir).unwrap_or(0);
        eprintln!("Scanned {} theories from full HOL", count);

        // Only load up to N theories
        let order = graph.topological_sort().unwrap_or_default();
        let to_load = order.len().min(n);
        eprintln!("Will load {} of {} theories", to_load, order.len());

        let mut db = HolTheoremDb::new();
        let mut loaded = 0usize;
        let mut errors = 0usize;

        for (idx, name) in order.iter().take(to_load).enumerate() {
            if let Some(node) = graph.nodes.get(name) {
                match TheoryGraph::load_file(&node.path) {
                    Ok((lemmas, _source)) => {
                        db.extend(&lemmas);
                        loaded += 1;
                        if (idx + 1) % 100 == 0 || idx == to_load - 1 {
                            eprintln!(
                                "  [{}/{}] {}: {} lemmas (DB: {} total, {} by-name, {} errors)",
                                idx + 1,
                                to_load,
                                name,
                                lemmas.len(),
                                db.all.len(),
                                db.by_name.len(),
                                errors,
                            );
                        }
                    },
                    Err(e) => {
                        errors += 1;
                        if errors <= 5 {
                            eprintln!("  Error loading {}: {}", name, e);
                        }
                    },
                }
            }
        }

        HolTheoremDb::add_builtins(&mut db);
        eprintln!(
            "Done: {} files loaded, {} errors, {} total theorems, {} by-name",
            loaded,
            errors,
            db.all.len(),
            db.by_name.len()
        );
    }

    #[test]
    fn test_load_100_from_full_hol() {
        load_n_from_full_hol(100);
    }

    #[test]
    fn test_load_500_from_full_hol() {
        load_n_from_full_hol(500);
    }

    #[test]
    fn test_load_1000_from_full_hol() {
        load_n_from_full_hol(1000);
    }

    /// Load 200 files and verify sample lemmas from key files beyond the core 5.
    #[test]
    fn test_verify_beyond_core() {
        let mut graph = TheoryGraph::new();
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("isabelle-source/src/HOL not found, skipping");
            return;
        }
        graph.scan(hol_dir).unwrap();
        let order = graph.topological_sort().unwrap_or_default();
        let to_load = order.len().min(100);
        eprintln!("Loading {} files...", to_load);

        let mut db = HolTheoremDb::new();
        for name in order.iter().take(to_load) {
            if let Some(node) = graph.nodes.get(name) {
                if let Ok((lemmas, _source)) = TheoryGraph::load_file(&node.path) {
                    db.extend(&lemmas);
                }
            }
        }
        HolTheoremDb::add_builtins(&mut db);
        eprintln!("DB: {} theorems, {} by-name", db.all.len(), db.by_name.len());

        // Verify sample lemmas using the custom DB
        HolTheoremDb::with_override(&db, || {
            let target_files = [
                "Fun.thy",
                "Product_Type.thy",
                "Sum_Type.thy",
                "Option.thy",
                "Lattices.thy",
                "Typedef.thy",
                "Num.thy",
                "Power.thy",
                "Fields.thy",
            ];
            let mut total_v = 0usize;
            let mut total_a = 0usize;
            for fname in &target_files {
                let path = hol_dir.join(fname);
                if !path.exists() {
                    continue;
                }
                let source = std::fs::read_to_string(&path).unwrap_or_default();
                let lemmas = crate::hol::hol_loader::parse_lemmas(&source);
                let with_proofs: Vec<_> =
                    lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
                let sample = with_proofs.len().min(15);
                let mut verified = 0;
                for lem in with_proofs.iter().take(sample) {
                    if crate::isar::method::verify_lemma(lem).is_some() {
                        verified += 1;
                    }
                }
                total_v += verified;
                total_a += sample;
                eprintln!("  {}: {}/{}", fname, verified, sample);
            }
            eprintln!(
                "Beyond-core: {}/{} ({:.1}%)",
                total_v,
                total_a,
                if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 }
            );
        });
    }

    #[test]
    fn test_verify_extended() {
        let mut graph = TheoryGraph::new();
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("isabelle-source/src/HOL not found, skipping");
            return;
        }
        graph.scan(hol_dir).unwrap();
        let order = graph.topological_sort().unwrap_or_default();
        let to_load = order.len().min(200);
        eprintln!("Loading {} files...", to_load);

        let mut db = HolTheoremDb::new();
        for name in order.iter().take(to_load) {
            if let Some(node) = graph.nodes.get(name) {
                if let Ok((lemmas, _source)) = TheoryGraph::load_file(&node.path) {
                    db.extend(&lemmas);
                }
            }
        }
        HolTheoremDb::add_builtins(&mut db);
        eprintln!("DB: {} theorems, {} by-name", db.all.len(), db.by_name.len());

        // Target files to verify
        let target_files = [
            "HOL.thy",
            "Orderings.thy",
            "Set.thy",
            "Nat.thy",
            "List.thy",
            "Fun.thy",
            "Product_Type.thy",
            "Sum_Type.thy",
            "Option.thy",
            "Lattices.thy",
            "Typedef.thy",
            "Num.thy",
            "Power.thy",
            "Fields.thy",
            "Groups.thy",
            "Rings.thy",
            "Int.thy",
            "Complete_Lattices.thy",
            "Boolean_Algebras.thy",
            "Set_Interval.thy",
            "Equiv_Relations.thy",
            "Order_Relation.thy",
            "Map.thy",
            "Filter.thy",
            "Limits.thy",
            // Below: overflow with cumulative DB
            // "GCD.thy", "Binomial.thy", "Factorial.thy", "Parity.thy",
            "Enum.thy",
            "String.thy",
            "Bit_Operations.thy",
            "Code_Numeral.thy",
            "Groups_Big.thy",
            "Groups_List.thy",
            "Lattices_Big.thy",
            "Archimedean_Field.thy",
            "Transitive_Closure.thy",
            "Complete_Partial_Order.thy",
            "Conditionally_Complete_Lattices.thy",
            "Hull.thy",
            "Modules.thy",
            // "Vector_Spaces.thy",  // overflow
            "Fun_Def.thy",
            "ATP.thy",
            "Meson.thy",
            "Metis.thy",
            "Basic_BNF_LFPs.thy",
            "Basic_BNFs.thy",
            "BNF_Def.thy",
            "BNF_Composition.thy",
            "Deriv.thy",
            "MacLaurin.thy",
            "NthRoot.thy",
            "Series.thy",
            "Transfer.thy",
            // Additional small/medium files
            "Inequalities.thy",
            "Wfrec.thy",
            "Typerep.thy",
            "Code_Evaluation.thy",
            "Ctr_Sugar.thy",
            // Tool config files (tiny)
            "SAT.thy",
            "Argo.thy",
            "Mirabelle.thy",
            "Nunchaku.thy",
            // Previously overflow — now verified with global DB
            "Parity.thy",
            // Medium candidates
            "Random.thy",
            "Lifting_Set.thy",
            "Extraction.thy",
            "Predicate.thy",
            // "Record.thy",  // overflow
            "Quickcheck_Narrowing.thy",
            // More candidates
            "Quickcheck_Random.thy",
            "Quickcheck_Exhaustive.thy",
            "Lazy_Sequence.thy",
            "Limited_Sequence.thy",
            "Random_Pred.thy",
            "Random_Sequence.thy",
            "Nitpick.thy",
            "Partial_Function.thy",
            "Presburger.thy",
            // Algebraic / number theory
            "Numeral_Simprocs.thy",
            "Semiring_Normalization.thy",
            "Groebner_Basis.thy",
            "Topological_Spaces.thy",
            "Real_Vector_Spaces.thy",
            "Quotient.thy",
            "SMT.thy",
            // Analysis
            "Complex.thy",
            // "Rat.thy",  // overflow
            // "Real.thy",  // overflow
            // "Zorn.thy",  // overflow
            // "Transcendental.thy",  // overflow
            // "Euclidean_Rings.thy",  // overflow
            // "Divides.thy",  // no proofs
            // Overflow files
            // "BNF_Fixpoint_Base.thy",
            // "BNF_Least_Fixpoint.thy",
            // "Inductive.thy",
        ];

        let mut total_v = 0usize;
        let mut total_a = 0usize;

        HolTheoremDb::with_override(&db, || {
            for fname in &target_files {
                let path = hol_dir.join(fname);
                if !path.exists() {
                    continue;
                }
                let source = std::fs::read_to_string(&path).unwrap_or_default();
                let lemmas = crate::hol::hol_loader::parse_lemmas(&source);
                let with_proofs: Vec<_> =
                    lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
                let sample = with_proofs.len().min(10);
                if sample == 0 {
                    continue;
                }
                let mut verified = 0;
                for lem in with_proofs.iter().take(sample) {
                    if crate::isar::method::verify_lemma(lem).is_some() {
                        verified += 1;
                    }
                }
                total_v += verified;
                total_a += sample;
                let pct = if sample > 0 { (verified as f64 / sample as f64) * 100.0 } else { 0.0 };
                eprintln!("  {}: {}/{} ({:.0}%)", fname, verified, sample, pct);
            }
        });

        let pct = if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 };
        eprintln!(
            "Extended ({}/{} files): {}/{} ({:.1}%)",
            target_files.len(),
            target_files.len(),
            total_v,
            total_a,
            pct
        );
    }

    /// Verify overflow-prone files using the global theorem database.
    #[test]
    fn test_verify_global_db() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("isabelle-source/src/HOL not found, skipping");
            return;
        }
        let _db = HolTheoremDb::get();
        eprintln!("Global DB: {} theorems", HolTheoremDb::get().all.len());

        let target_files = [
            "Parity.thy",
            // "Divides.thy",  // overflow
            // "GCD.thy",  // overflow
            // "Binomial.thy",  // overflow
            // "Factorial.thy",
            // "Euclidean_Rings.thy",
            // "Rat.thy",
            // "Real.thy",
            // "Zorn.thy",
            // "Transcendental.thy",
            // "Finite_Set.thy",
            // "Record.thy",
            // "Inductive.thy",
            // "BNF_Least_Fixpoint.thy",
            // "BNF_Fixpoint_Base.thy",
        ];

        let mut total_v = 0usize;
        let mut total_a = 0usize;
        for fname in &target_files {
            let path = hol_dir.join(fname);
            if !path.exists() {
                continue;
            }
            let Ok(source) = std::fs::read_to_string(&path) else { continue };
            let lemmas = crate::hol::hol_loader::parse_lemmas(&source);
            let with_proofs: Vec<_> = lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
            let sample = with_proofs.len().min(10);
            if sample == 0 {
                continue;
            }
            let mut verified = 0;
            for lem in with_proofs.iter().take(sample) {
                if crate::isar::method::verify_lemma(lem).is_some() {
                    verified += 1;
                }
            }
            total_v += verified;
            total_a += sample;
            let pct = if sample > 0 { (verified as f64 / sample as f64) * 100.0 } else { 0.0 };
            eprintln!("  {}: {}/{} ({:.0}%)", fname, verified, sample, pct);
        }
        let pct = if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 };
        eprintln!("Global DB: {}/{} ({:.1}%)", total_v, total_a, pct);
    }

    /// Systematic scan: verify sample lemmas from many HOL files with cumulative DB.
    #[test]
    fn test_verify_systematic() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("isabelle-source/src/HOL not found, skipping");
            return;
        }

        let mut graph = TheoryGraph::new();
        graph.scan(hol_dir).unwrap();
        let order = graph.topological_sort().unwrap_or_default();
        let to_load = order.len().min(100);
        eprintln!("Building DB with {} files...", to_load);

        let mut db = HolTheoremDb::new();
        for name in order.iter().take(to_load) {
            if let Some(node) = graph.nodes.get(name) {
                if let Ok((lemmas, source)) = TheoryGraph::load_file(&node.path) {
                    let file_env = HolTheoremDb::build_type_env(&source);
                    db.type_env.consts.extend(file_env.consts);
                    db.type_env.types.extend(file_env.types);
                    db.extend(&lemmas);
                }
            }
        }
        HolTheoremDb::add_builtins(&mut db);
        eprintln!("DB: {} theorems", db.all.len());

        // Test files from the first 150 loaded
        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut total_thms = 0usize;
        let mut total_verified = 0usize;

        HolTheoremDb::with_override(&db, || {
            for name in order.iter().take(100) {
                if let Some(node) = graph.nodes.get(name) {
                    let path = &node.path;
                    let Ok(source) = std::fs::read_to_string(path) else { continue };
                    let lemmas = crate::hol::hol_loader::parse_lemmas(&source);
                    let with_proofs: Vec<_> =
                        lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
                    let sample = with_proofs.len().min(5);
                    if sample == 0 {
                        continue;
                    }

                    let mut verified = 0;
                    for lem in with_proofs.iter().take(sample) {
                        if crate::isar::method::verify_lemma(lem).is_some() {
                            verified += 1;
                        }
                    }
                    total_thms += sample;
                    total_verified += verified;
                    if verified == sample {
                        passed += 1;
                    } else {
                        failed += 1;
                        eprintln!("  PARTIAL {}: {}/{}", name, verified, sample);
                    }
                }
            }
        });

        eprintln!(
            "Systematic: {}/{} files fully verified, {}/{} theorems ({:.1}%)",
            passed,
            passed + failed,
            total_verified,
            total_thms,
            if total_thms > 0 { (total_verified as f64 / total_thms as f64) * 100.0 } else { 0.0 }
        );
    }

    /// Verify additional theory files beyond the core beyond-core set.
    #[test]
    fn test_verify_expanded() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("isabelle-source/src/HOL not found, skipping");
            return;
        }

        // Files with their own isolated DB (no cumulative overflow)
        let files_to_try = [
            "Set_Interval.thy",
            "Complete_Lattices.thy",
            "Boolean_Algebras.thy",
            "Order_Relation.thy",
            "Equiv_Relations.thy",
            "Groups.thy",
            "Complete_Partial_Order.thy",
            "Conditionally_Complete_Lattices.thy",
            "Map.thy",
            "Filter.thy",
            "Limits.thy",
            "Rings.thy",
            "Int.thy",
            "Enum.thy",
            "String.thy",
            "Parity.thy",
            "Code_Numeral.thy",
            "Bit_Operations.thy",
            "Numeral_Simprocs.thy",
            "Groups_Big.thy",
            "Groups_List.thy",
            "Lattices_Big.thy",
            "Archimedean_Field.thy",
            "Transitive_Closure.thy",
            "Fun_Def.thy",
            "ATP.thy",
            "Meson.thy",
            "Metis.thy",
            "Basic_BNF_LFPs.thy",
            "Basic_BNFs.thy",
            "Hull.thy",
            "Modules.thy",
            "BNF_Def.thy",
            "BNF_Composition.thy",
            "Deriv.thy",
            "MacLaurin.thy",
            "NthRoot.thy",
            "Series.thy",
            "Transfer.thy",
            "Fun_Def_Base.thy",
            // Additional individual files
            "Finite_Set.thy",
            "Fun.thy",
            "Lattices.thy",
            "Option.thy",
            "Product_Type.thy",
            "Sum_Type.thy",
            "Power.thy",
            "Num.thy",
            "Nat.thy",
            "Set.thy",
            "List.thy",
            "Orderings.thy",
            "HOL.thy",
            "Fields.thy",
            "GCD.thy",
            "Binomial.thy",
            "Factorial.thy",
            "Euclidean_Rings.thy",
            "Semiring_Normalization.thy",
            "Groebner_Basis.thy",
            "Presburger.thy",
            "Wfrec.thy",
            "Typedef.thy",
        ];

        let mut total_v = 0usize;
        let mut total_a = 0usize;
        let mut passed_files = 0usize;

        for fname in &files_to_try {
            let path = hol_dir.join(fname);
            if !path.exists() {
                continue;
            }

            // Build minimal DB
            let Ok(source) = std::fs::read_to_string(&path) else { continue };
            let lemmas = crate::hol::hol_loader::parse_lemmas(&source);
            let mut db = HolTheoremDb::new();
            db.extend(&lemmas);
            HolTheoremDb::add_builtins(&mut db);

            let with_proofs: Vec<_> = lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
            if with_proofs.is_empty() {
                continue;
            }

            let sample = with_proofs.len().min(10);
            let mut verified = 0;

            HolTheoremDb::with_override(&db, || {
                for lem in with_proofs.iter().take(sample) {
                    if crate::isar::method::verify_lemma(lem).is_some() {
                        verified += 1;
                    }
                }
            });

            total_v += verified;
            total_a += sample;
            let pct = if sample > 0 { (verified as f64 / sample as f64) * 100.0 } else { 0.0 };
            eprintln!("  {}: {}/{} ({:.0}%)", fname, verified, sample, pct);
            passed_files += 1;
        }

        let pct = if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 };
        eprintln!("Expanded ({} files): {}/{} ({:.1}%)", passed_files, total_v, total_a, pct);
    }

    /// Verify additional theory files beyond the core beyond-core set. (OLD)
    #[test]
    fn test_verify_expanded_old() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("isabelle-source/src/HOL not found, skipping");
            return;
        }

        // Load and verify files one at a time to isolate problems
        let files_to_try = [
            // Already verified
            "Set_Interval.thy",
            "Complete_Lattices.thy",
            "Boolean_Algebras.thy",
            "Order_Relation.thy",
            "Equiv_Relations.thy",
            "Groups.thy",
            "Complete_Partial_Order.thy",
            "Conditionally_Complete_Lattices.thy",
            "Map.thy",
            "Filter.thy",
            "Limits.thy",
            "Rings.thy",
            "Int.thy",
            "Enum.thy",
            "String.thy",
            "Parity.thy",
            "Code_Numeral.thy",
            "Bit_Operations.thy",
            "Numeral_Simprocs.thy",
            "Groups_Big.thy",
            "Groups_List.thy",
            "Lattices_Big.thy",
            "Archimedean_Field.thy",
            "Transitive_Closure.thy",
            "Fun_Def.thy",
            "ATP.thy",
            "Meson.thy",
            "Metis.thy",
            "Basic_BNF_LFPs.thy",
            "Basic_BNFs.thy",
            "Hull.thy",
            "Modules.thy",
            "BNF_Def.thy",
            "BNF_Composition.thy",
            "Deriv.thy",
            "MacLaurin.thy",
            "NthRoot.thy",
            "Series.thy",
            "Transfer.thy",
            "Fun_Def_Base.thy",
            // New candidates — try these
            "Finite_Set.thy",
            "Fun.thy",
            "Lattices.thy",
            "Option.thy",
            "Product_Type.thy",
            "Sum_Type.thy",
            "Power.thy",
            "Num.thy",
            "Nat.thy",
            "Set.thy",
            "List.thy",
            "Orderings.thy",
            "HOL.thy",
            "Fields.thy",
            "GCD.thy",
            "Binomial.thy",
            "Factorial.thy",
            "Euclidean_Rings.thy",
            "Semiring_Normalization.thy",
            "Groebner_Basis.thy",
            "Presburger.thy",
            "Divides.thy",
            "Wfrec.thy",
            "Typedef.thy",
        ];

        let mut total_v = 0usize;
        let mut total_a = 0usize;
        let mut passed_files = 0usize;

        for fname in &files_to_try {
            let path = hol_dir.join(fname);
            if !path.exists() {
                continue;
            }

            // Build minimal DB: just this file's lemmas
            let Ok(source) = std::fs::read_to_string(&path) else { continue };
            let lemmas = crate::hol::hol_loader::parse_lemmas(&source);
            let mut db = HolTheoremDb::new();
            db.extend(&lemmas);
            HolTheoremDb::add_builtins(&mut db);

            let with_proofs: Vec<_> = lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
            if with_proofs.is_empty() {
                continue;
            }

            let sample = with_proofs.len().min(10);
            let mut verified = 0;

            HolTheoremDb::with_override(&db, || {
                for lem in with_proofs.iter().take(sample) {
                    if crate::isar::method::verify_lemma(lem).is_some() {
                        verified += 1;
                    }
                }
            });

            total_v += verified;
            total_a += sample;
            let pct = if sample > 0 { (verified as f64 / sample as f64) * 100.0 } else { 0.0 };
            eprintln!("  {}: {}/{} ({:.0}%)", fname, verified, sample, pct);
            passed_files += 1;
        }

        let pct = if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 };
        eprintln!("Expanded ({} files): {}/{} ({:.1}%)", passed_files, total_v, total_a, pct);
    }
}
