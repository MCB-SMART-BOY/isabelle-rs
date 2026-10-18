//! Opt-in HOL scale workloads; supervise with `cargo xtask supervise --scale-mode`.

use super::*;

#[path = "tier_diagnostics.rs"]
mod tier_diagnostics;

/// Explicitly selected legacy workload; no result grants theorem authority.
#[derive(Clone, Copy, clap::ValueEnum)]
pub enum ScaleMode {
    #[value(name = "load-first-50")]
    LoadFirst50,
    #[value(name = "load-100")]
    Load100,
    #[value(name = "load-500")]
    Load500,
    #[value(name = "load-1000")]
    Load1000,
    VerifyBeyondCore,
    VerifyExtended,
    VerifyGlobalDb,
    VerifySystematic,
    VerifyExpanded,
    VerifyExpandedOld,
    /// Original global-DB structured-proof sample (three per bundled core file).
    StructuredProofs,
    /// Original all-lemma verification of the first five scanned bundled files.
    VerifyBatchFirstFive,
    /// Original ten-lemma List sample.
    VerifyListSample,
    /// Original thirty-five-lemma Nat sample.
    VerifyNatSample,
    /// Original four named List induction attempts.
    VerifyInductionSample,
    /// Original full upstream SessionBuilder failure report.
    AnalyzeFailures,
    /// Original Tier2 source list, per-file soft deadlines and search limits.
    #[value(name = "tier2")]
    Tier2,
    /// Original Tier3 source list without an additional per-file search budget.
    #[value(name = "tier3")]
    Tier3,
}

/// User-fixable source-tree problem preventing a diagnostic run.
#[derive(Debug, thiserror::Error)]
pub enum ScaleDiagnosticError {
    /// A required HOL source file or directory cannot be read (user-fixable).
    #[error("cannot read required HOL diagnostic source {path}: {source}")]
    Source {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    /// No selected source could be read and processed (user-fixable).
    #[error("no {tier} diagnostic files processed; check the bundled theories/HOL source tree")]
    NoFilesProcessed { tier: &'static str },
}

pub use workloads::run;

fn require_source(path: &Path) -> Result<(), ScaleDiagnosticError> {
    std::fs::File::open(path)
        .and_then(|file| {
            if file.metadata()?.is_file() {
                Ok(())
            } else {
                Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "expected a regular theory source file",
                ))
            }
        })
        .map_err(|source| ScaleDiagnosticError::Source { path: path.to_path_buf(), source })
}

mod workloads {
    use super::*;

    /// Run an explicit workload; completion never establishes proof success.
    pub fn run(mode: ScaleMode) -> Result<(), ScaleDiagnosticError> {
        let marker = match mode {
            ScaleMode::LoadFirst50
            | ScaleMode::StructuredProofs
            | ScaleMode::VerifyBatchFirstFive => Some(Path::new("theories/HOL/HOL.thy")),
            ScaleMode::VerifyListSample
            | ScaleMode::VerifyNatSample
            | ScaleMode::VerifyInductionSample
            | ScaleMode::Tier2
            | ScaleMode::Tier3 => None,
            _ => Some(Path::new("isabelle-source/src/HOL/HOL.thy")),
        };
        if let Some(marker) = marker {
            require_source(marker)?;
        }
        if matches!(mode, ScaleMode::VerifyGlobalDb) {
            require_source(Path::new("theories/HOL/HOL.thy"))?;
        }
        match mode {
            ScaleMode::LoadFirst50 => load_first_50(),
            ScaleMode::Load100 => load_100_from_full_hol(),
            ScaleMode::Load500 => load_500_from_full_hol(),
            ScaleMode::Load1000 => load_1000_from_full_hol(),
            ScaleMode::VerifyBeyondCore => verify_beyond_core(),
            ScaleMode::VerifyExtended => verify_extended(),
            ScaleMode::VerifyGlobalDb => verify_global_db(),
            ScaleMode::VerifySystematic => verify_systematic(),
            ScaleMode::VerifyExpanded => verify_expanded(),
            ScaleMode::VerifyExpandedOld => verify_expanded_old(),
            ScaleMode::StructuredProofs => crate::isar::diag::run_structured_proofs(),
            ScaleMode::VerifyBatchFirstFive => {
                crate::isar::method::diagnostics::run_batch_first_five()?
            },
            ScaleMode::VerifyListSample => crate::isar::method::diagnostics::run_list_sample(),
            ScaleMode::VerifyNatSample => crate::isar::method::diagnostics::run_nat_sample(),
            ScaleMode::VerifyInductionSample => {
                crate::isar::method::diagnostics::run_induction_sample()
            },
            ScaleMode::AnalyzeFailures => analyze_failures()?,
            ScaleMode::Tier2 => tier_diagnostics::run_tier2()?,
            ScaleMode::Tier3 => tier_diagnostics::run_tier3()?,
        }
        Ok(())
    }
    fn is_transitional_strict_closed(lemma: &ParsedLemma, db: &HolTheoremDb) -> bool {
        let result = crate::isar::method::verify_lemma(lemma, db);
        crate::isar::method::classify_verify_result(&lemma.name, &result)
            .is_transitional_strict_closed()
    }

    fn analyze_failures() -> Result<(), ScaleDiagnosticError> {
        const FAILURE_PREVIEW_LIMIT: usize = 10;
        let path = Path::new("isabelle-source/src/HOL");
        let mut builder = crate::theory::session_builder::SessionBuilder::new();
        builder.set_accept_all(true);
        builder
            .scan(path)
            .map_err(|source| ScaleDiagnosticError::Source { path: path.to_path_buf(), source })?;
        builder.resolve_dependencies();
        let report = builder.build_with_classifier();
        let syntax_count = report.counts.get("SYNTAX").copied().unwrap_or(0);
        let dependency_count = report.counts.get("DEPEND").copied().unwrap_or(0);
        let unsupported_count = report.counts.get("UNSUP").copied().unwrap_or(0);
        let conflict_count = report.counts.get("CONFLICT").copied().unwrap_or(0);
        let proof_count = report.counts.get("PROOF").copied().unwrap_or(0);
        let partial_count = report.counts.get("PARTIAL").copied().unwrap_or(0);
        eprintln!("\nFailure Analysis:");
        eprintln!("  SYNTAX errors:  {syntax_count} files");
        eprintln!("  DEPEND errors:  {dependency_count} files");
        eprintln!("  UNSUP errors:   {unsupported_count} files");
        eprintln!("  CONFLICT errors: {conflict_count} files");
        eprintln!("  PROOF failures: {proof_count} files");
        eprintln!("  PARTIAL passes: {partial_count} files");
        report.print_failures(FAILURE_PREVIEW_LIMIT);
        if syntax_count > 0 {
            eprintln!("\n  ACTION: Fix syntax errors first — these block all lemmas");
        }
        if dependency_count > 0 {
            eprintln!("  ACTION: Resolve missing, failed, or incompatible imports");
        }
        if proof_count > 0 {
            eprintln!("  ACTION: Add proof method support for the failing patterns");
        }
        Ok(())
    }

    fn load_first_50() {
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

    fn load_100_from_full_hol() {
        load_n_from_full_hol(100);
    }

    fn load_500_from_full_hol() {
        load_n_from_full_hol(500);
    }

    fn load_1000_from_full_hol() {
        load_n_from_full_hol(1000);
    }

    /// Load 200 files and verify sample lemmas from key files beyond the core 5.
    fn verify_beyond_core() {
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
            if let Some(node) = graph.nodes.get(name)
                && let Ok((lemmas, _source)) = TheoryGraph::load_file(&node.path)
            {
                db.extend(&lemmas);
            }
        }
        HolTheoremDb::add_builtins(&mut db);
        eprintln!("DB: {} theorems, {} by-name", db.all.len(), db.by_name.len());

        // Classify sampled lemmas using the custom legacy DB.
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
            let with_proofs: Vec<_> = lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
            let sample = with_proofs.len().min(15);
            let mut verified = 0;
            for lem in with_proofs.iter().take(sample) {
                if is_transitional_strict_closed(lem, &db) {
                    verified += 1;
                }
            }
            total_v += verified;
            total_a += sample;
            eprintln!("  {}: {}/{}", fname, verified, sample);
        }
        eprintln!(
            "Beyond-core TransitionalStrictClosed: {}/{} ({:.1}%)",
            total_v,
            total_a,
            if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 }
        );
    }

    fn verify_extended() {
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
            if let Some(node) = graph.nodes.get(name)
                && let Ok((lemmas, _source)) = TheoryGraph::load_file(&node.path)
            {
                db.extend(&lemmas);
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

        for fname in &target_files {
            let path = hol_dir.join(fname);
            if !path.exists() {
                continue;
            }
            let source = std::fs::read_to_string(&path).unwrap_or_default();
            let lemmas = crate::hol::hol_loader::parse_lemmas(&source);
            let with_proofs: Vec<_> = lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
            let sample = with_proofs.len().min(10);
            if sample == 0 {
                continue;
            }
            let mut verified = 0;
            for lem in with_proofs.iter().take(sample) {
                if is_transitional_strict_closed(lem, &db) {
                    verified += 1;
                }
            }
            total_v += verified;
            total_a += sample;
            let pct = if sample > 0 { (verified as f64 / sample as f64) * 100.0 } else { 0.0 };
            eprintln!("  {}: {}/{} ({:.0}%)", fname, verified, sample, pct);
        }

        let pct = if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 };
        eprintln!(
            "Extended TransitionalStrictClosed ({}/{} files): {}/{} ({:.1}%)",
            target_files.len(),
            target_files.len(),
            total_v,
            total_a,
            pct
        );
    }

    /// Verify overflow-prone files using the global theorem database.
    fn verify_global_db() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("isabelle-source/src/HOL not found, skipping");
            return;
        }
        let db = HolTheoremDb::global();
        eprintln!("Global DB: {} theorems", db.all.len());

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
                if is_transitional_strict_closed(lem, db) {
                    verified += 1;
                }
            }
            total_v += verified;
            total_a += sample;
            let pct = if sample > 0 { (verified as f64 / sample as f64) * 100.0 } else { 0.0 };
            eprintln!("  {}: {}/{} ({:.0}%)", fname, verified, sample, pct);
        }
        let pct = if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 };
        eprintln!("Global DB TransitionalStrictClosed: {}/{} ({:.1}%)", total_v, total_a, pct);
    }

    /// Systematic scan: classify sampled lemmas from many HOL files with a cumulative DB.
    fn verify_systematic() {
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
            if let Some(node) = graph.nodes.get(name)
                && let Ok((lemmas, source)) = TheoryGraph::load_file(&node.path)
            {
                let file_env = HolTheoremDb::build_type_env(&source);
                db.type_env.consts.extend(file_env.consts);
                db.type_env.types.extend(file_env.types);
                db.extend(&lemmas);
            }
        }
        HolTheoremDb::add_builtins(&mut db);
        eprintln!("DB: {} theorems", db.all.len());

        // Test files from the first 150 loaded
        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut total_thms = 0usize;
        let mut total_verified = 0usize;

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
                    if is_transitional_strict_closed(lem, &db) {
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

        eprintln!(
            "Systematic: {}/{} files all transitional, {}/{} TransitionalStrictClosed ({:.1}%)",
            passed,
            passed + failed,
            total_verified,
            total_thms,
            if total_thms > 0 { (total_verified as f64 / total_thms as f64) * 100.0 } else { 0.0 }
        );
    }

    /// Verify additional theory files beyond the core beyond-core set.
    fn verify_expanded() {
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

            for lem in with_proofs.iter().take(sample) {
                if is_transitional_strict_closed(lem, &db) {
                    verified += 1;
                }
            }

            total_v += verified;
            total_a += sample;
            let pct = if sample > 0 { (verified as f64 / sample as f64) * 100.0 } else { 0.0 };
            eprintln!("  {}: {}/{} ({:.0}%)", fname, verified, sample, pct);
            passed_files += 1;
        }

        let pct = if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 };
        eprintln!(
            "Expanded TransitionalStrictClosed ({} files): {}/{} ({:.1}%)",
            passed_files, total_v, total_a, pct
        );
    }

    /// Verify additional theory files beyond the core beyond-core set. (OLD)
    fn verify_expanded_old() {
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

            for lem in with_proofs.iter().take(sample) {
                if is_transitional_strict_closed(lem, &db) {
                    verified += 1;
                }
            }

            total_v += verified;
            total_a += sample;
            let pct = if sample > 0 { (verified as f64 / sample as f64) * 100.0 } else { 0.0 };
            eprintln!("  {}: {}/{} ({:.0}%)", fname, verified, sample, pct);
            passed_files += 1;
        }

        let pct = if total_a > 0 { (total_v as f64 / total_a as f64) * 100.0 } else { 0.0 };
        eprintln!(
            "Expanded TransitionalStrictClosed ({} files): {}/{} ({:.1}%)",
            passed_files, total_v, total_a, pct
        );
    }
}
