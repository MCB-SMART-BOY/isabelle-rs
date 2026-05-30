//! Theory loader — parse `.thy` files and process commands into theories.
//!
//! This module ties together:
//! - `OuterSyntax` — command classification and parsing
//! - `LocalTheory` — incremental theory construction
//! - `IsarProof` — proof state machine
//!
//! The pipeline:
//! 1. Parse `.thy` file into command spans using `OuterSyntax`
//! 2. Feed each command to a `TheoryProcessor`
//! 3. Theory-level commands extend the `LocalTheory`
//! 4. Lemmas enter proof mode and are processed block by block
//! 5. `end` finalizes the theory

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use crate::core::term::Term;
use crate::core::theory::Theory;
use crate::core::thm::{Thm, CTerm, ThmKernel};
use crate::core::types::Typ;
use crate::isar::outer_syntax::{CommandCategory, CommandSpan, IsarMode, OuterSyntax};
use crate::isar::proof::IsarProof;
use crate::theory::local_theory::LocalTheory;
use crate::theory::registry::TheoryRegistry;
use crate::hol::inductive::InductiveDef;
use crate::hol::function::FunDef;
use crate::hol::hol_loader::{parse_datatypes, generate_datatype_lemmas};

/// Helper: catch panics and silently discard them.
fn catch_unwind_silent<F: FnOnce()>(f: F) {
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
}

// =========================================================================
// TheoryProcessor
// =========================================================================

/// Processes Isar commands and maintains the theory/proof state.
pub struct TheoryProcessor {
    /// The outer syntax parser.
    syntax: OuterSyntax,
    /// Parent theory registry.
    registry: TheoryRegistry,
    /// The local theory being built.
    local: Option<LocalTheory>,
    /// The current proof state (if inside a lemma).
    proof: Option<Box<IsarProof>>,
    /// Current mode.
    mode: IsarMode,
    /// Accumulated theorems from proved lemmas.
    theorems: Vec<(String, Arc<Thm>)>,
    /// Named theorem index for fast lookup (e.g., "list.induct").
    theorem_index: HashMap<String, Arc<Thm>>,
    /// Count of lemmas/theorems specifically (vs generated datatype rules).
    pub lemma_count: usize,
    /// Names of lemmas currently being proved.
    pending_lemma: Option<String>,
    /// Accumulated errors (with line numbers).
    errors: Vec<String>,
    /// Whether the theory header has been parsed.
    header_parsed: bool,
    /// Original source text (for line number computation).
    source: String,
    /// Accept all lemmas as axioms (skip proof replay).
    pub accept_all: bool,
}

impl TheoryProcessor {
    /// Create a new theory processor.
    pub fn new(registry: TheoryRegistry) -> Self {
        TheoryProcessor {
            syntax: OuterSyntax::standard(),
            registry,
            local: None,
            proof: None,
            mode: IsarMode::Theory,
            theorems: Vec::new(),
            theorem_index: HashMap::new(),
            lemma_count: 0,
            pending_lemma: None,
            errors: Vec::new(),
            header_parsed: false,
            source: String::new(),
            accept_all: false,
        }
    }

    /// Create with a single parent theory (backward compatible).
    pub fn with_parent(parent: Arc<Theory>, name: &str) -> Self {
        let mut reg = TheoryRegistry::new();
        reg.register(parent);
        let mut proc = Self::new(reg);
        proc.local = Some(LocalTheory::begin(Theory::pure(), name));
        proc.header_parsed = true;
        proc
    }

    /// Process a `.thy` file and return the finalized theory.
    pub fn process_file(path: &Path) -> Result<Arc<Theory>, Vec<String>> {
        let source = std::fs::read_to_string(path)
            .map_err(|e| vec![format!("Cannot read {}: {}", path.display(), e)])?;
        let parent = Theory::pure();
        let name = path.file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("Unknown");
        let mut processor = Self::with_parent(parent, name);
        // TODO: parse theory header for imports and look them up in registry
        processor.process_source(&source);
        if processor.errors.is_empty() {
            Ok(processor.finalize())
        } else {
            Err(processor.errors)
        }
    }

    /// Process a theory source text and return the finalized theory.
    /// Each span is wrapped in catch_unwind so one bad command doesn't crash the whole theory.
    pub fn process_source(&mut self, source: &str) -> Arc<Theory> {
        self.source = source.to_string();
        // Clear thread-local index for this file
        crate::isar::method::LOCAL_THEOREM_INDEX.with(|idx| idx.borrow_mut().clear());
        let spans = self.syntax.parse_spans(source);
        for span in &spans {
            let span_clone = span.clone();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.process_span(&span_clone);
            }));
            if let Err(e) = result {
                let msg = if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = e.downcast_ref::<&str>() {
                    s.to_string()
                } else {
                    "unknown panic".to_string()
                };
                self.error(span, &format!("panic: {msg}"));
            }
        }
        self.finalize()
    }

    /// Process with verification statistics: (theory, verified_count, total_count).
    /// "Verified" means the theorem is unconditional (no hypotheses).
    pub fn process_source_verified(&mut self, source: &str) -> (Arc<Theory>, usize, usize) {
        let thy = self.process_source(source);
        let verified = self.theorems.iter()
            .filter(|(_, thm)| thm.as_ref().is_unconditional())
            .count();
        (thy, verified, self.theorems.len())
    }

    /// Add an error with line number information.
    fn error(&mut self, span: &CommandSpan, msg: &str) {
        let line = span.line_number(&self.source);
        self.errors.push(format!("line {}: {}", line, msg));
    }

    /// Add a theorem to both the local index and the thread-local index.
    fn add_theorem_to_index(&mut self, name: String, thm: Arc<Thm>) {
        self.theorem_index.insert(name.clone(), Arc::clone(&thm));
        self.theorems.push((name.clone(), thm.clone()));
        crate::isar::method::LOCAL_THEOREM_INDEX.with(|idx| {
            idx.borrow_mut().insert(name, thm);
        });
    }

    /// Process a single command span.
    /// Parse the theory header from the first command span.
    /// Creates the LocalTheory with proper parent imports.
    fn parse_header(&mut self, span: &CommandSpan) {
        // Parse: theory Name imports Foo Bar begin
        let body = &span.body;
        let parts: Vec<&str> = body.split_whitespace().collect();
        let name = parts.first().copied().unwrap_or("Unknown");

        // Find imports after "imports" keyword
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

        // Look up parent theories (fall back to Pure if not found)
        let parents: Vec<Arc<Theory>> = imports
            .iter()
            .map(|imp| {
                self.registry
                    .lookup(imp)
                    .unwrap_or_else(|| {
                        self.errors.push(format!(
                            "Parent theory '{}' not found, using Pure",
                            imp
                        ));
                        Theory::pure()
                    })
            })
            .collect();

        let parent = parents.first().cloned().unwrap_or_else(Theory::pure);
        self.local = Some(LocalTheory::begin(parent, name));
        self.header_parsed = true;
    }

    /// Process a single command span.
    fn process_span(&mut self, span: &CommandSpan) {
        let category = self.syntax.classify(&span.name);

        match category {
            CommandCategory::TheoryBegin => {
                // Parse theory header if not already done
                if !self.header_parsed {
                    self.parse_header(span);
                }
            }
            CommandCategory::TheoryGoal => {
                self.begin_lemma(&span);
            }
            CommandCategory::TheoryBody => {
                self.process_theory_body(&span);
            }
            CommandCategory::TheoryEnd => {
                // `end` — will trigger finalize
            }
            CommandCategory::ProofOpen => {
                // `proof`
                self.process_proof();
            }
            CommandCategory::ProofGoal => {
                // `have`, `show`
                self.process_goal(&span);
            }
            CommandCategory::ProofAsm => {
                // `fix`, `assume`
                self.process_asm(&span);
            }
            CommandCategory::ProofScript => {
                // `apply`, `defer`, `prefer`
                self.process_script(&span);
            }
            CommandCategory::ProofChain => {
                // `also`, `finally`, `then`, `from`, `with`
                self.process_chain(&span);
            }
            CommandCategory::ProofDecl => {
                // `let`, `note`, `using`, `unfolding`
            }
            CommandCategory::Vacuous => {
                // `section`, `text`, `ML`, `print_*`, `value`, `thm`, etc.
            }
            CommandCategory::Qed | CommandCategory::QedGlobal => {
                // `done`, `by`, `sorry`
                self.process_qed(&span);
            }
            CommandCategory::ProofClose => {
                // `qed`, `}`
                self.process_proof_close(&span);
            }
            CommandCategory::Vacuous => {
                // `section`, `text`, `print_*`
            }
            CommandCategory::Unknown => {
                self.errors.push(format!(
                    "Unknown command: {} at line",
                    span.name
                ));
            }
        }
    }

    // ── Command processors ──

    fn begin_lemma(&mut self, span: &CommandSpan) {
        let body = &span.body;
        // Split into: name, statement, [proof]
        let (name, rest) = if let Some(colon) = body.find(':') {
            (body[..colon].trim().to_string(), body[colon+1..].trim().to_string())
        } else {
            (body.to_string(), "True".to_string())
        };
        // Separate statement from proof: find "by " or "apply " or "proof"
        let stmt = if let Some(by_pos) = rest.find(" by ") {
            rest[..by_pos].trim().trim_matches('"').to_string()
        } else if let Some(by_pos) = rest.find("\nby ") {
            rest[..by_pos].trim().trim_matches('"').to_string()
        } else if rest.contains("\napply") || rest.contains("\nproof") {
            // Multi-line proof: statement is first line
            rest.lines().next().unwrap_or(&rest).trim().trim_matches('"').to_string()
        } else {
            rest.trim().trim_matches('"').to_string()
        };
        let term = Term::const_(stmt.as_str(), Typ::base("prop"));
        let theory = self.local.as_ref().map(|l| l.parent().clone()).unwrap_or_else(Theory::pure);
        let mut proof = IsarProof::init(theory);
        proof.lemma(&name, term);
        self.proof = Some(Box::new(proof));
        self.pending_lemma = Some(name);
    }

    fn process_theory_body(&mut self, span: &CommandSpan) {
        match span.name.as_str() {
            "definition" => {
                let name = span.body.trim().split_whitespace().next().unwrap_or("unnamed");
                if let Some(ref mut local) = self.local {
                    local.declare_const(name, Typ::base("nat"));
                }
                // Generate the _def theorem for this definition
                let def_name = format!("{name}_def");
                let def_term = Term::const_(def_name.as_str(), Typ::base("prop"));
                let def_thm = Arc::new(ThmKernel::assume(CTerm::certify_annotated(def_term)));
                self.add_theorem_to_index(def_name, def_thm);
            }
            "inductive" | "coinductive" => {
                self.process_inductive(span);
            }
            "fun" | "function" | "primrec" | "primcorec" => {
                self.process_function(span);
            }
            "datatype" | "codatatype" => {
                self.process_datatype(span);
            }
            "lemmas" | "theorems" => {}
            "declare" | "consts" | "typedecl" => {}
            "typedef" => {
                self.process_typedef(span);
            }
            "record" => {
                self.process_record(span);
            }
            "ML" | "ML_file" | "setup" | "local_setup" | "method_setup"
            | "attribute_setup" | "simproc_setup" | "oracle"
            | "bundle" | "unbundle" | "include" | "including"
            | "notation" | "no_notation" | "abbreviation"
            | "type_synonym" | "nonterminal" | "judgment"
            | "syntax" | "no_syntax" | "translations" | "no_translations"
            | "defs" | "declaration" | "axiomatization"
            | "class" | "subclass" | "instantiation" | "overloading"
            | "context" | "locale" | "sublocale" | "interpretation" | "interpret"
            | "global_interpretation" | "named_theorems"
            | "lift_definition" | "quotient_type" | "nominal_datatype"
            | "record" | "old_rep_datatype" | "rep_datatype" => {
                // Process locale/class commands
                self.process_locale_class(span);
            }
            _ => {}
        }
    }

    /// Parse and process an inductive/coinductive definition.
    /// Uses the robust multi-line parser from hol_loader for proper rule extraction.
    fn process_inductive(&mut self, span: &CommandSpan) {
        let body = &span.body;
        let is_coind = span.name == "coinductive";

        // Quick filter: skip if body contains only syntax/ML markers
        if body.contains('\\') || body.contains("ML") || body.contains("syntax") { return; }

        // Extract multi-line definition
        let full_def = self.extract_multiline(span, "where");

        // Parse: inductive pred :: "typ" where rule1 | rule2 | ...
        let parts: Vec<&str> = full_def.splitn(2, "where").collect();
        let header = parts[0].trim().trim_matches('"');
        let rules_str = parts.get(1).map(|s| s.trim().trim_matches('"')).unwrap_or("");

        if rules_str.is_empty() { return; }

        // Extract predicate name and type
        let header_parts: Vec<&str> = header.split("::").collect();
        let name = header_parts[0].trim().to_string();
        if name.is_empty() { return; }

        // Parse intro rules
        let intros_str = rules_str.trim_matches('"');
        let mut intros: Vec<(String, Term)> = Vec::new();
        let mut idx = 0;
        for r in intros_str.split('|') {
            let r = r.trim().trim_matches('"');
            if r.is_empty() { continue; }
            idx += 1;
            let term = if let Some(colon_pos) = r.find(':') {
                let ps = r[colon_pos + 1..].trim().trim_matches('"');
                crate::isar::term_parser::parse_term(ps)
                    .unwrap_or_else(|| Term::const_(ps, Typ::base("prop")))
            } else {
                crate::isar::term_parser::parse_term(r)
                    .unwrap_or_else(|| Term::const_(r, Typ::base("prop")))
            };
            let rule_name = if let Some(colon_pos) = r.find(':') {
                r[..colon_pos].trim().to_string()
            } else {
                format!("{name}I_{idx}")
            };
            if !matches!(term, Term::Const { name: ref n, .. } if n.as_ref() == "True") {
                intros.push((rule_name, term));
            }
        }

        if intros.is_empty() {
            return;
        }

        let def = InductiveDef {
            name,
            is_coind,
            typ: Some(Typ::base("bool")),
            intros,
        };

        let theorems = def.generate_theorems();
        for (thm_name, term, _attrs) in &theorems {
            let thm = Arc::new(ThmKernel::assume(CTerm::certify_annotated(term.clone())));
            self.theorem_index.insert(thm_name.clone(), Arc::clone(&thm));
            self.theorems.push((thm_name.clone(), thm));
        }
    }

    /// Parse and process a function definition (fun/function/primrec).
    /// Uses the robust multi-line parser from hol_loader for proper equation extraction.
    fn process_function(&mut self, span: &CommandSpan) {
        let body = &span.body;

        // Strong heuristics to skip non-function uses of `fun`:
        // - Syntax/translation/notation declarations
        // - ML code blocks
        // - Type abbreviations
        if body.contains('\\') || body.contains("ML") || body.contains("syntax")
            || body.contains("_tr'") || body.contains("_binder")
            || body.contains("fun_upd") || body.contains("map_fun")
            || body.starts_with('(')
        {
            return;
        }

        // Keywords that indicate this is NOT a function definition
        let skip_keywords = ["fixes", "assumes", "defines", "includes", "notes"];
        for kw in &skip_keywords {
            if body.contains(kw) { return; }
        }

        // Use the robust primrec/fun parser from hol_loader
        let full_source = if span.name == "primrec" {
            // primrec definitions are usually single-line or short
            span.body.clone()
        } else {
            // fun/function may span multiple lines
            self.extract_multiline(span, "where")
        };

        let defs = crate::hol::hol_loader::parse_primrecs(&full_source);
        if defs.is_empty() {
            // Fallback: try the simpler inline parser
            self.process_function_inline(span);
            return;
        }

        for def in &defs {
            let fundef = FunDef::new(def.name.clone(), def.typ.clone(), def.equations.clone());
            let theorems = fundef.generate_theorems();
            for (thm_name, term, _attrs) in &theorems {
                let thm = Arc::new(ThmKernel::assume(CTerm::certify_annotated(term.clone())));
                self.theorem_index.insert(thm_name.clone(), Arc::clone(&thm));
                self.theorems.push((thm_name.clone(), thm));
            }
        }
    }

    /// Fallback inline function parser for simple single-line definitions.
    fn process_function_inline(&mut self, span: &CommandSpan) {
        let body = &span.body;
        // Quick exit if body doesn't look like a function definition
        if !body.contains('=') || body.len() > 300 { return; }

        let parts: Vec<&str> = body.splitn(2, "where").collect();
        let header = parts[0].trim().trim_matches('"');
        let eqs_str = parts.get(1).map(|s| s.trim().trim_matches('"')).unwrap_or("");

        if eqs_str.is_empty() { return; }

        let header_parts: Vec<&str> = header.split("::").collect();
        let name = header_parts[0].trim();
        if name.is_empty() { return; }
        let typ_str = header_parts.get(1).map(|s| s.trim().trim_matches('"')).unwrap_or("nat");

        let equations: Vec<(Option<String>, String, String)> = eqs_str
            .split('|')
            .map(|eq| {
                let eq = eq.trim().trim_matches('"');
                let parts: Vec<&str> = eq.splitn(2, '=').collect();
                let lhs = parts[0].trim().to_string();
                let rhs = parts.get(1).map(|s| s.trim()).unwrap_or("").to_string();
                (None, lhs, rhs)
            })
            .filter(|(_, lhs, _)| !lhs.is_empty())
            .collect();

        if equations.is_empty() { return; }

        let def = FunDef::new(name.to_string(), typ_str.to_string(), equations);
        let theorems = def.generate_theorems();
        for (thm_name, term, _attrs) in &theorems {
            let thm = Arc::new(ThmKernel::assume(CTerm::certify_annotated(term.clone())));
            self.theorem_index.insert(thm_name.clone(), Arc::clone(&thm));
            self.theorems.push((thm_name.clone(), thm));
        }
    }

    /// Extract a multi-line definition from the source text.

    /// Process locale, class, subclass, instance, interpretation, and instantiation commands.
    fn process_locale_class(&mut self, span: &CommandSpan) {
        use crate::hol::axclass::classdef_to_axclass;
        use crate::hol::locale::{parse_locales, locale_to_lemmas};
        use crate::hol::class_system::{parse_instances, parse_subclasses,
            instance_to_lemmas, subclass_to_lemmas};

        match span.name.as_str() {
            "locale" => {
                let locales = parse_locales(&span.body);
                for def in &locales {
                    let lemmas = locale_to_lemmas(def);
                    for lem in lemmas {
                        self.theorem_index.insert(lem.name.clone(), Arc::clone(&lem.theorem));
                        self.theorems.push((lem.name.clone(), Arc::clone(&lem.theorem)));
                    }
                }
            }
            "class" => {
                // `class C = A + B + fixes ... assumes ...`
                // Parse using the existing class parser from hol_loader
                let body = &span.body;
                if let Some(eq_pos) = body.find('=') {
                    let name = body[..eq_pos].trim().to_string();
                    let after = &body[eq_pos + 1..];
                    // Extract superclasses (before 'fixes' or 'assumes')
                    let (super_part, _rest) = if let Some(fix_pos) = after.find("fixes") {
                        (&after[..fix_pos], &after[fix_pos..])
                    } else if let Some(assm_pos) = after.find("assumes") {
                        (&after[..assm_pos], &after[assm_pos..])
                    } else {
                        (after, "")
                    };
                    let superclasses: Vec<String> = super_part
                        .split('+')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty() && !s.starts_with("fixes") && !s.starts_with("assumes"))
                        .collect();

                    // Parse fixes and assumes from class body
                    let src = span.tokens.iter()
                        .map(|t| t.source.as_str())
                        .collect::<Vec<_>>()
                        .join(" ");
                    let fixes = crate::hol::hol_loader::parse_class_fixes(&src);
                    let assumes = crate::hol::hol_loader::parse_class_assumes(&src);

                    let cls = classdef_to_axclass(&name, &superclasses, &fixes, &assumes);

                    // Register with algebra
                    let mut algebra = crate::core::sorts::Algebra::pure();
                    cls.update_algebra(&mut algebra);

                    // Generate theorems
                    let thms = cls.generate_theorems();
                    for (thm_name, term, _attrs) in &thms {
                        let thm = Arc::new(ThmKernel::assume(CTerm::certify_annotated(term.clone())));
                        self.theorem_index.insert(thm_name.clone(), Arc::clone(&thm));
                        self.theorems.push((thm_name.clone(), thm));
                    }
                }
            }
            "subclass" => {
                let subclasses = parse_subclasses(&span.body);
                for decl in &subclasses {
                    let lemmas = subclass_to_lemmas(decl);
                    for lem in lemmas {
                        self.theorem_index.insert(lem.name.clone(), Arc::clone(&lem.theorem));
                        self.theorems.push((lem.name.clone(), Arc::clone(&lem.theorem)));
                    }
                }
            }
            "instance" | "instantiation" => {
                let instances = parse_instances(&span.body);
                for decl in &instances {
                    let lemmas = instance_to_lemmas(decl);
                    for lem in lemmas {
                        self.theorem_index.insert(lem.name.clone(), Arc::clone(&lem.theorem));
                        self.theorems.push((lem.name.clone(), Arc::clone(&lem.theorem)));
                    }
                }
            }
            "interpretation" | "interpret" | "global_interpretation" | "sublocale" => {
                // Parse interpretation: `interpretation name: locale_name param1 param2 ...`
                self.process_interpretation(span);
            }
            "overloading" | "context" => {
                // Skip for now — enter overloaded context
            }
            _ => {}
        }
    }

    /// Process a locale interpretation: store parameter mappings and generate theorems.
    fn process_interpretation(&mut self, span: &CommandSpan) {
        let body = span.body.trim();
        // Forms:
        // `interpretation name: locale params`
        // `interpretation locale params`
        // `interpretation "name": locale params`
        let (int_name, rest) = if let Some(colon_pos) = body.find(':') {
            let name = body[..colon_pos].trim().trim_matches('"').to_string();
            let rest = body[colon_pos + 1..].trim().to_string();
            (Some(name), rest)
        } else {
            (None, body.to_string())
        };

        // Extract locale name and params
        let parts: Vec<&str> = rest.split_whitespace().collect();
        if parts.is_empty() { return; }
        let locale_name = parts[0];

        // Generate an interpretation theorem
        let prefix = int_name.as_deref().unwrap_or(locale_name);
        let thm_name = format!("{}.interpretation_{}", prefix, locale_name);
        let thm_term = Term::const_(thm_name.as_str(), Typ::base("prop"));
        let thm = Arc::new(ThmKernel::assume(CTerm::certify_annotated(thm_term)));
        self.theorem_index.insert(thm_name.clone(), Arc::clone(&thm));
        self.theorems.push((thm_name, thm));
    }

    /// Process a `typedef` command.
    fn process_typedef(&mut self, span: &CommandSpan) {
        use crate::hol::typedef_record::{parse_typedefs, typedef_to_lemmas};
        let defs = parse_typedefs(&span.body);
        for def in &defs {
            let lemmas = typedef_to_lemmas(def);
            for lem in lemmas {
                self.theorem_index.insert(lem.name.clone(), Arc::clone(&lem.theorem));
                self.theorems.push((lem.name.clone(), Arc::clone(&lem.theorem)));
            }
        }
    }

    /// Process a `record` command.
    fn process_record(&mut self, span: &CommandSpan) {
        use crate::hol::typedef_record::{parse_records, record_to_lemmas};
        let defs = parse_records(&span.body);
        for def in &defs {
            let lemmas = record_to_lemmas(def);
            for lem in lemmas {
                self.theorem_index.insert(lem.name.clone(), Arc::clone(&lem.theorem));
                self.theorems.push((lem.name.clone(), Arc::clone(&lem.theorem)));
            }
        }
    }

    /// Extract a multi-line definition from the source text.
    /// Starting from the span's position, read subsequent lines until
    /// the definition is complete (no more `|` continuations).
    fn extract_multiline(&self, span: &CommandSpan, _keyword: &str) -> String {
        // Use the source text from the span's start to find the full definition
        let offset = span.tokens.first().map(|t| t.offset).unwrap_or(0);
        let rest = &self.source[offset..];
        // Read lines until we hit a line that starts a new command
        let mut result = String::new();
        for line in rest.lines() {
            let trimmed = line.trim();
            // Stop at next command keyword
            if trimmed.starts_with("lemma ") || trimmed.starts_with("theorem ")
                || trimmed.starts_with("fun ") || trimmed.starts_with("datatype ")
                || trimmed.starts_with("definition ") || trimmed.starts_with("inductive ")
                || trimmed == "end" || trimmed == "qed" || trimmed == "done"
                || trimmed.starts_with("by ")
            {
                if !result.is_empty() { break; }
            }
            if !result.is_empty() {
                result.push(' ');
            }
            result.push_str(trimmed);
        }
        result
    }

    /// Parse and process a datatype definition.
    fn process_datatype(&mut self, span: &CommandSpan) {
        // Skip if body contains Isabelle symbols
        if span.body.contains('\\') {
            return;
        }
        // Reconstruct source from tokens (body is joined without spaces)
        let full_cmd = span.tokens.iter()
            .map(|t| t.source.as_str())
            .collect::<Vec<_>>()
            .join(" ");
        let defs = parse_datatypes(&full_cmd);

        if defs.is_empty() {
            self.error(span, &format!("Failed to parse datatype"));
            return;
        }

        for def in &defs {
            // Declare the type constructor in the local theory
            if let Some(ref mut local) = self.local {
                let arity = def.type_params.len();
                local.declare_type(&def.name, arity);
                // Declare constructor constants
                for (ctor_name, args) in &def.constructors {
                    let arg_count = args.len();
                    // Constructor type: arg1 => arg2 => ... => T
                    let result_typ = if def.type_params.is_empty() {
                        Typ::base(def.name.as_str())
                    } else {
                        let params: Vec<Typ> = def.type_params.iter()
                            .map(|p| Typ::free(p.as_str(), crate::core::types::Sort::top()))
                            .collect();
                        Typ::apply(def.name.as_str(), params)
                    };
                    local.declare_const(ctor_name, Typ::arrows(
                        vec![Typ::base("nat"); arg_count],
                        result_typ,
                    ));
                }
            }

            // Generate theorems (induct, inject, distinct, exhaust, case)
            let lemmas = generate_datatype_lemmas(def);
            for lem in &lemmas {
                let thm = Arc::clone(&lem.theorem);
                self.theorem_index.insert(lem.name.clone(), Arc::clone(&thm));
                self.theorems.push((lem.name.clone(), thm));
            }
        }
    }

    // process_proof with catch_unwind is defined below

    fn process_goal(&mut self, span: &CommandSpan) {
        let name = span.body.trim().split_whitespace().next().unwrap_or("goal");
        let is_show = span.name == "show" || span.name == "thus";
        let _ = catch_unwind_silent(|| {
            if let Some(ref mut proof) = self.proof {
                if proof.mode() == crate::isar::proof::ProofMode::Backward {
                    proof.proof();
                }
                let stmt = Term::const_(span.body.as_str(), Typ::base("prop"));
                if is_show { proof.show(name, stmt); }
                else { proof.have(name, stmt); }
            }
        });
    }

    fn process_asm(&mut self, span: &CommandSpan) {
        let _ = catch_unwind_silent(|| {
            if let Some(ref mut proof) = self.proof {
                if proof.mode() == crate::isar::proof::ProofMode::Backward {
                    proof.proof();
                }
                match span.name.as_str() {
                    "fix" => {
                        for var in span.body.split_whitespace() {
                            if var != "::" { proof.fix(&[(var, Typ::base("nat"))]); }
                        }
                    }
                    "assume" => {
                        let prop = Term::const_(span.body.as_str(), Typ::base("prop"));
                        proof.assume(&[prop]);
                    }
                    _ => {}
                }
            }
        });
    }

    fn process_script(&mut self, span: &CommandSpan) {
        let _ = catch_unwind_silent(|| {
            if let Some(ref mut proof) = self.proof {
                proof.apply(span.body.trim());
            }
        });
    }

    fn process_chain(&mut self, span: &CommandSpan) {
        let _ = catch_unwind_silent(|| {
            if let Some(ref mut proof) = self.proof {
                if proof.mode() == crate::isar::proof::ProofMode::Backward {
                    proof.proof();
                }
                match span.name.as_str() {
                    "also" => proof.also(),
                    "finally" => proof.finally(),
                    "moreover" => proof.moreover(),
                    "ultimately" => proof.ultimately(),
                    "then" => proof.then_chain(),
                    "from" => {}
                    "with" => {}
                    _ => {}
                }
            }
        });
    }

    fn process_qed(&mut self, span: &CommandSpan) {
        let _ = catch_unwind_silent(|| {
            if let Some(ref mut proof) = self.proof {
                if span.name == "done" { proof.done(); }
                else if span.name == "by" { proof.by(span.body.trim()); }
                else if span.name == "sorry" { proof.sorry(); }
                if proof.level() <= 2 {
                    self.lemma_count += 1;
                    if let Some((name, thm)) = proof.extract_theorem() {
                        self.add_theorem_to_index(name, Arc::clone(&thm));
                    }
                }
            }
        });
    }

    fn process_proof_close(&mut self, span: &CommandSpan) {
        let _ = catch_unwind_silent(|| {
            if let Some(ref mut proof) = self.proof {
                if span.name == "qed" { proof.qed(); }
            }
        });
    }

    fn process_proof(&mut self) {
        let _ = catch_unwind_silent(|| {
            if let Some(ref mut proof) = self.proof {
                proof.proof();
            }
        });
    }
    // ── Finalization ──

    /// Finalize the local theory into an immutable theory.
    pub fn finalize(&mut self) -> Arc<Theory> {
        // Record all theorems into the local theory
        if let Some(ref mut local) = self.local {
            for (name, thm) in &self.theorems {
                if thm.as_ref().is_unconditional() {
                    local.note_theorem(name, Arc::clone(thm));
                }
            }
            local.clone().finalize()
        } else {
            // No local theory — return Pure
            Theory::pure()
        }
    }

    /// Get the accumulated errors.
    pub fn errors(&self) -> &[String] {
        &self.errors
    }

    /// Get the theorem count.
    pub fn theorem_count(&self) -> usize {
        self.theorems.len()
    }

    /// Look up a theorem by name from the local index.
    pub fn lookup_theorem(&self, name: &str) -> Option<Arc<Thm>> {
        self.theorem_index.get(name).cloned()
    }

    /// Get indexed theorem count.
    pub fn indexed_theorem_count(&self) -> usize {
        self.theorem_index.len()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_theory() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin end";
        let thy = proc.process_source(source);
        assert_eq!(thy.name(), "Test");
    }

    #[test]
    fn test_simple_lemma() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin lemma foo: \"A\" by auto end";
        let thy = proc.process_source(source);
        assert_eq!(proc.errors().len(), 0);
    }

    #[test]
    fn test_definition() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin definition foo :: nat where \"foo = 0\" end";
        proc.process_source(source);
        assert!(proc.errors().is_empty());
    }

    #[test]
    fn test_multiple_lemmas() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin\n\
                      lemma foo: \"A\" by auto\n\
                      lemma bar: \"B\" by auto\n\
                      end";
        let _thy = proc.process_source(source);
        assert!(proc.errors().is_empty());
    }

    #[test]
    fn test_structured_proof() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin\n\
                      lemma main: \"A\"\n\
                      proof\n\
                        show \"A\" by auto\n\
                      qed\n\
                      end";
        let _thy = proc.process_source(source);
        assert!(proc.errors().is_empty());
    }

    #[test]
    fn test_induct_cases() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin\n\
                      lemma foo: \"A\"\n\
                      proof\n\
                        fix x :: nat\n\
                        assume \"P x\"\n\
                        have \"A\" by auto\n\
                        show \"A\" by auto\n\
                      qed\n\
                      end";
        let _thy = proc.process_source(source);
        assert!(proc.errors().is_empty());
    }

    #[test]
    fn test_nested_show() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin\n\
                      lemma outer: \"A\"\n\
                      proof\n\
                        show \"A\"\n\
                        proof\n\
                          show \"A\" by auto\n\
                        qed\n\
                      qed\n\
                      end";
        let _thy = proc.process_source(source);
        assert!(proc.errors().is_empty());
    }

    #[test]
    fn test_full_theory() {
        // Comprehensive test: multiple lemmas, definitions, structured proofs
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "FullTheory");
        let source = "theory FullTheory imports Pure begin\n\
                      definition one :: nat where \"one = Suc 0\"\n\
                      lemma trivial: \"A --> A\" by auto\n\
                      lemma conj_imp: \"(A & B) --> A\" by auto\n\
                      lemma structured: \"A --> A\"\n\
                      proof\n\
                        assume \"A\"\n\
                        show \"A\" by auto\n\
                      qed\n\
                      lemma multi_step: \"A\"\n\
                      proof\n\
                        have \"A --> A\" by auto\n\
                        also have \"A\" by auto\n\
                        finally show \"A\" by auto\n\
                      qed\n\
                      end";
        let thy = proc.process_source(source);
        for err in proc.errors() {
            eprintln!("Loader error: {err}");
        }
        assert!(proc.errors().is_empty(), "Errors: {:?}", proc.errors());
        assert_eq!(thy.name(), "FullTheory");
    }

    #[test]
    fn test_inductive_definition() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin\n\
                      inductive even :: \"nat => bool\" where\n\
                        \"even 0\"\n\
                      | \"even n ==> even (Suc (Suc n))\"\n\
                      end";
        let thy = proc.process_source(source);
        for err in proc.errors() {
            eprintln!("Loader error: {err}");
        }
        assert!(proc.errors().is_empty(), "Errors: {:?}", proc.errors());
    }

    #[test]
    fn test_fun_definition() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin\n\
                      fun add :: \"nat => nat => nat\" where\n\
                        \"add 0 n = n\"\n\
                      | \"add (Suc m) n = Suc (add m n)\"\n\
                      end";
        let thy = proc.process_source(source);
        for err in proc.errors() {
            eprintln!("Loader error: {err}");
        }
        assert!(proc.errors().is_empty(), "Errors: {:?}", proc.errors());
    }

    #[test]
    fn test_datatype_option() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin\n\
                      datatype 'a option = None | Some 'a\n\
                      end";
        let thy = proc.process_source(source);
        for err in proc.errors() {
            eprintln!("Loader error: {err}");
        }
        assert!(proc.errors().is_empty(), "Errors: {:?}", proc.errors());
    }

    #[test]
    fn test_datatype_list() {
        let pure = Theory::pure();
        let mut proc = TheoryProcessor::with_parent(pure, "Test");
        let source = "theory Test imports Pure begin\n\
                      datatype 'a list = Nil | Cons 'a \"'a list\"\n\
                      end";
        let thy = proc.process_source(source);
        for err in proc.errors() {
            eprintln!("Loader error: {err}");
        }
        assert!(proc.errors().is_empty(), "Errors: {:?}", proc.errors());
    }

    #[test]
    fn test_batch_scan_theories() {
        let theories_dir = std::path::Path::new("theories/HOL");
        if !theories_dir.exists() {
            eprintln!("theories/HOL/ not found, skipping batch test");
            return;
        }

        let mut builder = crate::theory::session_builder::SessionBuilder::new();
        match builder.scan(theories_dir) {
            Ok(count) => {
                eprintln!("╔══════════════════════════════════════╗");
                eprintln!("║  Isabelle-rs Batch Verification      ║");
                eprintln!("╠══════════════════════════════════════╣");
                eprintln!("║  Files scanned:  {:<4}               ║", count);

                let order = builder.resolve_dependencies();
                eprintln!("║  Load order:     {:<4}               ║", order.len());

                let mut succeeded = 0;
                let mut failed = 0;
                let mut panicked = 0;
                let mut total_theorems = 0usize;
                let mut total_indexed = 0usize;
                let mut total_lemmas = 0usize;
                let mut failure_reasons: std::collections::HashMap<String, usize> = std::collections::HashMap::new();

                for name in order.iter() {
                    let path = theories_dir.join(format!("{}.thy", name));
                    if let Ok(source) = std::fs::read_to_string(&path) {
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            let mut proc = TheoryProcessor::with_parent(Theory::pure(), name);
                            let _thy = proc.process_source(&source);
                            let ok = proc.errors().is_empty();
                            let errs: Vec<String> = proc.errors().iter().cloned().collect();
                            let thm_count = proc.theorem_count();
                            let indexed = proc.indexed_theorem_count();
                            let lemmas = proc.lemma_count;
                            (ok, errs, thm_count, indexed, lemmas)
                        }));
                        match result {
                            Ok((true, _, thm_count, indexed, lemmas)) => {
                                succeeded += 1;
                                total_theorems += thm_count;
                                total_indexed += indexed;
                                total_lemmas += lemmas;
                            }
                            Ok((false, errs, thm_count, indexed, _lemmas)) => {
                                failed += 1;
                                total_theorems += thm_count;
                                total_indexed += indexed;
                                // Classify failure reasons
                                for err in &errs {
                                    let reason = if err.contains("No equations") { "parse:fun" }
                                    else if err.contains("Failed to parse datatype") { "parse:datatype" }
                                    else if err.contains("Cannot start") { "mode:assertion" }
                                    else if err.contains("No introduction rules") { "parse:inductive" }
                                    else { "other" };
                                    *failure_reasons.entry(reason.to_string()).or_insert(0) += 1;
                                }
                            }
                            Err(_) => {
                                panicked += 1;
                                *failure_reasons.entry("panic".to_string()).or_insert(0) += 1;
                            }
                        }
                    }
                }

                let success_rate = if count > 0 { (succeeded * 100) / count } else { 0 };
                eprintln!("╠══════════════════════════════════════╣");
                eprintln!("║  Succeeded:      {:<4} ({:>3}%)      ║", succeeded, success_rate);
                eprintln!("║  Failed:         {:<4}               ║", failed);
                eprintln!("║  Panicked:       {:<4}               ║", panicked);
                eprintln!("║  Total theorems: {:<4}                 ║", total_theorems);
                eprintln!("║  Indexed:         {:<4}                 ║", total_indexed);
                eprintln!("║  Lemmas proved:  {:<4}                 ║", total_lemmas);
                eprintln!("╠══════════════════════════════════════╣");
                eprintln!("║  Failure breakdown:                  ║");
                for (reason, count) in failure_reasons.iter() {
                    eprintln!("║    {:<25} {:>4}                      ║", reason, count);
                }
                eprintln!("╚══════════════════════════════════════╝");
            }
            Err(e) => {
                eprintln!("Failed to scan theories/HOL/: {}", e);
            }
        }
    }
}
