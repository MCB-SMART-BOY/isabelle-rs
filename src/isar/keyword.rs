//! Isar keyword classification — defines the categories for outer syntax commands.
//!
//! Corresponds to `src/Pure/Isar/keyword.ML`.
//!
//! Every Isar command has a **kind** that determines where it can appear:
//!
//! - **Theory-level**: `thy_begin`, `thy_end`, `thy_decl`, `thy_defn`, `thy_stmt`,
//!   `thy_goal`, `thy_load`
//! - **Proof-level**: `prf_goal`, `prf_block`, `prf_open`, `prf_close`, `prf_chain`,
//!   `prf_decl`, `prf_asm`, `prf_asm_goal`, `prf_script`, `prf_script_goal`
//! - **QED**: `qed`, `qed_script`, `qed_block`, `qed_global`
//! - **Document**: `diag`, `document_heading`, `document_body`, `document_raw`
//!
//! This module provides the `Keywords` table and query functions to classify
//! commands at runtime.

use std::collections::HashMap;

// =========================================================================
// Keyword kinds
// =========================================================================

pub const DIAG: &str = "diag";
pub const DOCUMENT_HEADING: &str = "document_heading";
pub const DOCUMENT_BODY: &str = "document_body";
pub const DOCUMENT_RAW: &str = "document_raw";
pub const THY_BEGIN: &str = "thy_begin";
pub const THY_END: &str = "thy_end";
pub const THY_DECL: &str = "thy_decl";
pub const THY_DECL_BLOCK: &str = "thy_decl_block";
pub const THY_DEFN: &str = "thy_defn";
pub const THY_STMT: &str = "thy_stmt";
pub const THY_LOAD: &str = "thy_load";
pub const THY_GOAL: &str = "thy_goal";
pub const THY_GOAL_DEFN: &str = "thy_goal_defn";
pub const THY_GOAL_STMT: &str = "thy_goal_stmt";
pub const QED: &str = "qed";
pub const QED_SCRIPT: &str = "qed_script";
pub const QED_BLOCK: &str = "qed_block";
pub const QED_GLOBAL: &str = "qed_global";
pub const PRF_GOAL: &str = "prf_goal";
pub const PRF_BLOCK: &str = "prf_block";
pub const NEXT_BLOCK: &str = "next_block";
pub const PRF_OPEN: &str = "prf_open";
pub const PRF_CLOSE: &str = "prf_close";
pub const PRF_CHAIN: &str = "prf_chain";
pub const PRF_DECL: &str = "prf_decl";
pub const PRF_ASM: &str = "prf_asm";
pub const PRF_ASM_GOAL: &str = "prf_asm_goal";
pub const PRF_SCRIPT: &str = "prf_script";
pub const PRF_SCRIPT_GOAL: &str = "prf_script_goal";
pub const PRF_SCRIPT_ASM_GOAL: &str = "prf_script_asm_goal";
pub const BEFORE_COMMAND: &str = "before_command";
pub const QUASI_COMMAND: &str = "quasi_command";

/// All command kinds.
pub const ALL_KINDS: &[&str] = &[
    DIAG,
    DOCUMENT_HEADING,
    DOCUMENT_BODY,
    DOCUMENT_RAW,
    THY_BEGIN,
    THY_END,
    THY_LOAD,
    THY_DECL,
    THY_DECL_BLOCK,
    THY_DEFN,
    THY_STMT,
    THY_GOAL,
    THY_GOAL_DEFN,
    THY_GOAL_STMT,
    QED,
    QED_SCRIPT,
    QED_BLOCK,
    QED_GLOBAL,
    PRF_GOAL,
    PRF_BLOCK,
    NEXT_BLOCK,
    PRF_OPEN,
    PRF_CLOSE,
    PRF_CHAIN,
    PRF_DECL,
    PRF_ASM,
    PRF_ASM_GOAL,
    PRF_SCRIPT,
    PRF_SCRIPT_GOAL,
    PRF_SCRIPT_ASM_GOAL,
];

// =========================================================================
// Keyword entry
// =========================================================================

/// An entry in the keyword table.
#[derive(Clone, Debug)]
pub struct KeywordEntry {
    pub kind: String,
    pub tags: Vec<String>,
}

impl KeywordEntry {
    pub fn new(kind: &str) -> Self {
        KeywordEntry {
            kind: kind.to_string(),
            tags: Vec::new(),
        }
    }

    pub fn with_tags(kind: &str, tags: Vec<String>) -> Self {
        KeywordEntry {
            kind: kind.to_string(),
            tags,
        }
    }
}

// =========================================================================
// Keywords table
// =========================================================================

/// The keyword table maps command names to their keyword entries.
/// Also maintains a set of "minor" keywords (like `::`, `=`, `where`, etc.)
/// that are not commands but are reserved.
#[derive(Clone, Debug, Default)]
pub struct Keywords {
    /// Command entries: name → entry.
    commands: HashMap<String, KeywordEntry>,
    /// Minor keywords (reserved words that are not commands).
    minors: Vec<String>,
}

impl Keywords {
    /// Create an empty keyword table.
    pub fn empty() -> Self {
        Keywords::default()
    }

    /// Create the standard Pure/HOL keywords table.
    pub fn standard() -> Self {
        let mut kw = Keywords::empty();

        // ── Theory-level commands ──
        kw.add_command("theory", THY_BEGIN);
        kw.add_command("end", THY_END);
        kw.add_command("imports", THY_LOAD); // not a command, but reserved
        kw.add_command("keywords", THY_LOAD);
        kw.add_command("abbrevs", THY_LOAD);
        kw.add_command("begin", THY_BEGIN);

        // Theory declarations
        kw.add_command("typedecl", THY_DECL);
        kw.add_command("type_synonym", THY_DECL);
        kw.add_command("nonterminal", THY_DECL);
        kw.add_command("judgment", THY_DECL);
        kw.add_command("consts", THY_DECL);
        kw.add_command("syntax", THY_DECL);
        kw.add_command("no_syntax", THY_DECL);
        kw.add_command("translations", THY_DECL);
        kw.add_command("no_translations", THY_DECL);
        kw.add_command("defs", THY_DECL);
        kw.add_command("declare", THY_DECL);
        kw.add_command("declaration", THY_DECL);
        kw.add_command("setup", THY_DECL);
        kw.add_command("local_setup", THY_DECL);
        kw.add_command("attribute_setup", THY_DECL);
        kw.add_command("method_setup", THY_DECL);
        kw.add_command("simproc_setup", THY_DECL);
        kw.add_command("ML_file", THY_DECL);
        kw.add_command("ML", THY_DECL);
        kw.add_command("oracle", THY_DECL);
        kw.add_command("bundle", THY_DECL);
        kw.add_command("unbundle", THY_DECL);
        kw.add_command("include", THY_DECL);
        kw.add_command("including", THY_DECL);
        kw.add_command("class", THY_DECL_BLOCK);
        kw.add_command("subclass", THY_DECL);
        kw.add_command("instantiation", THY_DECL_BLOCK);
        kw.add_command("overloading", THY_DECL_BLOCK);
        kw.add_command("context", THY_DECL_BLOCK);
        kw.add_command("locale", THY_DECL_BLOCK);
        kw.add_command("sublocale", THY_DECL);
        kw.add_command("interpretation", THY_DECL);
        kw.add_command("interpret", THY_DECL);
        kw.add_command("global_interpretation", THY_DECL);

        // Theory definitions
        kw.add_command("definition", THY_DEFN);
        kw.add_command("abbreviation", THY_DEFN);
        kw.add_command("type_notation", THY_DEFN);
        kw.add_command("no_type_notation", THY_DEFN);
        kw.add_command("notation", THY_DEFN);
        kw.add_command("no_notation", THY_DEFN);
        kw.add_command("axiomatization", THY_DEFN);
        kw.add_command("primrec", THY_DEFN);
        kw.add_command("fun", THY_DEFN);
        kw.add_command("function", THY_DEFN);
        kw.add_command("termination", THY_DEFN);
        kw.add_command("datatype", THY_DEFN);
        kw.add_command("codatatype", THY_DEFN);
        kw.add_command("record", THY_DEFN);
        kw.add_command("inductive", THY_DEFN);
        kw.add_command("coinductive", THY_DEFN);
        kw.add_command("inductive_set", THY_DEFN);
        kw.add_command("coinductive_set", THY_DEFN);
        kw.add_command("nominal_datatype", THY_DEFN);
        kw.add_command("quotient_type", THY_DEFN);
        kw.add_command("lift_definition", THY_DEFN);

        // Theory statements
        kw.add_command("lemmas", THY_STMT);
        kw.add_command("theorems", THY_STMT);
        kw.add_command("named_theorems", THY_STMT);

        // Theory goals (enter proof mode)
        kw.add_command("lemma", THY_GOAL);
        kw.add_command("theorem", THY_GOAL);
        kw.add_command("corollary", THY_GOAL);
        kw.add_command("proposition", THY_GOAL);
        kw.add_command("schematic_goal", THY_GOAL);

        // ── Proof-level commands ──
        kw.add_command("apply", PRF_SCRIPT);
        kw.add_command("apply_end", PRF_SCRIPT);
        kw.add_command("supply", PRF_SCRIPT);
        kw.add_command("subgoal", PRF_SCRIPT);
        kw.add_command("defer", PRF_SCRIPT);
        kw.add_command("prefer", PRF_SCRIPT);
        kw.add_command("back", PRF_SCRIPT);
        kw.add_command("sorry", QED_SCRIPT);
        kw.add_command("done", QED_SCRIPT);
        kw.add_command("by", QED_SCRIPT);

        // Proof block structure
        kw.add_command("proof", PRF_OPEN);
        kw.add_command("qed", QED_BLOCK);
        kw.add_command("{", PRF_OPEN);
        kw.add_command("}", PRF_CLOSE);

        // Structured proof commands
        kw.add_command("fix", PRF_ASM);
        kw.add_command("assume", PRF_ASM);
        kw.add_command("presume", PRF_ASM);
        kw.add_command("def", PRF_ASM);
        kw.add_command("let", PRF_DECL);
        kw.add_command("note", PRF_DECL);
        kw.add_command("from", PRF_CHAIN);
        kw.add_command("with", PRF_CHAIN);
        kw.add_command("using", PRF_DECL);
        kw.add_command("unfolding", PRF_DECL);
        kw.add_command("case", PRF_ASM_GOAL);
        kw.add_command("then", PRF_CHAIN);
        kw.add_command("also", PRF_CHAIN);
        kw.add_command("finally", PRF_CHAIN);
        kw.add_command("moreover", PRF_CHAIN);
        kw.add_command("ultimately", PRF_CHAIN);

        // Proof goals
        kw.add_command("have", PRF_GOAL);
        kw.add_command("show", PRF_GOAL);
        kw.add_command("hence", PRF_GOAL);
        kw.add_command("thus", PRF_GOAL);
        kw.add_command("obtain", PRF_ASM_GOAL);
        kw.add_command("guess", PRF_ASM_GOAL);

        // Next
        kw.add_command("next", NEXT_BLOCK);

        // ── Document-level commands ──
        kw.add_command("section", DOCUMENT_HEADING);
        kw.add_command("subsection", DOCUMENT_HEADING);
        kw.add_command("subsubsection", DOCUMENT_HEADING);
        kw.add_command("chapter", DOCUMENT_HEADING);
        kw.add_command("paragraph", DOCUMENT_HEADING);
        kw.add_command("subparagraph", DOCUMENT_HEADING);
        kw.add_command("text", DOCUMENT_BODY);
        kw.add_command("txt", DOCUMENT_BODY);
        kw.add_command("text_raw", DOCUMENT_RAW);

        // ── Diagnostic commands ──
        kw.add_command("value", DIAG);
        kw.add_command("print_theory", DIAG);
        kw.add_command("print_theorems", DIAG);
        kw.add_command("print_locales", DIAG);
        kw.add_command("print_classes", DIAG);
        kw.add_command("print_types", DIAG);
        kw.add_command("print_commands", DIAG);
        kw.add_command("thm", DIAG);
        kw.add_command("term", DIAG);
        kw.add_command("typ", DIAG);
        kw.add_command("prf", DIAG);
        kw.add_command("full_prf", DIAG);
        kw.add_command("pr", DIAG);
        kw.add_command("find_theorems", DIAG);
        kw.add_command("find_consts", DIAG);
        kw.add_command("help", DIAG);
        kw.add_command("welcome", DIAG);

        // ── Minor keywords (reserved, not commands) ──
        kw.add_minor("::");
        kw.add_minor("==");
        kw.add_minor("=>");
        kw.add_minor("==>");
        kw.add_minor("--->");
        kw.add_minor("where");
        kw.add_minor("for");
        kw.add_minor("is");
        kw.add_minor("and");
        kw.add_minor("if");
        kw.add_minor("in");
        kw.add_minor("rewrites");
        kw.add_minor("notes");
        kw.add_minor("defines");
        kw.add_minor("includes");
        kw.add_minor("fixes");
        kw.add_minor("constrains");
        kw.add_minor("assumes");
        kw.add_minor("shows");
        kw.add_minor("obtains");
        kw.add_minor("begin");
        kw.add_minor("overloaded");
        kw.add_minor("open");
        kw.add_minor("pervasive");
        kw.add_minor("structure");
        kw.add_minor("unchecked");
        kw.add_minor("no_vars");
        kw.add_minor("infix");
        kw.add_minor("infixl");
        kw.add_minor("infixr");
        kw.add_minor("binder");
        kw.add_minor("input");
        kw.add_minor("output");
        kw.add_minor("(structure)");
        kw.add_minor("(");
        kw.add_minor(")");
        kw.add_minor("[");
        kw.add_minor("]");
        kw.add_minor("|");
        kw.add_minor(".");
        kw.add_minor(";");
        kw.add_minor(":");

        kw
    }

    // ── Building ──

    /// Add a command keyword.
    pub fn add_command(&mut self, name: &str, kind: &str) {
        self.commands
            .insert(name.to_string(), KeywordEntry::new(kind));
    }

    /// Add a minor keyword.
    pub fn add_minor(&mut self, name: &str) {
        self.minors.push(name.to_string());
    }

    /// Merge two keyword tables (second wins on conflict).
    pub fn merge(&self, other: &Keywords) -> Keywords {
        let mut result = self.clone();
        for (k, v) in &other.commands {
            result.commands.insert(k.clone(), v.clone());
        }
        for m in &other.minors {
            if !result.minors.contains(m) {
                result.minors.push(m.clone());
            }
        }
        result
    }

    // ── Query ──

    /// Check if a string is any keyword (command or minor).
    pub fn is_keyword(&self, s: &str) -> bool {
        self.commands.contains_key(s) || self.minors.contains(&s.to_string())
    }

    /// Check if a string is a command keyword.
    pub fn is_command(&self, s: &str) -> bool {
        self.commands.contains_key(s)
    }

    /// Get the list of command names.
    pub fn command_names(&self) -> Vec<&String> {
        self.commands.keys().collect()
    }

    /// Get the kind of a command.
    pub fn command_kind(&self, name: &str) -> Option<&str> {
        self.commands.get(name).map(|e| e.kind.as_str())
    }

    /// Check if a command has a given kind.
    pub fn is_kind(&self, name: &str, kind: &str) -> bool {
        self.commands
            .get(name)
            .map(|e| e.kind == kind)
            .unwrap_or(false)
    }

    /// Check if a command belongs to a set of kinds.
    fn is_one_of_kinds(&self, name: &str, kinds: &[&str]) -> bool {
        self.commands
            .get(name)
            .map(|e| kinds.contains(&e.kind.as_str()))
            .unwrap_or(false)
    }

    // ── Category predicates ──

    pub fn is_vacuous(&self, name: &str) -> bool {
        self.is_one_of_kinds(name, &[DIAG, DOCUMENT_HEADING, DOCUMENT_BODY, DOCUMENT_RAW])
    }

    pub fn is_diag(&self, name: &str) -> bool {
        self.is_kind(name, DIAG)
    }

    pub fn is_document(&self, name: &str) -> bool {
        self.is_one_of_kinds(name, &[DOCUMENT_HEADING, DOCUMENT_BODY, DOCUMENT_RAW])
    }

    pub fn is_theory_begin(&self, name: &str) -> bool {
        self.is_kind(name, THY_BEGIN)
    }

    pub fn is_theory_end(&self, name: &str) -> bool {
        self.is_kind(name, THY_END)
    }

    pub fn is_theory(&self, name: &str) -> bool {
        self.is_one_of_kinds(
            name,
            &[
                THY_BEGIN,
                THY_END,
                THY_LOAD,
                THY_DECL,
                THY_DECL_BLOCK,
                THY_DEFN,
                THY_STMT,
                THY_GOAL,
                THY_GOAL_DEFN,
                THY_GOAL_STMT,
            ],
        )
    }

    pub fn is_theory_body(&self, name: &str) -> bool {
        self.is_one_of_kinds(
            name,
            &[
                THY_LOAD,
                THY_DECL,
                THY_DECL_BLOCK,
                THY_DEFN,
                THY_STMT,
                THY_GOAL,
                THY_GOAL_DEFN,
                THY_GOAL_STMT,
            ],
        )
    }

    pub fn is_proof(&self, name: &str) -> bool {
        self.is_one_of_kinds(
            name,
            &[
                QED,
                QED_SCRIPT,
                QED_BLOCK,
                QED_GLOBAL,
                PRF_GOAL,
                PRF_BLOCK,
                NEXT_BLOCK,
                PRF_OPEN,
                PRF_CLOSE,
                PRF_CHAIN,
                PRF_DECL,
                PRF_ASM,
                PRF_ASM_GOAL,
                PRF_SCRIPT,
                PRF_SCRIPT_GOAL,
                PRF_SCRIPT_ASM_GOAL,
            ],
        )
    }

    pub fn is_proof_open(&self, name: &str) -> bool {
        self.is_one_of_kinds(
            name,
            &[
                PRF_GOAL,
                PRF_ASM_GOAL,
                PRF_SCRIPT_GOAL,
                PRF_SCRIPT_ASM_GOAL,
                PRF_OPEN,
            ],
        )
    }

    pub fn is_proof_close(&self, name: &str) -> bool {
        self.is_one_of_kinds(name, &[QED, QED_SCRIPT, QED_BLOCK, PRF_CLOSE])
    }

    pub fn is_qed(&self, name: &str) -> bool {
        self.is_one_of_kinds(name, &[QED, QED_SCRIPT, QED_BLOCK])
    }

    pub fn is_qed_global(&self, name: &str) -> bool {
        self.is_kind(name, QED_GLOBAL)
    }

    pub fn is_theory_goal(&self, name: &str) -> bool {
        self.is_one_of_kinds(name, &[THY_GOAL, THY_GOAL_DEFN, THY_GOAL_STMT])
    }

    pub fn is_proof_goal(&self, name: &str) -> bool {
        self.is_one_of_kinds(name, &[PRF_GOAL, PRF_ASM_GOAL, PRF_SCRIPT_GOAL, PRF_SCRIPT_ASM_GOAL])
    }

    pub fn is_proof_asm(&self, name: &str) -> bool {
        self.is_one_of_kinds(name, &[PRF_ASM, PRF_ASM_GOAL])
    }

    pub fn is_proof_script(&self, name: &str) -> bool {
        self.is_one_of_kinds(name, &[PRF_SCRIPT, PRF_SCRIPT_GOAL, PRF_SCRIPT_ASM_GOAL])
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standard_keywords() {
        let kw = Keywords::standard();

        // Theory commands
        assert!(kw.is_theory_begin("theory"));
        assert!(kw.is_theory_end("end"));
        assert!(kw.is_theory("definition"));
        assert!(kw.is_theory("lemma"));

        // Proof commands
        assert!(kw.is_proof_open("proof"));
        assert!(kw.is_proof_close("qed"));
        assert!(kw.is_qed("done"));
        assert!(kw.is_proof("apply"));
        assert!(kw.is_proof_goal("have"));
        assert!(kw.is_proof_goal("show"));
        assert!(kw.is_proof_asm("fix"));
        assert!(kw.is_proof_asm("assume"));

        // Document
        assert!(kw.is_document("section"));
        assert!(kw.is_diag("value"));
        assert!(kw.is_vacuous("text"));

        // Theory goals
        assert!(kw.is_theory_goal("lemma"));
        assert!(kw.is_theory_goal("theorem"));
        assert!(!kw.is_theory_goal("fix"));
    }

    #[test]
    fn test_command_kind() {
        let kw = Keywords::standard();
        assert_eq!(kw.command_kind("lemma"), Some(THY_GOAL));
        assert_eq!(kw.command_kind("have"), Some(PRF_GOAL));
        assert_eq!(kw.command_kind("fix"), Some(PRF_ASM));
        assert_eq!(kw.command_kind("done"), Some(QED_SCRIPT));
        assert_eq!(kw.command_kind("nonexistent"), None);
    }

    #[test]
    fn test_is_keyword() {
        let kw = Keywords::standard();
        assert!(kw.is_keyword("lemma"));
        assert!(kw.is_keyword("::"));
        assert!(kw.is_keyword("where"));
        assert!(!kw.is_keyword("xyz123"));
    }

    #[test]
    fn test_merge() {
        let mut kw1 = Keywords::empty();
        kw1.add_command("foo", THY_DECL);

        let mut kw2 = Keywords::empty();
        kw2.add_command("bar", PRF_SCRIPT);

        let merged = kw1.merge(&kw2);
        assert!(merged.is_command("foo"));
        assert!(merged.is_command("bar"));
    }
}
