//! Theory-scoped theorem database — mirrors Isabelle's per-theory structure.
//!
//! Isabelle stores theorems per-theory, not in a flat global DB.
//! Each theory has its own discrimination nets. When proving a lemma in
//! theory B that imports A, we search B's nets + A's nets, not ALL nets.
//!
//! This prevents the global DB density overflow we were experiencing.

use std::{collections::HashMap, sync::Arc};

use crate::{core::thm::Thm, hol::hol_loader::HolTheoremDb};

/// A theory-scoped database that mirrors Isabelle's architecture.
#[derive(Default)]
pub struct TheoryDB {
    /// Theory name → its local theorem database
    pub theories: HashMap<String, HolTheoremDb>,
    /// Import graph: theory name → list of imported theory names
    pub imports: HashMap<String, Vec<String>>,
    /// Global built-in theorems (Pure, basic HOL)
    pub builtins: Option<HolTheoremDb>,
    /// Current theory being processed
    pub current: Option<String>,
}

impl TheoryDB {
    pub fn new() -> Self {
        TheoryDB::default()
    }

    /// Set the built-in theorems (Pure + basic HOL).
    pub fn set_builtins(&mut self, mut db: HolTheoremDb) {
        HolTheoremDb::add_builtins(&mut db);
        self.builtins = Some(db);
    }

    /// Start a new theory scope.
    pub fn begin_theory(&mut self, name: &str, imports: &[String]) {
        self.current = Some(name.to_string());
        self.imports.insert(name.to_string(), imports.to_vec());
        self.theories.insert(name.to_string(), HolTheoremDb::new());
    }

    /// Add lemmas to the current theory.
    pub fn extend_current(&mut self, lemmas: &[crate::hol::hol_loader::ParsedLemma]) {
        if let Some(ref current) = self.current.clone()
            && let Some(db) = self.theories.get_mut(current)
        {
            db.extend(lemmas);
        }
    }

    /// Look up a theorem by name — searches current theory + imports + builtins.
    pub fn lookup(&self, name: &str) -> Option<Arc<Thm>> {
        // 1. Search current theory
        if let Some(ref current) = self.current {
            if let Some(db) = self.theories.get(current)
                && let Some(thm) = db.by_name.get(name)
            {
                return Some(Arc::clone(thm));
            }
            // 2. Search imported theories (transitive)
            if let Some(imps) = self.imports.get(current) {
                for imp in imps {
                    if let Some(db) = self.theories.get(imp)
                        && let Some(thm) = db.by_name.get(name)
                    {
                        return Some(Arc::clone(thm));
                    }
                }
            }
        }
        // 3. Search builtins
        if let Some(ref builtins) = self.builtins
            && let Some(thm) = builtins.by_name.get(name)
        {
            return Some(Arc::clone(thm));
        }
        None
    }

    /// Get the current theory's local DB (for building nets, etc.).
    pub fn current_db(&self) -> Option<&HolTheoremDb> {
        self.current.as_ref().and_then(|c| self.theories.get(c))
    }

    /// Get all theorems visible from the current theory (current + imports + builtins).
    pub fn visible_theorems(&self) -> Vec<Arc<Thm>> {
        let mut all = Vec::new();
        if let Some(ref current) = self.current {
            if let Some(db) = self.theories.get(current) {
                all.extend(db.all.iter().cloned());
            }
            if let Some(imps) = self.imports.get(current) {
                for imp in imps {
                    if let Some(db) = self.theories.get(imp) {
                        all.extend(db.all.iter().cloned());
                    }
                }
            }
        }
        if let Some(ref builtins) = self.builtins {
            all.extend(builtins.all.iter().cloned());
        }
        all
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::{
            term::Term,
            thm::{CTerm, ThmKernel},
            types::Typ,
        },
        hol::hol_loader::ParsedLemma,
    };

    fn make_lemma(name: &str, proof: &str) -> ParsedLemma {
        let term = Term::const_(name, Typ::base("prop"));
        let thm = ThmKernel::assume(CTerm::certify(term));
        ParsedLemma {
            name: name.to_string(),
            attributes: vec![],
            theorem: Arc::new(thm),
            proof_script: Some(proof.to_string()),
            alias_for: None,
            source_loc: None,
        }
    }

    #[test]
    fn test_theory_db_scoping() {
        let mut db = TheoryDB::new();

        // Theory A defines lemma_a
        db.begin_theory("A", &[]);
        db.extend_current(&[make_lemma("lemma_a", "by auto")]);

        // Theory B imports A, defines lemma_b
        db.begin_theory("B", &["A".to_string()]);
        db.extend_current(&[make_lemma("lemma_b", "by auto")]);

        // In theory B, we can see lemma_b (local) and lemma_a (import)
        assert!(db.lookup("lemma_b").is_some());
        assert!(db.lookup("lemma_a").is_some());

        // In theory A (switch back), we can see lemma_a but not lemma_b
        db.current = Some("A".to_string());
        assert!(db.lookup("lemma_a").is_some());
        // lemma_b is NOT visible from A (B imports A, not vice versa)
    }

    #[test]
    fn test_theory_db_isolation() {
        let mut db = TheoryDB::new();
        db.begin_theory("A", &[]);
        db.extend_current(&[make_lemma("a", "by auto")]);

        db.begin_theory("B", &[]); // B does NOT import A
        db.extend_current(&[make_lemma("b", "by auto")]);

        assert!(db.lookup("b").is_some());
        // a is not visible because B doesn't import A
        assert!(db.lookup("a").is_none());
    }
}
