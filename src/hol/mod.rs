//! HOL — Higher-Order Logic built on Pure.
//!
//! Corresponds to `src/HOL/` in the Isabelle distribution.
//!
//! HOL is the most-used object logic in Isabelle.
//! It defines `bool`, connectives, quantifiers, and equality.
pub mod axclass;
pub mod defs;
pub mod hologic;
pub mod simpdata;
pub mod bnf_lfp;
pub mod class_system;
pub mod ctr_sugar;
pub mod function;
pub mod hol_consts;
pub mod hol_loader;
pub mod hol_rules;
pub mod hol_theorems;
pub mod inductive;
pub mod inductive_set;
pub mod locale;
pub mod primcorec;
pub mod theory_db;
pub mod theory_graph;
pub mod transfer;
pub mod typedef_record;
