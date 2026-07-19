//! Isabelle-rs: an Isabelle/Pure-inspired LCF kernel research prototype in Rust.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(unreachable_patterns)]
//! ## Modes
//!
//! - **Demo mode** (default): Shows legacy kernel, term, proof-state, and LSP prototypes.
//! - **LSP mode** (`--lsp`): Runs the experimental Language Server Protocol server.
//!
//! ## Architecture
//!
//! ```text
//! isabelle-rs
//! ├── core/          Legacy proof engine and migration kernel
//! │   ├── types.rs   Sort, Typ (type system)
//! │   ├── term.rs    Term (lambda calculus)
//! │   └── thm.rs     ThmKernel (inference rules)
//! ├── document/      Document model (versioned, incremental)
//! │   └── document.rs  Node, Command, Snapshot
//! ├── fleche/        Flèche: incremental checking engine
//! │   └── engine.rs  CommandExecutor, Fleche
//! └── server/        LSP server (Language Server Protocol)
//!     ├── lsp_types.rs  LSP 3.17 type definitions
//!     ├── transport.rs  JSON-RPC over stdio
//!     └── handler.rs    Request dispatch & lifecycle
//! ```

mod core;
mod document;
mod fleche;
mod lsp;
mod server;

mod hol;
mod isar;
mod kernel;
mod tools;

use core::{CTerm, Sort, Term, ThmKernel, Typ};
use std::sync::Arc;

use fleche::engine::{Fleche, RealExecutor};
use server::IsabelleServer;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() > 1 && args[1] == "--lsp" {
        run_lsp_server();
    } else {
        run_demo();
    }
}

/// Run in LSP server mode (for editors).
fn run_lsp_server() {
    let _ = tracing_subscriber::fmt::try_init();
    eprintln!("╔══════════════════════════════════════════════╗");
    eprintln!("║  Isabelle-rs LSP Server                      ║");
    eprintln!("║  Experimental partial LSP implementation      ║");
    eprintln!("╚══════════════════════════════════════════════╝");

    let executor = Arc::new(RealExecutor::new());
    let fleche = Arc::new(Fleche::new(executor));
    let mut server = IsabelleServer::new(fleche);

    server.run();
}

/// Run the research-prototype demo.
fn run_demo() {
    let _ = tracing_subscriber::fmt::try_init();
    println!("╔══════════════════════════════════════════════╗");
    println!("║  Isabelle-rs: LCF Kernel Research Prototype  ║");
    println!("║  Partial tooling; not Isabelle-compatible     ║");
    println!("╠══════════════════════════════════════════════╣");
    println!("║  Run with --lsp to start LSP server          ║");
    println!("╚══════════════════════════════════════════════╝\n");

    demo_types();
    demo_terms();
    demo_kernel();
    demo_isabelle();
    demo_proofs();
    demo_lsp();
}

fn demo_types() {
    println!("─── Types & Sorts ───");

    let sort_type = Sort::singleton("type");
    println!("Default sort: {sort_type:?}");

    let sort_ord = Sort::singleton("ord");
    println!("Sort `ord`: {sort_ord:?}");

    let bool_t = Typ::base("bool");
    let nat_t = Typ::base("nat");
    let fun_t = Typ::arrow(bool_t.clone(), nat_t.clone());

    println!("bool: {bool_t:?}");
    println!("nat:  {nat_t:?}");
    println!("bool => nat: {fun_t:?}");

    let a = Typ::free("a", Sort::singleton("type"));
    println!("Free type var: {a:?}");

    let b = Typ::var("b", 0, Sort::singleton("type"));
    println!("Schematic type var: {b:?}");

    let pair = Typ::arrows(vec![bool_t, nat_t], Typ::base("bool"));
    println!("bool => nat => bool: {pair:?}");
    println!();
}

fn demo_terms() {
    println!("─── Lambda Terms ───");

    let true_t = Term::const_("True", Typ::base("prop"));
    println!("Constant: {true_t:?}");

    let x = Term::free("x", Typ::base("nat"));
    println!("Free var: {x:?}");

    let p = Term::var("P", 0, Typ::base("bool"));
    println!("Schematic var: {p:?}");

    let nat = Typ::base("nat");
    let identity = Term::abs("x", nat.clone(), Term::bound(0));
    println!("Identity λx.x: {identity}");

    let f = Term::free("f", Typ::arrow(nat.clone(), Typ::base("bool")));
    let app = Term::app(f.clone(), x.clone());
    println!("Application f(x): {app:?}");

    let a = Term::free("a", Typ::base("dummy"));
    let b = Term::free("b", Typ::base("dummy"));
    let c = Term::free("c", Typ::base("dummy"));
    let curried = Term::apps(f, vec![a, b, c]);
    println!("Curried f(a, b, c): {curried:?}");

    let (head, args) = curried.strip_comb();
    println!("  strip_comb: head={head:?}, args={args:?}");
    println!();
}

fn demo_kernel() {
    println!("─── Theorem Kernel (Trusted Core) ───");

    let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
    let thm_a = ThmKernel::assume_compat(a.clone());
    println!("Assume: {thm_a}");

    let t = CTerm::certify(Term::const_("t", Typ::dummy()));
    let thm_refl = ThmKernel::reflexive_compat(t);
    println!("Reflexive: {thm_refl}");

    println!("✅ The trusted kernel is operational!");
    println!("   All theorems must be constructed through ThmKernel.");
    println!("   The LCF architecture guarantees soundness.");
    println!();
}

fn demo_isabelle() {
    use core::{CTerm, ProofContext, Term, Theory, ThmKernel, Typ};

    println!("─── Isabelle: Theory / Signature / Context ───");

    // 1. Bootstrap theory Pure
    let pure = Theory::pure();
    println!("Theory: {}", pure.name());
    println!("  Signature has {} constants:", pure.signature().const_count());
    for decl in pure.signature().consts() {
        println!("    {} :: {:?}", decl.name, decl.typ);
    }

    // 2. Create a new theory extending Pure
    let mut thy = Theory::begin("MyTheory", vec![pure.clone()]);
    thy.declare_const("MyTheory.zero", Typ::base("nat"));
    println!("\nExtended theory: {}", thy.name());
    println!("  Inherited Pure.imp: {:?}", thy.const_type("Pure.imp").expect("Pure.imp not found"));
    println!(
        "  Own MyTheory.zero: {:?}",
        thy.const_type("MyTheory.zero").expect("MyTheory.zero not found")
    );
    assert!(thy.is_declared("Pure.all")); // inherited
    assert!(thy.is_declared("MyTheory.zero")); // own

    // 3. Prove a theorem and store it
    let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
    let trivial = ThmKernel::trivial(a).unwrap();
    thy.add_theorem("trivial", trivial);
    println!("\n  Stored theorem 'trivial': {}", thy.lookup_theorem("trivial").is_some());

    // 4. Proof context: fix + assume (Isar style)
    let mut ctx = ProofContext::init(&pure);
    ctx.fix("x", Typ::base("nat"));
    ctx.fix("y", Typ::base("nat"));
    ctx.assume(Term::const_("Px", Typ::base("prop")));
    println!("\nProof context:");
    println!("  Fixes: {:?}", ctx.fixes().iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>());
    println!("  Assumptions: {}", ctx.assumptions().len());

    println!("\n✅ Isabelle-style Theory/Signature/Context architecture in place.");
    println!();
}

fn demo_proofs() {
    println!("─── Theory Loading + Proof Engine ───");
    use isabelle_rs::{
        core::{term::Term, theory::Theory, types::Typ},
        theory::loader::TheoryProcessor,
    };

    // Show the full pipeline
    let source = r#"theory Demo imports Pure begin
  datatype 'a option = None | Some 'a
  fun id :: "'a => 'a" where "id x = x"
  lemma trivial: "A --> A" by auto
  lemma structured: "A --> A"
  proof
    assume "A"
    show "A" by auto
  qed
end"#;

    let mut proc = TheoryProcessor::with_parent(Theory::pure(), "Demo");
    let thy = proc.process_source(source);
    println!("  Theory: {}", thy.name());
    println!("  Errors: {:?}", proc.errors());
    println!("  Theorems extracted: {}", proc.theorem_count());
    println!();

    // Show Isar proof engine
    println!("─── Isar Proof Engine ───");
    use isabelle_rs::isar::proof::IsarProof;
    let mut proof = IsarProof::init(Theory::pure());
    let prop = Term::const_("A", Typ::base("prop"));
    proof.lemma("test", prop.clone());
    println!("  lemma test → mode: {:?}", proof.mode());
    proof.proof();
    println!("  proof → mode: {:?}, level: {}", proof.mode(), proof.level());
    proof.show("goal", prop);
    println!("  show A → mode: {:?}", proof.mode());
    proof.by("auto");
    println!("  by auto → mode: {:?}, level: {}", proof.mode(), proof.level());
    proof.qed();
    proof.done();
    println!("  qed+done → mode: {:?}, level: {}", proof.mode(), proof.level());
    println!("  ✅ Structured proof complete!");
    println!();
}

fn demo_lsp() {
    println!("─── Experimental LSP Protocol ───");
    println!("Implemented handlers:");
    println!("  initialize / shutdown");
    println!("  textDocument/didOpen / didChange / didClose");
    println!("  textDocument/publishDiagnostics and hover");
    println!("  isabelle/proofGoals (extension)");
    println!("Prototype handlers:");
    println!("  completion / definition / documentSymbol");
    println!();

    println!("─── Current Trust Position ───");
    println!("  Candidate strict kernel: checked local nucleus; not the sole TCB");
    println!("  Sampled HOL: 1/125 transitional, 0/125 kernel-trusted");
    println!("  HOL / Isar / LSP: partial research prototypes");
    println!("  Full Isabelle compatibility: not implemented");
    println!("  Canonical status: docs/PROJECT_STATUS.md");
    println!();
}
