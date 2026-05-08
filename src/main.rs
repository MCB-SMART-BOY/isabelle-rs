//! Isabelle-rs: A modern reimplementation of the Isabelle proof assistant in Rust.
//!
//! ## Modes
//!
//! - **Demo mode** (default): Showcases the trusted kernel, type system, and terms.
//! - **LSP mode** (`--lsp`): Runs as a Language Server Protocol server for editors.
//!
//! ## Architecture
//!
//! ```text
//! isabelle-rs
//! ├── core/          Trusted kernel (LCF architecture)
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
mod server;

mod isar;
mod hol;

use core::{Sort, Term, ThmKernel, Typ, CTerm};
use fleche::engine::{Fleche, RealExecutor};
use server::IsabelleServer;
use std::sync::Arc;

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
    eprintln!("║  Isabelle-rs LSP Server                    ║");
    eprintln!("║  Language Server Protocol for Isabelle     ║");
    eprintln!("╚══════════════════════════════════════════════╝");

    let executor = Arc::new(RealExecutor::new());
    let fleche = Arc::new(Fleche::new(executor));
    let mut server = IsabelleServer::new(fleche);

    server.run();
}

/// Run in demo mode (showcases the kernel).
fn run_demo() {
    let _ = tracing_subscriber::fmt::try_init();
    println!("╔══════════════════════════════════════════════╗");
    println!("║  Isabelle-rs: Isabelle Kernel in Rust       ║");
    println!("║  A modern proof assistant with LSP support  ║");
    println!("╠══════════════════════════════════════════════╣");
    println!("║  Run with --lsp to start LSP server         ║");
    println!("╚══════════════════════════════════════════════╝\n");

    demo_types();
    demo_terms();
    demo_kernel();
    demo_isabelle();
    demo_document();
    demo_fleche();
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
    let thm_a = ThmKernel::assume(a.clone());
    println!("Assume: {thm_a}");

    let t = CTerm::certify(Term::const_("t", Typ::dummy()));
    let thm_refl = ThmKernel::reflexive(t);
    println!("Reflexive: {thm_refl}");

    println!("✅ The trusted kernel is operational!");
    println!("   All theorems must be constructed through ThmKernel.");
    println!("   The LCF architecture guarantees soundness.");
    println!();
}


fn demo_isabelle() {
    use core::{Theory, Signature, ProofContext, CTerm, ThmKernel, Term, Typ};

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
    println!("  Inherited Pure.imp: {:?}", thy.const_type("Pure.imp").unwrap());
    println!("  Own MyTheory.zero: {:?}", thy.const_type("MyTheory.zero").unwrap());
    assert!(thy.is_declared("Pure.all"));  // inherited
    assert!(thy.is_declared("MyTheory.zero")); // own

    // 3. Prove a theorem and store it
    let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
    let trivial = ThmKernel::trivial(a);
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

fn demo_document() {
    println!("─── Document Model (Incremental Checking) ───");

    use document::Document;

    let mut doc = Document::new();
    let uri = "file:///test.thy";

    doc.open_file(uri.into(), "theory Test\nlemma foo: True\n  by auto".into());

    let node = doc.get_node(uri).unwrap();
    println!("Opened file: {uri}");
    println!("  Version: {}", node.version);
    println!("  Commands: {}", node.commands.len());
    for cmd in &node.commands {
        println!("    [{cmd_id}] {kind:?}: {src}",
            cmd_id = cmd.id,
            kind = cmd.kind,
            src = &cmd.source[..cmd.source.len().min(50)]);
    }

    // Simulate an edit: change "by auto" to "proof ... qed"
    let result = doc.update_file(
        uri,
        "theory Test\nlemma foo: True\nproof\n  auto\nqed".into(),
    ).unwrap();
    println!("Updated: fork_point={}, snapshots_kept={}",
        result.fork_point, result.snapshots_kept);
    println!();
}

fn demo_fleche() {
    println!("─── Flèche: Incremental Checking Engine ───");

    let engine = Fleche::new(Arc::new(RealExecutor::new()));

    // Check a valid file
    let diags = engine.open_file(
        "file:///good.thy",
        "theory Good\nlemma A: True\nproof\n  auto\ndone",
    );
    println!("Valid file: {} diagnostics", diags.len());

    // Check a file with errors (nested lemma)
    let diags = engine.open_file(
        "file:///bad.thy",
        "theory Bad\nlemma A: True\nlemma B: False",
    );
    println!("Bad file: {} diagnostics", diags.len());
    for d in &diags {
        if d.severity == Some(server::lsp_types::DiagnosticSeverity::Error) {
            println!("  ❌ {}", d.message);
        }
    }
    println!();
}

fn demo_lsp() {
    println!("─── LSP Protocol Support ───");

    println!("Supported LSP features:");
    println!("  ✅ initialize / shutdown");
    println!("  ✅ textDocument/didOpen / didChange / didClose / didSave");
    println!("  ✅ textDocument/publishDiagnostics");
    println!("  ✅ textDocument/hover");
    println!("  🚧 textDocument/completion");
    println!("  🚧 textDocument/definition");
    println!("  ✅ isabelle/proofGoals (extension)");
    println!();

    println!("─── Comparison: Isabelle PIDE vs LSP ───");
    println!("┌──────────────────┬─────────────────────┬──────────────────┐");
    println!("│ Feature          │ Isabelle PIDE       │ Isabelle-rs LSP  │");
    println!("├──────────────────┼─────────────────────┼──────────────────┤");
    println!("│ Protocol         │ Custom XML/YXML     │ Standard LSP     │");
    println!("│ Transport        │ Pipe (Poly/ML)      │ JSON-RPC/stdio   │");
    println!("│ Editors          │ jEdit, VSCode ★     │ ANY LSP editor   │");
    println!("│ Incremental      │ ✅ Snapshot-based   │ ✅ Snapshot-based │");
    println!("│ Async checking   │ ✅                  │ ✅                │");
    println!("│ Error recovery   │ Limited             │ ✅ Admit-based    │");
    println!("│ Goal display     │ ✅ Output panel     │ ✅ via LSP ext    │");
    println!("│ Hover types      │ ✅                  │ ✅                │");
    println!("│ Go-to-def        │ ✅ Hyperlinks       │ 🚧 WIP            │");
    println!("└──────────────────┴─────────────────────┴──────────────────┘");
    println!();

    println!("🚀 Run `isabelle-rs --lsp` to start the LSP server.");
    println!("   Configure your editor to use it as the Isabelle language server.");
}
