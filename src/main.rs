//! Isabelle-rs: an Isabelle/Pure-inspired LCF kernel research prototype in Rust.
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
//! │   └── model.rs     Node, Command, Snapshot
//! ├── fleche/        Flèche: incremental checking engine
//! │   └── engine.rs  CommandExecutor, Fleche
//! └── server/        LSP server (Language Server Protocol)
//!     ├── lsp_types.rs  LSP 3.17 type definitions
//!     ├── transport.rs  JSON-RPC over stdio
//!     └── handler.rs    Request dispatch & lifecycle
//! ```

use std::{
    io::{self, Write},
    sync::{
        Arc,
        mpsc::{self, SyncSender, TrySendError},
    },
};

use isabelle_rs::{
    core::{Sort, Term, Typ},
    fleche::engine::{Fleche, RealExecutor},
    server::IsabelleServer,
};

const LOG_QUEUE_CAPACITY: usize = 64;
const MAX_LOG_FRAGMENT_BYTES: usize = 4096;

#[derive(Clone)]
struct NonblockingLogWriter {
    sender: SyncSender<Vec<u8>>,
}

impl Write for NonblockingLogWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let fragment = bytes[..bytes.len().min(MAX_LOG_FRAGMENT_BYTES)].to_vec();
        match self.sender.try_send(fragment) {
            Ok(()) | Err(TrySendError::Full(_)) => Ok(bytes.len()),
            Err(TrySendError::Disconnected(_)) => {
                Err(io::Error::new(io::ErrorKind::BrokenPipe, "LSP log sink stopped"))
            },
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn start_lsp_logging() -> io::Result<()> {
    let (sender, receiver) = mpsc::sync_channel::<Vec<u8>>(LOG_QUEUE_CAPACITY);
    std::thread::spawn(move || {
        let stderr = io::stderr();
        for fragment in receiver {
            if stderr.lock().write_all(&fragment).is_err() {
                break;
            }
        }
    });
    let writer = NonblockingLogWriter { sender };
    tracing_subscriber::fmt()
        .with_writer(move || writer.clone())
        .with_ansi(false)
        .try_init()
        .map_err(|error| io::Error::other(format!("failed to initialize LSP logging: {error}")))
}

fn main() -> std::process::ExitCode {
    match isabelle_rs::ml::host::solver::run_launcher_if_requested() {
        Ok(Some(code)) => {
            return u8::try_from(code)
                .map_or(std::process::ExitCode::FAILURE, std::process::ExitCode::from);
        },
        Ok(None) => {},
        Err(error) => {
            eprintln!("Solver launcher failed: {error}");
            return std::process::ExitCode::FAILURE;
        },
    }
    if std::env::args().nth(1).as_deref() == Some("--compute-worker") {
        return match isabelle_rs::compute_worker::run_stdio() {
            Ok(()) => std::process::ExitCode::SUCCESS,
            Err(_) => std::process::ExitCode::FAILURE,
        };
    }
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 && args[1] == "--lsp" {
        if let Err(error) = run_lsp_server() {
            tracing::error!("LSP server stopped: {error}");
            return std::process::ExitCode::FAILURE;
        }
    } else {
        run_demo();
    }
    std::process::ExitCode::SUCCESS
}

/// Run in LSP server mode (for editors).
fn run_lsp_server() -> std::io::Result<()> {
    start_lsp_logging()?;

    let executor = Arc::new(RealExecutor::new());
    let fleche = Arc::new(Fleche::new(executor));
    let worker_executable = std::env::current_exe().map_err(|error| {
        io::Error::new(error.kind(), format!("locating LSP compute executable: {error}"))
    })?;
    let mut server = IsabelleServer::new(fleche, worker_executable);

    server.run()
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

    let f = Term::free(
        "f",
        Typ::arrow(
            nat.clone(),
            Typ::arrow(nat.clone(), Typ::arrow(nat.clone(), Typ::base("bool"))),
        ),
    );
    let app = Term::app(f.clone(), x.clone());
    println!("Application f(x): {app:?}");

    let a = Term::free("a", nat.clone());
    let b = Term::free("b", nat.clone());
    let c = Term::free("c", nat);
    let curried = Term::apps(f, vec![a, b, c]);
    println!("Curried f(a, b, c): {curried:?}");

    let (head, args) = curried.strip_comb();
    println!("  strip_comb: head={head:?}, args={args:?}");
    println!();
}

fn demo_kernel() {
    use isabelle_rs::{isar::source_ast::SourceId, theory::trusted_loader::compile_trusted_source};

    println!("─── Strict Kernel: Source-backed Theorem ───");
    let source = include_str!("../tests/fixtures/TrustedPureIdentity.thy");
    match compile_trusted_source(source, SourceId::new("TrustedPureIdentity.thy")) {
        Ok(result) => println!("KernelTrustedClosed: {}", result.theorem.name()),
        Err(error) => eprintln!("Strict source proof failed: {error}"),
    }
    println!();
}

fn demo_isabelle() {
    use isabelle_rs::core::types::TypeEnv;
    use isabelle_rs::core::{CTerm, ProofContext, Term, Theory, ThmKernel, Typ};

    println!("─── Isabelle: Theory / Signature / Context ───");

    // 1. Bootstrap theory Pure
    let pure = Theory::pure();
    println!("Theory: {}", pure.name());
    println!("  Signature has {} constants:", pure.signature().const_count());
    for decl in pure.signature().consts() {
        println!("    {} :: {:?}", decl.name, decl.typ);
    }

    // 2. Create a new theory extending Pure
    let mut thy = match Theory::begin("MyTheory", vec![pure.clone()]) {
        Ok(theory) => theory,
        Err(error) => {
            eprintln!("Cannot create demo theory: {error}");
            return;
        },
    };
    thy.declare_const("MyTheory.zero", Typ::base("nat"));
    println!("\nExtended theory: {}", thy.name());
    println!("  Inherited Pure.imp: {:?}", thy.const_type("Pure.imp").expect("Pure.imp not found"));
    println!(
        "  Own MyTheory.zero: {:?}",
        thy.const_type("MyTheory.zero").expect("MyTheory.zero not found")
    );
    assert!(thy.is_declared("Pure.all")); // inherited
    assert!(thy.is_declared("MyTheory.zero")); // own

    // Legacy theory storage remains transitional, not a TrustedTheorem.
    let prop = Typ::base("prop");
    let mut env = TypeEnv::new();
    env.declare_const("A", prop.clone());
    thy.declare_const("A", prop.clone());
    let a = CTerm::certify_checked(Term::const_("A", prop), &env)
        .expect("demo constant must be checked");
    let trivial = ThmKernel::trivial(a).expect("demo identity must be derivable");
    thy.add_theorem("trivial", trivial);
    println!("\n  Transitional theorem stored: {}", thy.lookup_theorem("trivial").is_some());

    // 4. Proof context: fix + assume (Isar style)
    let mut ctx = ProofContext::init(&pure);
    ctx.fix("x", Typ::base("nat"));
    ctx.fix("y", Typ::base("nat"));
    ctx.assume(Term::const_("Px", Typ::base("prop")));
    println!("\nProof context:");
    println!("  Fixes: {:?}", ctx.fixes().iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>());
    println!("  Assumptions: {}", ctx.assumptions().len());

    println!("\nLegacy theory/context API demo; not a trusted-theorem acceptance path.");
    println!();
}

fn demo_proofs() {
    println!("─── Legacy Theory Declarations + Isar State ───");
    use isabelle_rs::theory::{loader::TheoryProcessor, registry::TheoryRegistry};

    // Complete legacy loading supports declarations only where implemented.
    let source = "theory Demo imports Pure begin typedecl demo_type end";

    let mut proc = TheoryProcessor::for_theory(TheoryRegistry::new(), "Demo");
    match proc.process_source(source) {
        Ok(theory) => println!("  Theory: {}", theory.name()),
        Err(errors) => eprintln!("  Theory loading failed: {errors:?}"),
    }
    println!("  Errors: {:?}", proc.errors());
    println!("  Legacy theorem entries (not kernel-trusted): {}", proc.theorem_count());
    println!();

    // Show Isar proof engine
    println!("─── Isar Proof Engine ───");
    match demo_legacy_identity() {
        Ok(theorem) => println!(
            "  Checked legacy identity: {:?}; no TrustedTheorem produced.",
            theorem.prop().term(),
        ),
        Err(error) => eprintln!("  Legacy proof failed: {error}"),
    }
    println!();
}

fn demo_legacy_identity() -> Result<
    std::sync::Arc<isabelle_rs::core::thm::Thm>,
    isabelle_rs::isar::proof_result::GoalExportError,
> {
    use isabelle_rs::{
        core::{logic::Pure, term::Term, theory::Theory, types::Typ},
        isar::proof::IsarProof,
    };
    let mut proof = IsarProof::init(Theory::pure());
    proof.fix(&[("A", Typ::base("prop"))])?;
    let proposition = Term::free("A", Typ::base("prop"));
    proof.lemma("identity", Pure::mk_implies(proposition.clone(), proposition.clone()))?;
    proof.proof()?;
    proof.assume(std::slice::from_ref(&proposition))?;
    proof.show("goal", proposition)?;
    proof.by("assumption", &isabelle_rs::hol::hol_loader::HolTheoremDb::new())?;
    proof.qed()?;
    proof.close_lemma()
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
    println!("  Isolated strict kernel: accepted-theorem TCB; legacy search remains separate");
    println!("  Sampled HOL: run cargo +stable xtask core for current trust counts");
    println!("  HOL / Isar / LSP: partial research prototypes");
    println!("  Full Isabelle compatibility: not implemented");
    println!("  Canonical status: docs/status/PROJECT_STATUS.md");
    println!();
}
