# Isabelle-rs v1.8.1

> **Isabelle proof assistant kernel and Isar proof engine — Rust rewrite**
>
> LCF trusted kernel · 27 proof methods · HOL simplifier · Fourier-Motzkin arithmetic · Meson + Metis + Sledgehammer
> **0 warnings · 694+ tests · 5/5 core files 100% verified · 125/125 theorems**

---

## Overview

isabelle-rs rewrites the Isabelle proof assistant's core in Rust: the LCF trusted kernel and Isar structured proof language. It tracks the Isabelle/ML source, preserving full LCF safety while leveraging Rust's type system, ownership model, and zero-cost abstractions.

### Key Features

| Feature | Description |
|---------|-------------|
| **LCF Trusted Kernel** | 15 primitive rules + tpairs/shyps, 0 Typ::dummy() fallback |
| **Isar Proof Engine** | 3-mode state machine (Forward/Chain/Backward), 30+ commands |
| **Proof Methods** | 27 (simp/auto/blast/fast/best/arith/metis/meson/etc.) |
| **HOL Simplifier** | Conditional rewriting + Solver plugins (ArithSolver/AsmSolver) |
| **FM Arithmetic** | Fourier-Motzkin variable elimination (nat/int linear) |
| **BNF Lfp/Gfp** | induction/coinduction/fold/rec/unfold/corec + map/set/rel/pred |
| **Ctr_Sugar** | case/disc/sel/split/cong/nchotomy/size theorem generation |
| **Metis/Meson** | Model elimination + resolution prover + SAT (DPLL/CDCL) |
| **Sledgehammer** | ATP invocation framework + TSTP proof reconstruction |
| **Performance** | Kernel ops 179ns-12us (release mode, criterion) |

---

## Quick Start

```bash
git clone https://github.com/MCB-SMART-BOY/isabelle-rs
cd isabelle-rs

cargo build
cargo test --lib                              # Unit tests
RUST_MIN_STACK=268435456 cargo test --lib     # Full tests (incl. verification)
cargo bench
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL --stats
```

Requires: Rust nightly (edition 2024), 256MB+ stack recommended

---

## Verification Results

### Tier 0 — Core (5/5 files, 125/125 theorems, 100%)

| File | Lemmas | Rate |
|------|:--:|:--:|
| HOL.thy | 25/25 | 100% |
| Orderings.thy | 25/25 | 100% |
| Set.thy | 25/25 | 100% |
| Nat.thy | 25/25 | 100% |
| List.thy | 25/25 | 100% |

### Tier 2 — Extended (20 files, accept_all mode)

Fun, Product_Type, Sum_Type, Option, Lattices, Groups, Rings, Fields,
Relation, Equiv_Relations, Map, Finite_Set, Num, Power, Complete_Lattices, etc.

---

## Architecture

```
.thy source (1,473 files) -> OuterSyntax::parse_spans() -> CommandSpan[]
  -> TheoryProcessor::process_span()
  -> IsarProof 3-mode state machine -> method dispatch -> ThmKernel (LCF)
  -> LocalTheory::finalize() -> Arc<Theory>
  -> SessionBuilder::build_session() -> DAG topo sort -> batch compile
```

See [ARCHITECTURE.md](docs/ARCHITECTURE.md) for details.

---

## Project Stats

| Metric | Value |
|--------|-------|
| Rust code | ~46,000 LOC (121 .rs files) |
| Proof methods | 27 |
| Tests | 694+ |
| Kernel coverage | ~95% |
| Compiler warnings | **0** |
| License | Apache-2.0 |

---

## Documentation

| Document | Content |
|----------|---------|
| [Architecture](docs/ARCHITECTURE.md) | Core architecture, data flow, design decisions |
| [Gap Analysis](docs/GAP_ANALYSIS.md) | **Complete gap analysis** — file-by-file vs Isabelle |
| [Roadmap](docs/ROADMAP.md) | Phase 0-60 plan (v1.8.1 -> v2.0.0) |
| [Developer Guide](docs/DEVELOPMENT.md) | Environment, build/test, command reference |
| [Session Transfer](docs/SESSION_TRANSFER.md) | v1.8.1 -> v1.9.0 handoff context |
| [Changelog](CHANGELOG.md) | Full version history |
| [Rules](.claude/rules/) | 20 domain and engineering rule files |
