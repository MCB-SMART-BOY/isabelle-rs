# Isabelle-rs

Rust research prototype of an Isabelle/Pure-inspired LCF kernel.

This repository is **not** a full Rust rewrite of Isabelle. The accurate current
position is:

```text
A Rust implementation of an Isabelle/Pure-inspired LCF kernel
with explicit oracle footprints, closed-theorem acceptance,
and minimal proofterm replay.
```

The project has moved beyond a toy parser. Its current value is trusted-kernel
engineering: theorem construction boundaries, admitted/oracle tracking, closed
proved theorem statistics, and proof-object replay. It is still far from full
Isabelle/HOL + Isar + PIDE + AFP feature parity.

Read [docs/PROJECT_STATUS.md](docs/PROJECT_STATUS.md) first for the canonical
current status.

## Quick Start

```bash
cargo check
cargo fmt --check
cargo test --test kernel_rewrite_soundness
cargo test --test kernel_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
```

Large theory runs usually need a larger stack:

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

Do not claim full `cargo test --lib` success unless the known
`theory::loader::tests::test_batch_scan_theories` stack-overflow issue is
verified as fixed in the current checkout.

## Trust Model

The core rule is simple:

```text
trusted proved lemma =
  strict kernel construction + no oracles + no hypotheses + no unresolved tpairs + no dummy types
```

Important API distinction:

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hyps + no unresolved tpairs
is_strict_closed_proved() == strict construction + is_closed_proved() + no dummy types
```

`ThmKernel::assume(A)` constructs `A |- A`. It is a valid open theorem, not
`|- A`, and must not be counted as a closed proved lemma.

`ThmKernel::admit(ct, reason)` is the explicit accepted-without-proof entry
point. Its oracle footprint is propagated through later kernel inferences.

See [docs/TRUST.md](docs/TRUST.md).

## Current Status

| Area | Status |
|---|---|
| LCF-style `Thm` kernel | Research prototype with private theorem fields and hardened construction routes. |
| Strict kernel nucleus | `src/kernel` is the new TCB: no dummy type, no compat certification, separate `ProofObligation`, `TrustedTheory`, and `SearchFactDb`; includes primitive rules and `resolve1_match` prototype. |
| Kernel primitive rules | Core subset implemented; several rounds of side-condition, type, burden, and oracle propagation audits done. |
| Checked instantiation | Production proof-search paths use `instantiate_checked`; legacy infallible instantiation is not a production API. |
| Oracle/admit tracking | Explicit `admitted:*` footprint tracking and propagation. |
| Closed theorem acceptance | Session and final theory statistics use `is_strict_closed_proved()`, not raw theorem entries or compatibility closed-shapes. |
| Searchable facts vs trusted table | `HolTheoremDb` is a proof-search fact index; final trusted theorem tables only accept strict closed proved theorems. |
| Proofterm replay | Minimal burden-aware replay for `assume`, `reflexive`, `symmetric`, `transitive`, `implies_intr`, `implies_elim`. |
| Isar/HOL/tools | Partial implementation; useful for experiments, not feature-compatible with Isabelle. |
| LSP/WASM/PIDE | Skeletons only; not current priority. |

Relative completion estimates:

| Scope | Estimate |
|---|---:|
| Full Isabelle/HOL + Isar + PIDE + AFP ecosystem | 15%-25% |
| Isabelle/Pure-inspired Rust kernel research slice | 45%-60% |
| Oracle footprints + closed theorem acceptance specialty | 65%-75% |
| T4 proofterm replay/checker | 10%-20% |
| HOL tools and automation | 10%-20% |

## Known Trust Debts

- Trusted kernel equality now uses strict `kernel_alpha_eq`. The old broad
  Free/Const and Var/Free behavior is isolated as explicit `compat_alpha_eq`
  parser/loader compatibility and remains a T2 boundary debt.
- `Typ::dummy()` still appears at trusted boundaries. The direction is stricter
  parsing, type inference, and `CTerm` certification, not more kernel tolerance.
- Some proof-search APIs still collapse `KernelError` into `Option<Thm>`. This
  is sound when rejected branches fail closed, but weak for auditability.
- Proofterm replay is currently a minimal derivation replay checker, not full
  Isabelle `proofterm.ML`.

## Roadmap

Current priority order (aligned with ADR-0002 layered platform vision):

1. Stabilize strict `src/kernel` nucleus (15 primitives + `resolve1_match` prototype) with firewall checks and compatibility matrix.
2. Extend strict-kernel invariant replay coverage after rule contracts and adapter boundaries are stable.
3. Reduce admitted lemmas by classified reason.
4. Split into Cargo workspace (`isabelle-kernel` crate first).
5. Expand HOL/Isar/tool coverage only after trusted boundaries remain stable.
6. Build session incremental engine, `isabelle.toml`, and Agent Proof Protocol.

Detailed plan: [docs/ROADMAP.md](docs/ROADMAP.md).

## Documentation

| Document | Purpose |
|---|---|
| [docs/PROJECT_STATUS.md](docs/PROJECT_STATUS.md) | Canonical current positioning and status. |
| [docs/BASELINE.md](docs/BASELINE.md) | Trusted-kernel checkpoint, gate, and next entry point. |
| [docs/TRUST.md](docs/TRUST.md) | Trust model, theorem acceptance, oracle/admit semantics. |
| [docs/KERNEL_RULES.md](docs/KERNEL_RULES.md) | Kernel rule audit ledger. |
| [docs/KERNEL_PRIMITIVES.md](docs/KERNEL_PRIMITIVES.md) | Strict-kernel base primitive rule contracts. |
| [docs/RESOLUTION_DESIGN.md](docs/RESOLUTION_DESIGN.md) | Resolution family design and `resolve1_match` status. |
| [docs/KERNEL_ATTACK_TESTS.md](docs/KERNEL_ATTACK_TESTS.md) | Soundness regression matrix. |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Current architecture and trusted-boundary data flow. |
| [docs/ROADMAP.md](docs/ROADMAP.md) | Concrete next phases and acceptance gates. |
| [docs/GAP_ANALYSIS.md](docs/GAP_ANALYSIS.md) | Honest comparison against Isabelle. |
| [docs/DEVELOPMENT.md](docs/DEVELOPMENT.md) | Development and verification commands. |

## Recommended Description

Use this description externally:

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel. It focuses on explicit oracle footprints,
closed-theorem acceptance, and proof-object replay rather than broad
Isabelle/HOL feature parity.
```

Avoid describing the project as a feature-complete Rust Isabelle.
