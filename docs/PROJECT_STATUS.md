# Project Status and Positioning

This document is the canonical high-level status for Isabelle-rs. It should be
read before using older roadmap, architecture, or gap-analysis notes.

## Current Position

Isabelle-rs is not a full Rust rewrite of Isabelle. The accurate current
position is:

```text
A Rust implementation of an Isabelle/Pure-inspired LCF kernel
with explicit oracle footprints, closed-theorem acceptance,
and minimal proofterm replay.
```

Chinese summary:

```text
一个受 Isabelle/Pure 启发的 Rust 化 LCF 证明内核原型，
重点研究 oracle 足迹追踪、闭合定理接收条件、
以及 proofterm replay 复检机制。
```

The project is now beyond a toy parser: it has a meaningful trusted-kernel
prototype and a growing soundness attack-test suite. Its research value is not
feature parity with Isabelle/HOL. Its value is a smaller Rust-native setting for
studying theorem-construction boundaries, admitted/oracle accounting, closed
theorem statistics, and proof-object replay.

## Current Baseline

The first trusted-kernel engineering checkpoint is recorded in
[BASELINE.md](BASELINE.md). It includes four reviewable commits:

```text
e60580b kernel: harden primitive rules and checked instantiation
7465d48 trust: require closed proved theorems for trusted acceptance
2dee3d0 proofterm: add minimal burden-aware derivation replay
eef6d80 docs: reposition project as trusted Rust LCF kernel prototype
```

The baseline gate is:

```bash
cargo fmt --check
cargo check
cargo test --test kernel_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
```

The baseline originally carried two ignored `alpha_eq` tests:

```text
Free / Const suffix matching
Var / Free index confusion
```

Strict kernel alpha-equivalence now rejects both in trusted paths. The legacy
behavior is isolated as explicit `compat_alpha_eq` parser/loader compatibility.

## What Is Solid

The following areas have a coherent implementation and regression coverage:

| Area | Current state |
|---|---|
| LCF-style theorem type | `Thm` fields are private; external construction routes through `ThmKernel`. |
| Kernel primitive rules | Core subset implemented; several rounds of type/burden/oracle boundary hardening done. |
| Checked instantiation | Production paths use `instantiate_checked`; legacy infallible instantiation is not a production API. |
| Oracle/admit tracking | `ThmKernel::admit(ct, reason)` marks unproved accepted propositions and propagates oracle footprints. |
| Closed theorem acceptance | A truly proved lemma requires no oracles, no hypotheses, and no unresolved `tpairs`. |
| Searchable vs trusted facts | `HolTheoremDb` is a proof-search fact index; final trusted theorem tables use closed proved filters. |
| Attribute fallback honesty | Non-derivational theorem transformations are admitted as `admitted:attribute_transformation`. |
| T4 minimal replay | `assume`, `reflexive`, `symmetric`, `transitive`, `implies_intr`, `implies_elim` replay with burden checks. |
| Attack tests | `tests/kernel_soundness.rs`, `src/core/thm.rs`, and `src/core/proofterm.rs` encode regression attacks. |

Important distinction:

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hyps + no unresolved tpairs
```

`assume(A)` is a valid theorem of shape `A |- A`; it is not `|- A` and must not
be counted as a closed proved lemma.

## What Is Not Complete

The project is not close to full Isabelle/HOL:

| Layer | Honest current assessment |
|---|---|
| Term / type / certification boundary | Basic structures exist, but `Typ::dummy()` and parser/loader representation gaps remain. |
| Pure kernel | Research-grade prototype, not full Isabelle `thm.ML` equivalence. |
| Proofterm replay | Minimal derivation replay, not full Isabelle `proofterm.ML` checking. |
| Isar | Partial state machine and method dispatch, far from full Isabelle/Isar semantics. |
| HOL tools | Simplifier/Metis/Meson/linarith/datatype packages are partial or heuristic. |
| HOL library coverage | Small subset; many accepted facts remain admitted or generated stubs. |
| Session/PIDE/LSP | Useful skeletons, not Isabelle session/PIDE infrastructure. |
| AFP / ecosystem | Out of scope for the current research slice. |

## Relative Completion Estimates

These are semantic/engineering estimates, not line-count percentages.

| Scope | Current estimate |
|---|---:|
| Full Isabelle/HOL + Isar + PIDE + AFP ecosystem | 15%-25% |
| Isabelle/Pure-inspired Rust kernel research slice | 45%-60% |
| Oracle footprints + closed theorem acceptance specialty | 65%-75% |
| T4 proofterm replay/checker | 10%-20% |
| HOL tools and automation | 10%-20% |
| PIDE/session ecosystem | 5%-15% |

The numbers are intentionally conservative. Do not market the project as
"Rust Isabelle" or "feature-compatible with Isabelle".

## Known T2 Debts

These are trusted-boundary issues that T4 replay does not automatically solve:

| Debt | Why it matters | Correct direction |
|---|---|---|
| `compat_alpha_eq` Free/Const suffix matching | Still available for legacy parser/loader compatibility, but no longer used by trusted kernel equality. | Fix parser/loader/type annotation, then remove/narrow compat usage. |
| `compat_alpha_eq` Var/Free matching | Still available for schematic-variable parser gaps, but no longer used by trusted kernel equality. | Align theorem DB/parser representation of schematic variables. |
| `Typ::dummy()` at kernel boundaries | Lets ill-typed terms remain too long. | Make parser/type inference/CTerm certification produce well-typed certified terms. |
| `Option<Thm>` errors | Type mismatch and normal non-match can both become `None`. | Gradually move trusted boundaries toward `Result<Option<Thm>, KernelError>`. |

## T4 Replay Status

Current supported replay rules:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

Current replay behavior:

- `Thm::check_proof()` reconstructs theorem shape and compares `prop`, `hyps`,
  `tpairs`, and `oracles`.
- `Thm::validate_proof()` uses the same burden-aware replay gate.
- `ProofBody::check(expected_prop)` is proposition-only compatibility code and
  is not a trusted theorem validation gate.
- `POracle` / admitted theorem replay fails for independent kernel replay.
- Unsupported rules fail explicitly; they are not silently trusted.

This is a kernel derivation replay prototype, not a full Isabelle proofterm
checker. Isabelle-style proof reconstruction, `PThm` expansion, proof
compression, type abstraction/application, stored theorem graph replay, and full
primitive rule coverage are still open.

## Next Priority Order

Do not spend the next phase on more HOL/Isar surface features, LSP, WASM,
Sledgehammer, SMT, or Code Generator work. The route is:

1. Tighten kernel equality/certification boundaries to reduce `Typ::dummy()` and
   Free/Const/Var confusion.
2. Extend T4 proofterm replay rule coverage after strict kernel semantics are
   stable.
3. Reduce admitted lemmas by cause, not by hiding fallback paths.
4. Expand HOL/Isar/tool coverage only after the trusted boundary remains stable.
5. Add optional CLI/verify integration for proof replay once major primitive
   rules are supported.

## Recommended Project Description

Use this in papers, README summaries, or external descriptions:

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel. It focuses on explicit oracle footprints,
closed-theorem acceptance, and proof-object replay rather than broad
Isabelle/HOL feature parity.
```

Avoid:

```text
Rust rewrite of Isabelle
Feature-complete Isabelle/HOL in Rust
Full Isabelle-compatible prover
```
