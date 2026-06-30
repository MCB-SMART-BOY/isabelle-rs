# CLAUDE.md — Isabelle-rs

This repository is **not** a full Rust rewrite of Isabelle.

Current accurate positioning:

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel. It focuses on explicit oracle footprints,
closed-theorem acceptance, and proof-object replay rather than broad
Isabelle/HOL feature parity.
```

Read these first:

1. [docs/PROJECT_STATUS.md](docs/PROJECT_STATUS.md)
2. [docs/TRUST.md](docs/TRUST.md)
3. [docs/ROADMAP.md](docs/ROADMAP.md)
4. [docs/KERNEL_RULES.md](docs/KERNEL_RULES.md)
5. [docs/KERNEL_ATTACK_TESTS.md](docs/KERNEL_ATTACK_TESTS.md)
6. [docs/ADR-0001-kernel-core-rewrite.md](docs/ADR-0001-kernel-core-rewrite.md) — Strangler-pattern kernel reset.
7. [docs/ADR-0002-layered-platform-architecture.md](docs/ADR-0002-layered-platform-architecture.md) — Target layered platform.

## Branch Strategy

- `dev` is the normal development branch.
- `main` is the stable release branch.
- Do not rewrite or revert unrelated dirty work.
- Do not modify `Cargo.lock` or `isabelle-source` unless explicitly in scope.

## Current State

| Track | Status |
|---|---|
| LCF-style `Thm` kernel | Research prototype with private theorem fields and `ThmKernel` construction boundary. |
| Strict kernel nucleus (`src/kernel/`) | Base primitive rules plus conservative `resolve1_match` prototype. No dummy type, no compat certification, no fallback theorem construction. |
| T2 primitive rule hardening | Main body improved; strict `kernel_alpha_eq` split out; `Typ::dummy()` and certification remain known trust debts. |
| Checked instantiation | Production paths use `instantiate_checked`; legacy infallible API is not production. |
| Oracle/admit tracking | Explicit `admitted:*` footprints and propagation. |
| Closed theorem acceptance | Verified lemma statistics require `is_strict_closed_proved()`. |
| Searchable vs trusted facts | `HolTheoremDb` is a search index; final `Theory` table accepts strict closed proved theorems. |
| T4 proofterm replay | Minimal burden-aware replay for `assume`, `reflexive`, `symmetric`, `transitive`, `implies_intr`, `implies_elim`. |
| HOL/Isar/tools | Partial prototypes, not Isabelle parity. |

## Trust Vocabulary

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hyps + no unresolved tpairs
is_strict_closed_proved() == strict construction + is_closed_proved() + no dummy types
```

`ThmKernel::assume(A)` constructs `A |- A`, not `|- A`.

`ThmKernel::admit(ct, reason)` is the only acceptable route for accepted
unproved propositions. Use specific reasons such as:

```text
admitted:proof_engine_failed
admitted:parser_gap
admitted:unsupported_method
admitted:attribute_transformation
admitted:datatype_stub
admitted:class_stub
admitted:metis_fallback
admitted:simp_fallback
```

## Iron Laws

1. `Thm` construction authority stays inside `src/core/thm.rs`; external code
   uses `ThmKernel`.
2. Do not use `assume` as fallback for failed proofs, stubs, unsupported
   methods, or attribute transformations.
3. Count a lemma as verified only if it is `is_strict_closed_proved()`.
4. Preserve `hyps`, `tpairs`, `shyps`, and `oracles` through kernel rules.
5. Use `instantiate_checked` on production theorem-instantiation paths.
6. Do not widen `Typ::dummy()` tolerance in the kernel.
7. Do not use `compat_alpha_eq` in trusted kernel rules; it exists only for
   explicitly marked parser/loader compatibility.
8. New trusted kernel work belongs in `src/kernel`; legacy `src/core` changes
   are bug fixes or adapter bridges only.
9. Run `scripts/check-kernel-firewall.sh` for strict-kernel boundary changes.
10. Proof replay success does not replace closed theorem acceptance.
11. `ProofBody::check(expected_prop)` is proposition-only compatibility code;
   trusted replay gates are `Thm::check_proof()` and `Thm::validate_proof()`.
12. Add attack tests for trusted-boundary fixes.

## Current Roadmap

Priority order (aligned with ADR-0002 layered platform vision):

1. Stabilize strict `src/kernel` nucleus, including firewall checks,
   deterministic substitutions, and explicit `resolve1_match` limitations.
2. Establish structured compatibility matrix for legacy adapters.
3. Extend strict-kernel replay/invariant coverage after rule contracts and
   compatibility boundaries are stable.
4. Reduce admitted lemmas by classified reason.
5. Split into Cargo workspace (`isabelle-kernel` crate first).
6. Design session incremental engine (snapshot/rollback/content-addressed cache).
7. Build `isabelle.toml` project system (Lake-style).
8. Design Agent Proof Protocol (APP).
9. Expand HOL/Isar/tool coverage only after trusted boundaries remain stable.
10. Harden WASM plugin sandbox boundaries.
11. AFP large-scale benchmark.

Do not start workspace splitting, session redesign, or Agent protocol work
before the strict-kernel prototype has a stable compatibility matrix and clear
adapter boundaries.

## Verification Commands

For docs-only changes:

```bash
cargo fmt --check
cargo check
```

For kernel, proof replay, theorem acceptance, or proof-search changes:

```bash
cargo fmt --check
cargo test --test kernel_soundness
cargo test --test kernel_rewrite_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
cargo check
```

For broad theory claims:

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

Do not claim full `cargo test --lib` success unless the known theory-loader
stack-sensitive test has been verified fixed.

## Architecture Summary

```text
.thy source
  -> parser / loader / type inference
  -> CTerm certification
  -> ThmKernel
  -> Thm with hyps/prop/tpairs/shyps/oracles/derivation
  -> proof-search indexes or final trusted Theory tables
```

Important split:

```text
HolTheoremDb / theorem_index
  = searchable fact indexes
  = may contain open/admitted/generated facts

final Theory theorem table
  = trusted output table
  = only is_strict_closed_proved() facts
```

## Known Persistent Debts

- `compat_alpha_eq` Free/Const compatibility outside trusted kernel paths.
- `compat_alpha_eq` Var/Free compatibility outside trusted kernel paths.
- `Typ::dummy()` at parser/type/certification boundaries.
- `Option<Thm>` erasing `KernelError` on some proof-search paths.
- Partial T4 replay coverage.
- HOL/Isar tools far from Isabelle parity.
