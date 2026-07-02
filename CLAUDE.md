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
6. [docs/KERNEL_PRIMITIVES.md](docs/KERNEL_PRIMITIVES.md) — Strict-kernel base primitive rule contracts.
7. [docs/RESOLUTION_DESIGN.md](docs/RESOLUTION_DESIGN.md) — Resolution family design and `resolve1_match` status.
8. [docs/HPC_SYMBOLIC_COMPUTE_DESIGN.md](docs/HPC_SYMBOLIC_COMPUTE_DESIGN.md) — Design-only untrusted CPU/GPU symbolic compute layer.
9. [docs/ADR-0001-kernel-core-rewrite.md](docs/ADR-0001-kernel-core-rewrite.md) — Strangler-pattern kernel reset.
10. [docs/ADR-0002-layered-platform-architecture.md](docs/ADR-0002-layered-platform-architecture.md) — Target layered platform.

## Branch Strategy

- `dev` is the normal development branch.
- `main` is the stable release branch.
- Do not rewrite or revert unrelated dirty work.
- Do not modify `Cargo.lock` or `isabelle-source` unless explicitly in scope.

## Current State

| Track | Status |
|---|---|
| LCF-style `Thm` kernel | Research prototype with private theorem fields and `ThmKernel` construction boundary. |
| Strict kernel nucleus (`src/kernel/`) | 15 base primitive rules (`assume`, `reflexive`, `symmetric`, `transitive`, `combination`, `abstraction`, `beta_conversion`, `implies_intr`, `implies_elim`, `forall_intr`, `forall_elim`, `equal_intr`, `equal_elim`, `generalize`, `instantiate`) plus conservative `resolve1_match` prototype. No dummy type, no compat certification, no fallback theorem construction. |
| T2 primitive rule hardening | Main body improved; strict `kernel_alpha_eq` split out; `Typ::dummy()` and certification remain known trust debts. |
| Checked instantiation | Production paths use `instantiate_checked`; legacy infallible API is not production. |
| Oracle/admit tracking | Explicit `admitted:*` footprints and propagation. |
| Closed theorem acceptance | Verified lemma statistics require `is_strict_closed_proved()`. |
| Searchable vs trusted facts | `HolTheoremDb` is a search index; final `Theory` table accepts strict closed proved theorems. |
| T4 proofterm replay | Minimal burden-aware replay for `assume`, `reflexive`, `symmetric`, `transitive`, `implies_intr`, `implies_elim`. |
| HPC symbolic compute | Parallel design track only: untrusted candidate generation, fingerprinting, and prefiltering. CPU baseline first; Burn/CubeCL only future optional backend; no kernel dependency. |
| HOL/Isar/tools | Partial prototypes, not Isabelle parity. |

## Type Names

| Strict kernel (`src/kernel/`) | Legacy core (`src/core/`) |
|---|---|
| `KernelRules` — primitive rule factory (TCB) | `ThmKernel` — legacy rule factory (quarantine) |
| `KernelThm` — internal theorem record | `Thm` — legacy theorem struct |
| `ClosedThm` — zero-hyps proved theorem | (no strict equivalent in legacy) |
| `OpenThm` — theorem with hypotheses | (no strict equivalent in legacy) |
| `TrustedTheorem` — certified-for-acceptance | `Thm` with `is_strict_closed_proved()` |
| `CTerm`, `CProp` — strict certified terms | `CTerm` with `CertStatus` — legacy certified terms |

## Trust Vocabulary

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hyps + no unresolved tpairs
is_strict_closed_proved() == strict construction + is_closed_proved() + no dummy types
```

`ThmKernel::assume(A)` constructs `A |- A`, not `|- A`.

`KernelRules::assume(prop)` returns `OpenThm` (has hypotheses). Most other
`KernelRules` methods operate on `KernelThm` and return `Result<KernelThm, ...>`
or `ClosedThm`.

`KernelRules::resolve1_match` is a conservative strict-kernel resolution
prototype: strict one-way matching only, no lifting/freshening, no full
unification, no flex-flex. Returns `RequiresLifting` on Free-variable collision.
It is NOT full `bicompose` — see `docs/RESOLUTION_DESIGN.md`.

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

1. `Thm` / `KernelThm` construction authority stays inside `src/core/thm.rs` /
   `src/kernel/thm.rs` respectively; external code uses `ThmKernel` (legacy) or
   `KernelRules` (strict). Strict `KernelThm`/`ClosedThm`/`OpenThm` constructors
   are gated by `pub(in crate::kernel)` visibility.
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
9. Run `bash scripts/check-strict-kernel.sh` for strict-kernel boundary changes.
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

Parallel non-blocking design track: HPC symbolic compute may define packed IR,
a deterministic CPU baseline, and future optional Burn/CubeCL backends. It must
not add GPU/backend dependencies to the kernel and must not delay the strict
kernel / resolution / admitted-inventory main line.

Do not start workspace splitting, session redesign, or Agent protocol work
before the strict-kernel prototype has a stable compatibility matrix and clear
adapter boundaries.

## Verification Commands

For docs-only changes:

```bash
cargo +stable fmt --check
cargo +stable check
```

For kernel, proof replay, theorem acceptance, or proof-search changes:

```bash
bash scripts/check-strict-kernel.sh
```

This formalized gate runs:
1. `cargo +stable fmt --check`
2. `cargo +stable check`
3. `scripts/check-kernel-firewall.sh` (no legacy deps, no forbidden patterns)
4. `cargo +stable test --test kernel_rewrite_soundness` (124 attack tests)
5. `cargo +stable test --test kernel_soundness` (26 boundary tests)
6. Kernel inline unit tests: `kernel::thm::` (11), `kernel::unify::tests::` (15), `kernel::rules::tests::` (30)
7. `cargo +stable test --lib core::` (199 compatibility tests)

For broad theory claims:

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

Do not claim full `cargo test --lib` success unless the known theory-loader
stack-sensitive test has been verified fixed.

## Architecture Summary

```text
Strict TCB (src/kernel/):
  ProofContext::certify_term / certify_prop
    -> CTerm / CProp
    -> KernelRules                # 15 primitives + resolve1_match
    -> KernelThm / ClosedThm / OpenThm
    -> TrustedTheorem (invariant replay)
    -> TrustedTheory

Legacy quarantine (src/core/):
  .thy source
    -> parser / loader / type inference
    -> CTerm certification (CertStatus::Checked/Compat)
    -> ThmKernel (LEGACY — bicompose/eresolve/subst_premise are core-only)
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
- Strict-kernel resolution limited to `resolve1_match` prototype (no full `bicompose`, `bicompose_eresolve`, `subst_premise`, lifting, or full unification).
- HOL/Isar tools far from Isabelle parity.
