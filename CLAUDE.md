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

## Branch Strategy

- `dev` is the normal development branch.
- `main` is the stable release branch.
- Do not rewrite or revert unrelated dirty work.
- Do not modify `Cargo.lock` or `isabelle-source` unless explicitly in scope.

## Current State

| Track | Status |
|---|---|
| LCF-style `Thm` kernel | Research prototype with private theorem fields and `ThmKernel` construction boundary. |
| T2 primitive rule hardening | Main body improved; `alpha_eq` and `Typ::dummy()` remain known trust debts. |
| Checked instantiation | Production paths use `instantiate_checked`; legacy infallible API is not production. |
| Oracle/admit tracking | Explicit `admitted:*` footprints and propagation. |
| Closed theorem acceptance | Verified lemma statistics require `is_closed_proved()`. |
| Searchable vs trusted facts | `HolTheoremDb` is a search index; final `Theory` table accepts closed proved theorems. |
| T4 proofterm replay | Minimal burden-aware replay for `assume`, `reflexive`, `symmetric`, `transitive`, `implies_intr`, `implies_elim`. |
| HOL/Isar/tools | Partial prototypes, not Isabelle parity. |

## Trust Vocabulary

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hyps + no unresolved tpairs
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
3. Count a lemma as verified only if it is `is_closed_proved()`.
4. Preserve `hyps`, `tpairs`, `shyps`, and `oracles` through kernel rules.
5. Use `instantiate_checked` on production theorem-instantiation paths.
6. Do not widen `Typ::dummy()` tolerance in the kernel.
7. Do not delete broad `alpha_eq` Free/Const or Var/Free compatibility until
   parser/loader/type annotation boundaries are fixed.
8. Proof replay success does not replace closed theorem acceptance.
9. `ProofBody::check(expected_prop)` is proposition-only compatibility code;
   trusted replay gates are `Thm::check_proof()` and `Thm::validate_proof()`.
10. Add attack tests for trusted-boundary fixes.

## Current Roadmap

Priority order:

1. Extend T4 replay to `beta_conversion`, `forall_intr`, and `forall_elim`.
2. Add replay for `combination`, `abstraction`, and equality-intro/elimination
   rules if present.
3. Add replay for `instantiate_checked` / generalization.
4. Add replay for `bicompose`, `bicompose_eresolve`, and `subst_premise`.
5. Tighten parser/type/certification boundaries and reduce `Typ::dummy()`.
6. Shrink admitted lemmas by classified reason.
7. Expand HOL/Isar/LSP/WASM only after trusted boundaries remain stable.

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
  = only is_closed_proved() facts
```

## Known Persistent Debts

- `alpha_eq` Free/Const compatibility.
- `alpha_eq` Var/Free compatibility.
- `Typ::dummy()` at parser/type/certification boundaries.
- `Option<Thm>` erasing `KernelError` on some proof-search paths.
- Partial T4 replay coverage.
- HOL/Isar tools far from Isabelle parity.
