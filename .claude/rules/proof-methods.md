---
description: Proof method dispatch, fallback, and theorem-result rules.
globs: src/isar/method.rs, src/isar/proof.rs, src/isar/proof_state.rs, src/isar/proof_result.rs, src/tools/**
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Proof Method Rules

Proof methods are search/derivation code, not theorem acceptance authority.
Complete-source method syntax must be fully consumed: unknown methods, unknown
facts, extra arguments, and failed named methods cannot silently fall back to
Auto/Blast. `apply_goal_method` checks an actual Strict/checked proof of the
complete expected proposition and permitted hypotheses; obligations are not
proof results. Keep sampled parser-gap/unsupported-method/proof failure
classifications separate from loader errors.

Never use `assume` for method failure or count an oracle-free open theorem as a
proved lemma. Explicitly classified sampled/search `admitted:*` reasons remain
legacy diagnostics, never accepted source proofs; strict kernel paths cannot
admit. Metis/Meson/ATP replay and simplifier certificates must cover their
full target and burden; broken ATP steps cannot fall back to search. Broad
method capability belongs to the approved staged program, not current support.
