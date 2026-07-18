---
description: Proof method dispatch, fallback, and theorem-result rules.
globs: src/isar/method.rs
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Proof Method Rules

Proof methods are search/derivation code, not theorem acceptance authority.
Preserve strict adapter priority for explicit proofs and keep parser-gap,
unsupported method, proof-engine failure, and goal-export failure as distinct
typed/admitted outcomes.

Never use `assume` for method failure. Never treat an oracle-free open theorem
as a proved lemma. Broad method expansion is deferred until the minimum trusted
HOL loop closes.
