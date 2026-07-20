---
name: Add Proof Method
description: Add a proof method only when explicitly scoped; broad method coverage is deferred behind source-aware HOL elaboration and basis installation.
category: development
version: 3.0.0
triggers: [add proof method, new search strategy, port method from Isabelle, add tactic]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit]
---
# Add Proof Method

General proof-method expansion is not the current main line. First prove that
the method reduces a classified admitted cause without adding trusted proof
power to `src/core` or bypassing `src/kernel` acceptance.

Follow the existing method enum, parser, execution dispatch, and theorem lookup
paths in `src/isar/method.rs`. Preserve `NotApplicable` versus explicit
rejection semantics, keep failed proof search admitted, add focused tests, and
run `scripts/dev-check.sh strict` plus the affected theory mode.
