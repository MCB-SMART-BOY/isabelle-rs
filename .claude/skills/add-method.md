---
name: Add Proof Method
description: Add a proof method only when explicitly scoped; proof completion requires a real checked result, not a search hit.
category: development
version: 3.0.0
triggers: [add proof method, new search strategy, port method from Isabelle, add tactic]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit]
---
# Add Proof Method

Broad proof-method compatibility belongs to later stages of the approved A–H
program, not the current implementation. For an explicitly scoped method
change, show that it addresses an observed failure without adding trusted proof
power to `src/core` or bypassing `crates/kernel` acceptance.

Follow method parsing, `src/isar/proof_result.rs`, execution dispatch, and
theorem lookup. The checked complete-source path must reject unknown methods,
arguments, and facts rather than falling back to Auto/Blast. Match the entire
goal with a Strict/checked theorem and permitted hypotheses before completion;
preserve separate explicit admit statistics only in sampled/search paths. Add
focused proof/failure tests, then run `cargo +stable xtask strict` and the
affected theory mode.
