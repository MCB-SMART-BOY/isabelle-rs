---
name: Add Isar Command
description: Add an Isar command only when explicitly scoped; broad command coverage is not the current trusted main line.
category: development
version: 3.0.0
triggers: [add Isar command, proof language, state machine, have/show, fix/assume, qed]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit]
---
# Add Isar Command

Broad Isar expansion is deferred until the implemented data-only source AST is
integrated with checked `CProp`/`Trueprop` elaboration, then the explicit HOL
basis and conservative-definition boundaries close. If a command is required
for that migration, inspect `src/isar/proof.rs`, `src/isar/toplevel.rs`, and the
existing dispatch tests before editing.

The command must preserve proof-mode invariants, return typed errors, and never
turn parser or method failure into `assume`. Add focused tests, then run
`scripts/dev-check.sh strict` and the relevant theory mode. Reusable Rust API
sketches belong in `scripts/templates/`, not this skill.
