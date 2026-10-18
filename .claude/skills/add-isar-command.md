---
name: Add Isar Command
description: Add an Isar command only when explicitly scoped; broad command coverage is not the current trusted main line.
category: development
version: 3.0.0
triggers: [add Isar command, proof language, state machine, have/show, fix/assume, qed]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit]
---
# Add Isar Command

Broad Isar support belongs to later stages of the approved A–H native
compatibility program, not the current implementation. The standalone checked
source compiler supports only narrow `TrueI` and Pure identity fixtures;
the sampled HOL `TrueI` has its own audited source projection. The legacy
complete-source loader supports a limited documented command allowlist.
Inspect `src/isar/proof.rs`, `src/isar/proof_state.rs`,
`src/isar/proof_result.rs`, `src/isar/toplevel.rs`, and relevant loader dispatch
tests before editing.

The command must fully consume its input, preserve proof-mode invariants,
return typed errors, and never turn parser or method failure into `assume`.
Only a real Strict/checked theorem of the entire statement may close a goal.
Add focused tests, then run `cargo +stable xtask strict` and the relevant
theory mode. Reusable Rust API sketches belong in `scripts/templates/`, not
this skill.
