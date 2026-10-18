---
name: Port from Isabelle
description: Port migration-critical Isabelle/ML semantics without widening trusted construction or conflating Pure and HOL.
category: development
version: 3.0.0
triggers: [port from Isabelle, Isabelle ML, ML to Rust, new module from Isabelle, port ML]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit, Grep]
---
# Port From Isabelle

Native Rust compatibility with the pinned Isabelle2025 source is the approved
long-term A–H goal, not current behavior. For capability inventory, completed
official reference runs and open gaps consult
[`PROJECT_STATUS.md`](../../docs/status/PROJECT_STATUS.md), not this skill.
For explicitly scoped migration work, read the authoritative Isabelle source
and identify exact semantics, types, side conditions, theory dependencies and
trust status before writing Rust. The JVM-free policy disables local
`reference prepare/build/inventory`; only offline `cargo +stable xtask reference compare`
remains available for separately approved reference evidence. Frozen official
observations and source comparison are not a fresh runtime run or native Rust
acceptance; production cannot fall back to official Isabelle.

Do not transliterate ML unchecked. Keep Pure rules in `crates/kernel` and
source-specific HOL rules in a validated logic basis; the current minimal
`refl` basis and conservative `True_def` are not a general HOL environment.
Keep Isar adapters separate from accepted owner authority. Do not add
theorem-specific legacy core constructors. Add focused/attack tests and run
`cargo +stable xtask strict` plus the affected theory mode.
