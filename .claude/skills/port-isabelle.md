---
name: Port from Isabelle
description: Port migration-critical Isabelle/ML semantics without widening trusted construction or conflating Pure and HOL.
category: development
version: 3.0.0
triggers: [port from Isabelle, Isabelle ML, ML to Rust, new module from Isabelle, port ML]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit, Grep]
---
# Port From Isabelle

Broad Isabelle surface porting is deferred. For migration-critical work, read
the authoritative Isabelle source and identify the exact semantic contract,
types, side conditions, theory dependencies, and trust status before writing
Rust.

Do not transliterate ML unchecked. Keep Pure rules in the candidate kernel,
future HOL basis in the explicit logic-extension design, and adapters in Isar.
Do not add theorem-specific legacy core constructors. Add focused/attack tests
and run `scripts/dev-check.sh strict` plus the affected theory mode.
