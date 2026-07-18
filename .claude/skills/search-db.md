---
name: Search Theorem Database
description: Navigate HolTheoremDb as a searchable migration index; never present indexed facts as final trusted theorems.
category: theory
version: 3.0.0
triggers: [find theorem, lookup rule, search database, theorem by name, where is]
permissions: [Read, Grep]
---
# Search Theorem Database

Inspect `src/hol/hol_loader.rs` and actual `HolTheoremDb` APIs rather than using
copied Rust snippets. Searchable entries may be open, admitted, generated,
compatibility, or transitional strict facts; lookup success is not trusted
acceptance.

Final trust requires a context-bound new-kernel `TrustedTheorem` entering
`TrustedTheory`. If a stable search helper is needed, add a compile-checked Rust
diagnostic under `scripts/` and document its trust-class output.
