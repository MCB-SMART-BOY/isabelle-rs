---
name: Search Theorem Database
description: Navigate HolTheoremDb and its database-local search caches as migration indexes; never present indexed facts as accepted theorems.
category: theory
version: 3.0.0
triggers: [find theorem, lookup rule, search database, theorem by name, where is]
permissions: [Read, Grep]
---
# Search Theorem Database

Inspect `src/hol/hol_loader.rs` and actual `HolTheoremDb` APIs rather than using
copied Rust snippets. Searchable entries may be open, admitted, generated,
compatibility, or transitional strict facts; lookup success is not trusted
acceptance. Pass a borrowed `&HolTheoremDb` through synchronous legacy search;
local theory transactions own isolated databases. DB-local cached rules are
invalidated by `extend`, `add_builtins`, and `insert_named_fact`; direct writes
to public search collections can leave caches stale.

Final trust requires a context-bound new-kernel `TrustedTheorem` entering
`TrustedTheory`. If a stable search helper is needed, keep product-dependent
diagnostics in a product binary and their orchestration in `xtask/`, which must
not depend on the product. Document the diagnostic's trust-class output.
