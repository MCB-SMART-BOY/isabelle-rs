---
description: Source parsing, theory loading, searchable facts, and final acceptance.
globs: src/hol/hol_loader.rs, src/isar/term_parser.rs, src/theory/**
alwaysApply: false
version: 3.0
updated: 2026-10-19
---
# Theory Loading Rules

Preserve full source proposition structure and provenance. Parser prefix recovery,
dummy types, surface-name matching, or compatibility certification must never be
silently upgraded into strict input. `TheoryProcessor` accepts a narrow
fully-consumed `.thy` subset: available, conflict-free merged imports, real
`typedecl`, supported lemma/proof/document commands, and a closing `end`. Unsupported commands,
unfinished proofs, `sorry`, `accept_all`, or trailing text fail the file without
publishing a partial theory. `SessionBuilder` may still publish independent
successful files, but must block descendants of failed imports.
Classify missing, failed, merge-conflicting and cyclic imports as
`DependencyError`; unsupported headers as `UnsupportedError`; duplicate theory
names as `ConflictError`. They remain failures. Actual parser failures remain
`SyntaxError`; never weaken the official-source no-syntax-error regression
to conceal an unsupported or incorrectly parsed command.

`HolTheoremDb` and legacy theory tables are searchable/transitional structures.
Pass a borrowed database through synchronous legacy search; each theory source
transaction owns isolated local facts. Search caches are DB-local, but directly
mutating public search collections can bypass invalidation. Final acceptance
requires context-bound new-kernel `TrustedTheorem` values in `TrustedTheory`.
Keep definition sources separate from theorem facts; do not invent
conservative-definition semantics in an adapter.
