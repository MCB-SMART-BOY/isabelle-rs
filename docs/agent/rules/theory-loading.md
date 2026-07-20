---
description: Source parsing, theory loading, searchable facts, and final acceptance.
globs: src/hol/hol_loader.rs, src/isar/term_parser.rs, src/theory/**
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Theory Loading Rules

Preserve full source proposition structure and provenance. Parser prefix recovery,
dummy types, surface-name matching, or compatibility certification must never be
silently upgraded into strict input.

`HolTheoremDb` and legacy theory tables are searchable/transitional structures.
Final acceptance requires context-bound new-kernel `TrustedTheorem` values in
`TrustedTheory`. Keep definition sources separate from theorem facts and do not
invent conservative-definition semantics in an adapter.
