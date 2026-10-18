---
description: Isar parser, proof-state, source provenance, and adapter rules.
globs: src/isar/**, src/hol/hol_loader.rs
alwaysApply: false
version: 4.0
updated: 2026-07-18
---
# Isar Rules

Preserve meta versus object connectives, source consumption, local context,
Const/Free/Var identity, explicit types, and `HOL.Trueprop` judgment positions.
The complete legacy term parser accepts only fully consumed input and binds
lexical variables to de Bruijn `Bound` indices; its status-returning API may
diagnose incomplete search input but cannot authorize a source theorem.

The registered sampled `TrueI` strict adapter's lexical source guard is
transitional metadata, not the standalone checked source elaborator. The
standalone compiler accepts only the narrow checked TrueI and explicitly
`PROP`-wrapped Pure identity with `by assumption`. Source proof commands must
yield a real Strict/checked theorem matching the complete goal and permitted
local hypotheses; synthetic obligations, Compat facts, and method fallback
cannot close a lemma. Unsupported scripts fail rather than silently admit
inside complete-source loading.
