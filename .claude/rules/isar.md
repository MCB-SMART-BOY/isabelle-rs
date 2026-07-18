---
description: Isar parser, proof-state, source provenance, and adapter rules.
globs: src/isar/**, src/hol/hol_loader.rs
alwaysApply: false
version: 4.0
updated: 2026-07-18
---
# Isar Rules

Preserve meta versus object connectives, source consumption, local context,
Const/Free/Var identity, explicit types, and implicit `HOL.Trueprop` judgment
positions. The current lexical TrueI source guard is transitional metadata, not
a source-faithful elaborator.

For explicit proofs, registered strict adapters run first: `Proved` returns,
`Rejected` admits with a specific strict-adapter reason, and only
`NotApplicable` may enter parser-gap or legacy fallback. Do not add another
theorem adapter before the `CProp`/theory/HOL-basis correction.
