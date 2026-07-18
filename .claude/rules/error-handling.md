---
description: Typed error handling at parser, adapter, kernel, and replay boundaries.
globs: "**/*.rs"
alwaysApply: false
version: 2.0
updated: 2026-07-18
---
# Error Handling Rules

Use typed enums for control flow. Error display strings are diagnostics only and
must never decide acceptance, rejection class, fallback, or theorem trust.
Preserve `KernelError` detail at trusted boundaries; collapse to `Option` only
for a documented fail-closed search non-match.

Unsupported proof work becomes a specific `admitted:*` legacy reason, not
`assume`. Strict kernel paths have no admit constructor. Add tests showing that
message changes do not alter typed classification.
