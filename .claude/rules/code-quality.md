---
description: Rust formatting, diagnostics, review, and executable-template policy.
globs: "**/*.rs"
alwaysApply: true
version: 2.0
updated: 2026-07-18
---
# Code Quality Rules

Use clear typed Rust, small auditable functions, specific errors, and minimal
comments explaining non-obvious invariants. Preserve unrelated dirty work and
avoid unsafe/destructive operations unless explicitly justified.

Run `scripts/fix.sh check` for normal changes and the relevant
`scripts/dev-check.sh` modes before reporting. Reusable commands live in Bash
under `scripts/`; large reusable Rust/configuration skeletons live under
`scripts/templates/`. Short explanatory Markdown snippets are allowed.
