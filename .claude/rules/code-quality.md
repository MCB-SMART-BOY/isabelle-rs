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

Use `cargo +stable xtask fix check` for non-mutating fix inspection when
applicable, then `cargo +stable xtask verify` for deterministic repository
verification. `selftest` and external security/global gates remain separate;
see [the command catalog](../../scripts/README.md#verification). All maintained
automation lives in `xtask/`; `scripts/` retains official reference probe
inputs and classified Rust/configuration design templates, not runnable
project scripts. Short explanatory Markdown snippets are allowed.
