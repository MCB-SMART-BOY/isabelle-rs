---
description: Convert deep recursive Rust traversals without semantic drift.
globs: "**/*.rs"
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Iterative Traversal Rules

Use explicit stacks, worklists, continuation frames, or iterative DFS only
after reproducing a real depth failure. Preserve traversal order, binder depth,
short-circuit behavior, error paths, and theorem burdens.

Add shallow equivalence plus deep non-overflow tests. A stable reusable Rust
skeleton must be classified as design-only, compile under
`scripts/check-rust-templates.sh`, and live in `scripts/templates/`. Short local
contract snippets may remain in Markdown.
