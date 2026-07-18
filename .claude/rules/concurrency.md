---
description: Concurrency rules for shared theorem databases and session infrastructure.
globs: src/core/net.rs, src/hol/hol_loader.rs, src/session/**, src/server/**
alwaysApply: false
version: 2.0
updated: 2026-07-18
---
# Concurrency Rules

Prefer immutable data and message passing. Keep lock scope explicit, never hold
a lock across blocking work or `.await`, and make initialization deterministic.
Thread-local or global theorem databases must not erase theory identity,
provenance, trust class, or theorem burdens.

Concurrency must not introduce alternative theorem construction paths. Add
deterministic stress tests and run the relevant verification mode. Large
reusable Rust examples belong in `scripts/templates/`; short local contract
snippets may remain in Markdown.
