---
description: Concurrency rules for shared theorem databases and session infrastructure.
globs: src/core/net.rs, src/hol/hol_loader.rs, src/session/**, src/server/**
alwaysApply: false
version: 2.1
updated: 2026-10-07
---
# Concurrency Rules

Prefer immutable data and message passing. Keep lock scope explicit, never hold
a lock across blocking work or `.await`, and make initialization deterministic.
Pass a borrowed `&HolTheoremDb` through synchronous legacy search; only
application roots may obtain the immutable process-wide database. Theory
transactions and local verification own isolated search databases. Cached
search rules must remain bound to the same database and declarations; never
use thread-local pointer overrides or reinterpret search facts as trusted
theorems.

For built-in `RealExecutor` document checks and definition lookup, keep the
single shared CPU queue but run legacy computation in a supervised
`--compute-worker` child. The owner must cancel, kill and reap that child on
close, replacement, timeout, and shutdown; a reply is committed only with the
original document lifetime/revision or outstanding request token. IPC carries
diagnostics and proof-state display data, never accepted theorem authority.
Worker start, frame, or execution failure is unavailable/error, not a successful
empty check. Custom `CommandExecutor` implementations still execute in-process
with cooperative cancellation; their shutdown grace is not a hard guarantee.

Use `extend`, `add_builtins`, or `insert_named_fact` to change a queried
legacy DB; direct writes to its public search collections can leave cached
rules stale. This limitation does not grant theorem authority.

Concurrency must not introduce alternative theorem construction paths. Add
deterministic stress tests and run the relevant verification mode. Large
reusable Rust examples belong in `scripts/templates/`; short local contract
snippets may remain in Markdown.
