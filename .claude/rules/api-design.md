---
description: Public API and visibility rules for kernel and Isar boundaries.
globs: crates/kernel/**, src/kernel/**, src/core/thm.rs, src/isar/method.rs, src/isar/proof.rs, src/isar/proof_result.rs
alwaysApply: false
version: 2.0
updated: 2026-07-18
---
# API Design Rules

Make invalid trust states unrepresentable. Keep unchecked strict constructors
private inside `crates/kernel`, theorem fields private, and expose typed
`Result` errors at trust boundaries. New-kernel accepted tokens only come
from exact-owner `accept_closed_theorem`, not legacy Strict, search, source
spans, obligations, or copied token identities. Do not publish theorem-specific
HOL constructors or implicit conversions to trusted theorems.

Prefer theorem-independent APIs with explicit theory, proof context, burden,
and provenance inputs. Large reusable API sketches belong in classified
design-only files under `scripts/templates/`; production APIs and tests remain
the source of truth, and standalone compilation does not validate integration.
