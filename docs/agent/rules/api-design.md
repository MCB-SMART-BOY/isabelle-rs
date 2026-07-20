---
description: Public API and visibility rules for kernel and Isar boundaries.
globs: src/kernel/**, src/core/thm.rs, src/isar/method.rs, src/isar/proof.rs
alwaysApply: false
version: 2.0
updated: 2026-07-18
---
# API Design Rules

Make invalid trust states unrepresentable. Keep strict unchecked constructors at
`pub(in crate::kernel)` or narrower, keep theorem fields private, and expose
typed `Result` errors at trust boundaries. Do not publish theorem-specific HOL
constructors or implicit conversions from search/obligation types to trusted
theorems.

Prefer theorem-independent APIs with explicit theory, proof context, burden,
and provenance inputs. Large reusable API sketches belong in classified
design-only files under `scripts/templates/`; production APIs and tests remain
the source of truth, and standalone compilation does not validate integration.
