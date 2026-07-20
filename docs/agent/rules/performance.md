---
description: Performance changes must preserve deterministic proof semantics.
globs: src/core/net.rs, src/hol/hol_loader.rs, src/isar/method.rs
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Performance Rules

Measure before optimizing and retain a deterministic CPU reference. Caches,
nets, parallel search, or future compute backends may rank candidates only; they
must not construct or accept theorems, erase trust classes, or alter the exact
kernel check.

Record benchmark inputs and correctness gates. Run the relevant
`scripts/dev-check.sh` mode before and after. HPC/Burn/CubeCL remains a deferred,
untrusted design track.
