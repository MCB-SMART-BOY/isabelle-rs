---
description: Honest release status, verification, changelog, and tags.
globs: Cargo.toml, Cargo.lock, CHANGELOG.md, README.md, docs/**
alwaysApply: false
version: 2.0
updated: 2026-07-18
---
# Release Rules

Release only on explicit request. Synchronize versions and canonical status/trust
documents. `cargo +stable xtask release-check --tag TAG` checks the version and
then runs `verify` on supported platforms; it never creates a tag or publishes.
Run `selftest`, independent security audits and the complete global validator;
report failures, omissions and unavailable prerequisites separately. `core` and
Tier diagnostics are explicit, not implicit release checks.

Do not describe `TransitionalStrictClosed` as kernel trust or claim full
Isabelle compatibility. Use normal commits and annotated tags; never rewrite
published history without explicit approval.
