---
description: Honest release status, verification, changelog, and tags.
globs: Cargo.toml, Cargo.lock, CHANGELOG.md, README.md, docs/**
alwaysApply: false
version: 2.0
updated: 2026-07-18
---
# Release Rules

Release only on explicit request. Synchronize versions and all status/trust
documents, run `scripts/dev-check.sh all` or document the approved narrower
scope, and report actual failures/skips.

Do not describe `TransitionalStrictClosed` as kernel trust or claim full
Isabelle compatibility. Use normal commits and annotated tags; never rewrite
published history without explicit approval.
