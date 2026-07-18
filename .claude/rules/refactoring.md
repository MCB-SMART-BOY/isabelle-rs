---
description: Behavior-preserving refactoring across the two-kernel migration.
globs: "**/*.rs"
alwaysApply: false
version: 2.0
updated: 2026-07-18
---
# Refactoring Rules

Separate structural changes from new proof power. Capture relevant tests and
trust metrics first, refactor in reviewable steps, and preserve public behavior,
error variants, theorem burdens, derivations, compatibility taint, and source
provenance.

Do not use a refactor to move legacy code into the candidate TCB or freeze an
unstable boundary into a workspace split. Run `scripts/fix.sh check`, the strict
gate, and affected theory modes.
