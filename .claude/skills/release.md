---
name: Release Phase
description: Prepare an explicitly requested release with honest trust metrics, exact verification, and reviewed dependency/history changes.
category: release
version: 3.0.0
triggers: [release, version bump, phase complete, changelog, cut release]
permissions: [Bash:cargo test, Bash:cargo check, Bash:cargo clippy, Read, Edit, Bash:git]
---
# Release

Release work must be explicitly requested. Review `CHANGELOG.md`, current
project positioning, dependency changes, and the dirty worktree. Run
`scripts/dev-check.sh all` unless the release scope documents a narrower gate.

Update versions and status documents consistently, report skipped or failing
tests, then create a normal non-amended commit and tag only after approval.
Never market transitional `HOL::TrueI` as a new-kernel trusted theorem.
