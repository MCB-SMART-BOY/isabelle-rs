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
[`PROJECT_STATUS.md`](../../docs/status/PROJECT_STATUS.md), dependency changes,
and the dirty worktree. `cargo +stable xtask release-check --tag TAG` verifies
the version, then runs `verify` on supported platforms; it does not create a
tag or publish. Run independent `selftest`, security audits and the complete
global validator; report actual failures, omissions and unavailable prerequisites.
`core`, `all`, and Tier modes remain explicit diagnostics, not release gates.

Update versions and status documents consistently. Only create a normal
non-amended commit or tag after explicit separate approval; never auto-commit.
Use the dated evidence in [`PROJECT_STATUS.md`](../../docs/status/PROJECT_STATUS.md)
for sampled outcomes and independent CLI fixtures; do not treat any historical
sample as a fresh release check or as full Isabelle compatibility.
