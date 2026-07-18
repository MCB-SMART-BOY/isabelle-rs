---
name: Safe Refactor
description: "Safely refactor isabelle-rs code. Project-specific patterns: kernel safety constraints, method dispatch, theory pipeline, attribute classification."
category: development
version: 3.0.0
triggers: [refactor, extract module, rename, restructure, code smell, clean up]
permissions: [Bash:cargo test, Bash:cargo clippy, Bash:cargo fmt, Read, Edit, Grep]
---
# Refactor

Capture a relevant baseline with `scripts/dev-check.sh`; inspect the dirty
worktree and preserve unrelated changes. Refactor in behavior-preserving steps,
keeping theorem construction authority, burden propagation, compatibility
taint, and `TransitionalStrictClosed`/`KernelTrustedClosed` semantics unchanged.

Run `scripts/fix.sh check`, the strict gate for trust-boundary code, and the
appropriate theory mode. Do not combine a structural refactor with new proof
power or workspace splitting.
