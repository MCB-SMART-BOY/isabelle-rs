---
name: audit
description: Run kernel safety audit — scan for Typ::dummy(), check Thm invariants
category: safety
---

# /audit

Run a quick kernel safety audit.

## Quick Scan

```bash
# Typ::dummy() in kernel — ZERO TOLERANCE
rg "Typ::dummy\(\)" src/core/thm.rs src/core/logic.rs src/core/drule.rs src/core/more_thm.rs

# Direct Thm construction outside thm.rs — FORBIDDEN
rg "Thm\s*\{" src/core/ --glob '!thm.rs'

# Missing require_non_dummy
cargo check --lib 2>&1 | grep -i "dummy"

# Recursive functions without depth guards
rg -l "fn.*exec.*state.*depth\|fn.*search" src/isar/method.rs
```

## Post-Audit Tests

```bash
cargo test --lib core::thm core::logic core::drule core::unify
cargo clippy -- -D warnings
cargo fmt -- --check
```

## Related

- Skill: `/audit-kernel`
- Rule: `.claude/rules/kernel.md`
