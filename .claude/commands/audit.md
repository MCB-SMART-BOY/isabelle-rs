---
name: audit
description: Run kernel safety audit — scan for Typ::dummy(), check Thm invariants
category: safety
---
# /audit

快速内核安全检查。完整流程见 `.claude/skills/audit-kernel.md`。

```bash
rg 'Typ::dummy()' src/core/thm.rs src/core/logic.rs src/core/drule.rs
cargo test --lib core::thm
```
