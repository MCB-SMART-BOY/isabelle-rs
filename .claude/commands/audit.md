---
name: audit
description: Run kernel safety audit — scan for Typ::dummy(), check Thm invariants
category: safety
---
# /audit

内核安全检查运行 `cargo +stable xtask strict`，兼容性调用点清单运行
`cargo +stable xtask compat`。审核契约见
`.claude/skills/audit-kernel.md`。
