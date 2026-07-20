---
name: audit
description: Run kernel safety audit — scan for Typ::dummy(), check Thm invariants
category: safety
---
# /audit

内核安全检查。运行 `scripts/dev-check.sh strict`，并使用
`scripts/audit-compat.sh` 查看 legacy compatibility 调用点。审核契约见
`.claude/skills/audit-kernel.md`。
