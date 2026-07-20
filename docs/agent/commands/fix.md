---
name: fix
description: Run auto-fixes for common issues — clippy, fmt, cargo fix
category: maintenance
---
# /fix

自动修复入口是 `scripts/fix.sh apply`；只检查不修改时使用
`scripts/fix.sh check`。`apply` 会修改当前工作区，执行前必须确认已有变更
都需保留。
