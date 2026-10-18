---
name: fix
description: Run auto-fixes for common issues — clippy, fmt, cargo fix
category: maintenance
---
# /fix

自动修复入口是 `cargo +stable xtask fix apply`；只检查不修改时使用
`cargo +stable xtask fix check`。`apply` 会修改当前工作区，执行前必须确认
已有变更都需保留。
