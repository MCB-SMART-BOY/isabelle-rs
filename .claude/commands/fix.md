---
name: fix
description: Run auto-fixes for common issues — clippy, fmt, cargo fix
category: maintenance
---
# /fix

自动修复常见代码问题。

```bash
cargo fix --allow-dirty && cargo fmt && cargo clippy --fix --allow-dirty && cargo check --lib
```
