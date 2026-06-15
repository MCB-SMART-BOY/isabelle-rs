---
name: fix
description: Run auto-fixes for common issues — clippy, fmt, cargo fix
category: maintenance
---

# /fix

Run all project auto-fixes.

## Steps

```bash
# 1. Auto-fix compiler suggestions
cargo fix --lib --allow-dirty

# 2. Format code
cargo fmt

# 3. Clippy lint
cargo clippy --fix --allow-dirty --lib

# 4. Verify
cargo check --lib
cargo test --lib core::thm
```
