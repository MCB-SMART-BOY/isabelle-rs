---
name: verify-all
description: Run the full verification test suite with appropriate stack size
category: verification
---
# /verify-all

完整验证入口是 `scripts/dev-check.sh all`。如果只做信任边界变更，
运行 `strict` 和 `core` 模式即可。实际输出是唯一可报告结果，
不使用历史的 `125/125` 或固定测试数。
