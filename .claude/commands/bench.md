---
name: bench
description: Run performance benchmarks and test matrix
category: meta
---
# /bench

运行维护的验证矩阵。使用 `scripts/dev-check.sh strict`；需要理论
宽验证时使用 `core`、`tier2`、`tier3` 或 `broad` 模式。

当前 sampled core 基线是 `TransitionalStrictClosed: 1/125` 和
`KernelTrustedClosed: 0/125`，不得声称 `125/125` 可信证明。
