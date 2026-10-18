---
name: bench
description: Select scoped theory diagnostics; benchmark performance only with separately measured runs
category: meta
---
# /bench

仓库级确定性验证使用 `cargo +stable xtask verify`；`selftest` 单独验证
xtask。信任边界用 `strict`，125 定理采样用 `core`，理论统计诊断需显式
选择 `tier2`、`tier3`、`broad` 或 `all`；后两者不是完整质量门，也不
包含 workspace `test`。`lib` 仅是 root library suite，`test` 才是完整
workspace 测试。外部安全审计与全局质量门独立执行和报告。
实际性能 benchmark 另需单独测量并报告输入/输出。历史 bundled 125
采样为 `KernelTrustedClosed: 1/125`（`HOL::TrueI` 源码投影）、
`TransitionalStrictClosed: 0/125`，不是本次验证结果；统计完成不是证明成功。
