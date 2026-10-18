---
name: verify-all
description: Select the maintained verification gates; do not imply a passing full suite
category: verification
---
# /verify-all

`cargo +stable xtask verify` 是确定性的仓库级完整验证：聚合 workspace
格式、严格 Clippy、locked all-targets 编译、TCB 零警告、文档三个子门、
kernel firewall 和完整 workspace `test --no-fail-fast` 的独立失败。
`selftest` 独立验证 xtask，外部安全审计与全局 `~/.omp/agent/validate.sh`
仍分别执行并报告；`verify` 不运行 `core` 或 Tier 2/3 诊断，
不调用官方 reference。统计诊断需显式选择，不能替代任何门。
报告每项实际成功、失败、阻断或未运行，不用历史 1/125 推断本次通过。
