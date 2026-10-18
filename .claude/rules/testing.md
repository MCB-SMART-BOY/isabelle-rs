---
description: Verification modes, attack tests, and honest result reporting.
globs: "**/*.rs"
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Testing Rules

Use `cargo +stable xtask verify` for deterministic repository verification and
`selftest` separately for product-independent automation tests. Use the
[command catalog](../../scripts/README.md#verification) for exact modes.
Trusted-boundary work also needs scoped `strict`; sampled theorem claims need
`core`; `tier2`/`tier3` and `all`/`broad` are explicit report-only diagnostics,
not quality gates. `test` is the full workspace suite, whereas bare `cargo test`
selects only the root default member. Security audits and the global validator
remain independent; do not infer one gate from another.

Every kernel side condition needs a positive test and a rejection/tampering
attack. Every adapter needs `NotApplicable`, `Proved`, and typed `Rejected`
coverage. Report exact counts from current output, including skipped,
stack-sensitive, or pre-existing failures.

声明与成功契约对应 `kernel_declaration_boundary`、`theory_load_contract`、
`session_load_contract`、`legacy_*_contract` 和 `automation_*_contract`。
strict 门运行独立 `isabelle-kernel` crate 单测、doctests 及零警告检查；
依赖 root `serde` 的反序列化边界例子在 root re-export 上单独执行。
不能以零匹配或缺失 crate 导致的 compile-fail 冒充有效边界检查。
正例必须是真实证明，不能保留 synthetic goal 直接结案或坏 ATP
证据回退搜索的假成功断言。
