---
name: Verify Lemma
description: Verify lemmas and reports without conflating searchable, admitted, transitional, or kernel-trusted outcomes.
category: verification
version: 3.0.0
triggers: [lemma verification, proof failure, test failure, this lemma doesn't prove, verify fails]
permissions: [Bash:cargo test, Bash:cargo run, Read, Grep]
---
# Verify

Classify each result as `KernelTrustedClosed`, `TransitionalStrictClosed`, compat
closed-shaped, open, admitted with a specific reason, or failed. Record whether
`crates/kernel` (re-exported by `src/kernel`), legacy `src/core`, an Isar adapter,
or a compatibility fallback produced it.

For sampled adapters, `Proved` and `Rejected` precede parser-gap/legacy
fallback; only `NotApplicable` may continue. Classified `admitted:*` on
legacy sampled/search paths is diagnostic only; strict acceptance never admits.
This sampling classification does not authorize complete-source compilation.
Never count oracle-free open facts or raw database entries as proved lemmas.

For repository completion run `cargo +stable xtask verify` (including full
workspace `test`) and independent `cargo +stable xtask selftest`; independent
security audits and the global validator remain separate. For trust-boundary
changes also use `cargo +stable xtask strict`, for sampled statistics `core`,
and for compatibility matching/certification `compat`. Record actual failures
and unrun paths; a scoped result is not a full-suite pass.

Rust 文档示例单独运行 `cargo +stable xtask test --doc`；strict 门的
kernel 过滤不能代替全部 root doctests。示例使用公共 crate 导入，Isabelle
公式标成 `text`，不得靠 `ignore` 或 `no_run` 掩盖真正的 Rust 示例错误。

完整源文件验证与搜索统计分开：`TheoryProcessor` 失败不得返回 partial Theory；
仅支持单 import、实际类型声明和已实现证明命令。源方法必须完整消费，无
未知方法转 Auto 的成功回退。两套 proof 状态都需要真实 Strict/checked 结果，
完整目标匹配和合法作用域导出；synthetic goal、Compat fact 不是结案证据。

The independent strict fixture uses `!!P::prop. PROP P ==> PROP P` with
`by assumption`, not `(rule impI)`; the sampled `HOL::TrueI` token is a separate
audited source projection (`KernelTrustedClosed: 1/125`). Run actual positive
CLI fixtures and wrong-goal/missing-`end` rejection cases for source changes;
SessionBuilder's no-CLI path needs separate public API smoke for release isolation.

词法分段成功不代表命令语法合法：`?` 是方法标点，不应作为词法错误。
`end ?` 必须在完整文件加载时拒绝；strict 不返回 accepted token，legacy
必须丢弃此前暂存的定理。保留非法词法尾部和这两层接受边界的独立回归。

ATP reconstruction 必须消费每步实际证据；错误证据不能因输入事实本来
可证明目标而回退本地搜索。rewrites 检查整个输入输出的等式证书。相关回归
位于 `tests/*_contract.rs`，不能把这些 legacy 测试计入 sampled kernel 指标。

算术契约运行 `cargo +stable xtask test --test arithmetic_proof_contract`：
合法 `HOL.Trueprop` 目标以 checked obligation 初始化；没有算术 basis 时，
六类旧算术场景必须保持未证明，不得把非空结果、自假设或零子目标当成功。
`ArithSolver` 接受前复用完整目标与授权假设检查，Pure 成功也仅为 legacy
transitional；全局 DB 集成测试仍属默认验收，不以受控 DB 替代装载覆盖。

慢路径使用 `cargo +stable xtask profile`；独立 worker 的受监督运行使用
`cargo +stable xtask supervise --worker PATH ...`。参数及重放方式见
[诊断入口](../../scripts/README.md#bounded-hol-diagnostics)。显式指定有限
墙钟、内存预算和新输出目录；记录首次至多200项装载顺序及完整 bootstrap
上下文，再用同一 manifest 重放。不得改为小 import 闭包冒充原场景提速。
以逐阶段 JSON 判定停在 bootstrap、装载还是搜索；`completed` 只表示诊断
完成，`timed_out` 不是测试通过，新的诊断入口不改变证明结果的信任等级。
Linux PID namespace 回收与 per-process 资源限制不是权限沙箱，也不保证
SIGKILL 或恶意同 UID 并发下的清理/文件完整性。

八项纯统计负载（原六项加 Tier 2/3）已迁到 `isabelle-scale-hol`，
不代表所有 scale mode 只有八项；用 `cargo +stable xtask supervise`
的 `--worker PATH --scale-mode MODE` 显式选择，模式及 Tier 2/3 保留的文件顺序、预算见
[诊断入口](../../scripts/README.md#report-only-scale-workloads)。
`cargo +stable xtask tier2`/`tier3` 默认 600 秒、4096 MiB 每进程，
环境变量 `HOL_DIAGNOSTIC_TIMEOUT_SECS` / `HOL_DIAGNOSTIC_MEMORY_MIB`
可覆盖；每次打印新日志目录。独立 worker 使用同一 `supervise` 入口并显式指定资源限制。
批次模式不提供单引理的 manifest 或逐阶段 JSON；保留 `stderr.log` 与
`supervisor.json`，不能把它描述为固定了历史扫描顺序的重放。
运行时源码路径相对调用目录；List/Nat/induction 样本使用内嵌源码。
核心125、全局 HOL 数据库、功能/信任契约及官方九文件不得有
`SyntaxError` 的兼容性断言仍是默认测试，Tier 2/3 统计不是；
完成统计不等于完整理论构建或证明成功。
