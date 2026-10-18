# Isabelle-rs 代理指南（中文摘要）

> 完整英文版见 [AGENTS.md](AGENTS.md)。本文为中文摘要，以英文原文为权威参考。

## 项目定位

Isabelle-rs 是一个受 Isabelle/Pure 启发的 Rust LCF 证明内核研究原型，**不是** Isabelle 的完整 Rust 重写。

本轮自动化迁移之前最后一次 `core` 源码支撑采样使用仓库捆绑的五个 HOL
理论文件、每文件 25 条带证明的候选，历史结果为：

```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

仅 `HOL::TrueI` 的受审计源码投影获得 accepted token；这不是整个
HOL 理论编译。2026-10-03 Gitlink 样本的 `1/125` transitional、
`0/125` kernel 仅是切换前历史记录。

长期目标见 [A–H 原生兼容程序](docs/status/ROADMAP.md#approved-native-compatibility-program)。
四个 workspace 成员分别是默认成员根产品 `isabelle-rs`、可信内核
`isabelle-kernel`、不提供定理权限的离线证据包 `isabelle-evidence` 和
独立维护自动化 `xtask`。自动化迁移和独立全项目阻断见
[当前交付记录](docs/status/PROJECT_STATUS.md#current-delivery-state)。
B 的九根官方参考观察仅为冻结历史，不能冒充原生 Rust 验收。JVM-free
策略在访问 workspace 前禁用 `reference prepare/build/inventory`，仅保留
离线 `reference compare`；不得启动官方 runtime 或新 solver。
P2/P3/P4 已按 [P1 已批准设计](docs/status/TRUST.md#p1-native-trust-design)
恢复实施，但不等于兼容性验收。`native_thm` / `native_thm_variables`
外部 Rust consumer 已有局部实际闭环，不是完整 ML `Thm: THM`、ROOT/HOL
或九根兼容；见 [THM 接口清单](docs/status/NATIVE_THM_INTERFACE_INVENTORY.md)
与 [最新原生进度](docs/status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19)。
已批准编译期 Rust 原生插件和明确 JVM-only 服务的仅加载期禁用延迟链接；
这不表示完整原生构建已通过。既有宿主清理阻断解除前不得再次启动 solver。
近期依赖与退出证据见
[下一交付计划](docs/status/ROADMAP.md#next-delivery-plan-2026-10-19)，
它不新增实施/发布授权。实际 ROOT 停止点以
[本次核对记录](docs/status/PROJECT_STATUS.md#source-backed-documentation-audit-and-delivery-plan-2026-10-19)
为准，不从 Rust consumer 或 Context API 存在推断原样源码已执行。

## 双内核边界

```text
crates/kernel/ → 已提取的 isabelle-kernel TCB crate
src/kernel/    → 严格内核公开 API 的根 crate re-export
src/core/      → 遗留隔离区（仅限 bug 修复和迁移适配）
```

独立的 `TrustedTrueI.thy` 和 `TrustedPureIdentity.thy` 已通过严格源编译
返回 accepted token，但不计入上述 125 条采样。Pure 源形式是
`!!P::prop. PROP P ==> PROP P` 配合 `by assumption`，不接受旧 `impI` 别名。

类型声明、arity 和 `SignatureId`、basis 安装前完整 schema 检查、
定义与 owner replay 的共同验证，以及 binder premise-local Free 作用域
均已实现。legacy loader 按文件事务发布；完整解析、真实 Strict/checked
证明结案及自动化证书检查不等于新内核授权，不能提高 sampled kernel 指标。
算术 solver 也必须检查完整目标、Strict/checked 证据与显式上下文假设；
`arith_tac` 的非空结果或零子目标不是成功证据。受控算术回归与默认全局
数据库集成分别验收，不增加新的算术 basis 或 trusted token。
当前身份版本见[严格内核不变量](docs/kernel/KERNEL_PRIMITIVES.md#global-invariants)，
不沿用历史 `SignatureId` v2 的 digest 契约。

## 目标平台架构（不是全部已实现）

| 层 | 职责 |
|----|------|
| 0 — TCB | `isabelle-kernel`：不可变定理构造、验收、重放。零警告，无异步。 |
| 1 — 逻辑 | Pure/HOL 精化、已检查判断、逻辑基础 |
| 2 — 运行时 | 无头文档/证明引擎（未来） |
| 3 — 适配器 | CLI/LSP/Agent（无定理权限） |

## ISIP 愿景

ISIP（Isabelle 结构化交互与证明标准）是长期交互设计，见
[ISIP 中文概述](docs/isip/ISIP.zh.md)。当前仅有概述与 ISIP-000 架构草案；
ISIP-100 至 ISIP-600 仍待编写。sampled `1/125` 只是局部前置证据，不等于
完整 TCB/前端闭环，也不单独授权 ISIP runtime 实现。

## 警告策略

- TCB：**零警告**（`RUSTFLAGS="-D warnings"` 强制实施）
- 根 crate：跟踪基线，禁止净增警告
- 永不恢复 `#![allow(warnings)]`

## 统一工程工作流

遵循 [SCOPE → DESIGN → IMPLEMENT → REVIEW → VERIFY → DELIVER](docs/guides/DEVELOPMENT.md#engineering-workflow)。
先明确用户可感知的目标、事实源和范围，再做最小设计；破坏性操作或实质
改变目标/风险时确认。按风险独立审查，先行为证明和项目门，再运行完整
`~/.omp/agent/validate.sh`。失败、阻断和未运行均不能写成通过。
这六阶段是任务流程，不是 A–H 实施包或旧可信阶段的完成度。

## 验证入口

```bash
cargo +stable xtask verify      # 完整仓库代码/测试矩阵，安全门独立
cargo +stable xtask strict      # 严格内核门禁
cargo +stable xtask checkpoint  # strict + 聚焦测试
cargo +stable xtask core        # 125 定理样本快照
cargo +stable xtask docs        # 文档策略检查
```

workspace 默认成员仍只有根产品；自动化自检用 `cargo +stable xtask selftest`，
完整 workspace 测试用 `cargo +stable xtask test`。`all` 包含 Tier 诊断，
不代替完整测试或全局 validator。CI 与 `verify` 使用 workspace/all-targets 严格 Clippy。

八项纯统计 HOL 负载（原六项及 Tier 2/3）改由显式
`isabelle-scale-hol` 模式执行，并非所有 scale mode 都只有八项。
`cargo +stable xtask tier2`/`tier3` 锁定构建 worker 并受监督运行；
默认 600 秒墙钟、4096 MiB 每进程地址空间限制，可用
`HOL_DIAGNOSTIC_TIMEOUT_SECS` / `HOL_DIAGNOSTIC_MEMORY_MIB` 覆盖。
每次打印新的日志目录，检查其中 `stderr.log`、`supervisor.json`；
独立 worker 通过 `cargo +stable xtask supervise --worker PATH ...` 运行。
见[诊断模式](scripts/README.md#report-only-scale-workloads)。没有新增 ignore；
核心125、全局 HOL 数据库、现有功能/信任契约与官方九文件不得出现
`SyntaxError` 的兼容性断言仍在默认测试中，Tier 2/3 统计不在其中。
回归结果与诊断结果分别报告，完成统计不等于理论构建或证明成功。

## 关键规则

- 未获明确授权，不提交、推送、改写历史或删除分支；一次提交指令只执行一次提交
- 保留无关工作，报告脏状态；不把工作区或 PR 状态冻结进文档
- TCB 变更需要独立审查；并行修改按文件分配所有权，不擅自创建 worktree
- 跨 harness 审查不等于向新 provider 外发数据的授权；遵循
  [数据交付边界](AGENTS.md#cross-harness-data-handoffs)，只传递必要、已授权且脱敏的材料
- 严格门通过不等于完整质量门通过；全量测试、扫描和 lint 阻断见
  [当前验证记录](docs/status/PROJECT_STATUS.md)
