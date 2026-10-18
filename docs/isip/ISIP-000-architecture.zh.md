# ISIP-000：架构与可信边界

**ISIP 版本：** 草案 0.1
**状态：** 仅为设计，不表示当前实现符合规范。目前只存在本规范与总览；
ISIP-100 至 ISIP-600 仍为规划。
**依赖：** 无（此为根设计规范）

## 1. 范围

ISIP-000 定义 ISIP 兼容证明平台的分层系统架构。它确立可信计算基（TCB）、依赖方向以及可信内核操作与不可信平台服务之间的边界。

实现现状：严格 TCB 已位于 `crates/kernel/`，仅依赖 `sha2` 和
`thiserror`；`src/kernel/mod.rs` 负责重导出。自动化迁移之前的捆绑 HOL
采样记录为 `TransitionalStrictClosed: 0/125`、`KernelTrustedClosed: 1/125`，
仅涉及 `HOL::TrueI` 经审计的源码投影；独立 Pure/HOL fixture 不计入采样。
后续按 P1 合同恢复实施的原生 P2/P3/P4 闭环尚未重跑这份采样或闭合更广泛的
HOL 可信门；该记录不授权 ISIP 运行时工作，也不代表整套理论执行、协议或
一致性测试已实现。
另行批准的[原生兼容计划](../status/ROADMAP.md#approved-native-compatibility-program)
以官方 Isabelle/ML 和 PIDE 能力为目标；B 包只有历史官方参考侧基线，C–H
尚未验收，不能与 ISIP 阶段混为一谈。另行批准的编译期 Rust 原生插件方向
不构成 ISIP 分层实现或平台兼容验收。历史 A 包结果见
[xtask 迁移记录](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)，
2026-10-14 原生自动化结果见[当前验证记录](../status/PROJECT_STATUS.md#native-rust-automation-verification-2026-10-14)，
当前命令见[工程工作流](../guides/DEVELOPMENT.md#engineering-workflow)。

## 2. 分层模型

ISIP 兼容系统**必须**至少组织为以下四层：

### Layer 0：可信计算基

TCB 是其正确性对定理可靠性不可或缺的组件集合。

**规划中的 TCB 职责：** 定理类型、原始推理规则、已认证项/命题、理论祖先、证书检查器、`accept_closed_theorem` 操作。这是设计约束，并非实现完整性的证明。

**不得包含或依赖：** ISIP、MCP/LSP/A2A、AI 模型、异步运行时、数据库、网络 I/O、WASM、GPU 计算、LSP 处理器、JSON 序列化、会话状态、文档版本、证明搜索算法。

**依赖：** 仅限于密码学哈希（`sha2`）和错误处理（`thiserror`）。在 Isabelle-rs 中，这是 `isabelle-kernel` crate。

**零警告策略：** TCB **必须**在 `RUSTFLAGS="-D warnings"` 下零警告编译通过；这是设计要求，不表示当前所有质量门均已通过。

### Layer 1：逻辑后端

负责声明感知解析、名称解析、已检查精化、逻辑基础清单、公理/定义实例化。

**规划接口：** `trait LogicBackend`，拟包含 `elaborate`、
`available_actions`、`apply`、`check` 方法；目前尚无此 trait。

**职责：** Pure/HOL 精化、类型推断、sort 检查、逻辑基础清单。
严格内核负责验证安装的公理模式及重放定理推导；逻辑层不授予定理权限。

**不得：** 直接构造 `TrustedTheorem` 值。所有定理构造必须通过 Layer 0。

### Layer 2：文档与证明运行时

无头、编辑器无关的引擎，管理文档版本、增量更新、依赖图、诊断、取消、语义标记、证明快照、目标和 fork/rollback/replay。

**规划接口：** `trait DocumentEngine` 和 `trait ProofSession`；
目前代码中尚无这些 trait。

**规划中的 schema（尚非现有 ISIP 运行时类型）：** `DocumentRevision`、`ProofSnapshot`、`BranchId`、`GoalId`、`StateTransition`、`StateDiff`、`Diagnostic`、租约管理及垃圾回收。

**不得：** 依赖任何特定编辑器、IDE、AI 框架或协议。

### Layer 3：适配器

将 ISIP 语义映射到特定客户端协议的薄协议适配器。

**包含：** LSP 适配器、MCP 适配器、A2A 适配器、CLI 适配器、Native SDK。

**不得：** 拥有证明状态、构造定理或做出信任决策。适配器仅转换请求/响应。

## 3. 依赖方向

依赖**必须**严格向下流动。禁止 Layer 0 依赖任何更高层，尤其是
MCP、LSP、A2A、JSON-RPC、Tokio、HTTP、AI、GPU 或 WASM。以下是目标架构，
并非声明当前 ISIP 运行时已实现。

## 4. 稳定与实验代码隔离

规划中的 `stable` / `experimental` crate 分类，目前在 workspace 中尚无
受强制执行的元数据或依赖政策；Cargo 不会自动强制执行此类分类。未来实现须
建立明确的规则及检查：实验 crate 不得进入稳定 crate 的依赖图，也不得构造
或认证 `TrustedTheorem`；TCB（Layer 0）始终属于稳定层。

## 5. 定理权限

外部客户端可以提交：引用、候选动作、候选推导、候选证书。

**不得**提交：`TrustedTheorem` 令牌、`KernelThm` 值、已认证项/命题值、理论扩展权限。

所有外部标识符均为查询引用，绝不构成定理能力。运行时必须根据当前理论祖先
解析外部标识符，才能授权任何依赖定理身份的操作。

## 6. 推测执行

运行时可以在隔离分支中执行证明动作。推测分支**不得**扩展可信理论。
推测结果在验收前**必须**重放或证书检查；失败的推测分支可以被垃圾回收。

## 7. ISIP-000 不规定的内容

本规范不规定内核实现细节、Isar 语法、具体证明方法、
构建系统/包管理、网络传输/序列化格式，也不规定 AI 模型架构或训练。

## 8. 一致性

实现须实际证明下列行为，才可以声明符合 ISIP-000；
当前 Isabelle-rs 不声明符合该设计规范：

1. 具有明确边界的 TCB 并记录依赖
2. 强制层级依赖方向
3. 分离稳定代码与实验代码
4. 不允许外部客户端构造定理值
5. 对可信制品要求内核验收（而非仅试验成功）
6. 区分推测状态与已验收理论扩展

## 参考文献

- [ISIP 概述](ISIP.zh.md)
- [ADR-0004: 分层平台架构 v2](../adr/ADR-0004-layered-platform-architecture-v2.md)
- [AGENTS.md: 平台架构](../../AGENTS.md)
