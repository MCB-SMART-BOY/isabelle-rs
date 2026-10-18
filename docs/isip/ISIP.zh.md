# ISIP：Isabelle 结构化交互与证明标准

ISIP 是 Isabelle-rs 项目提出的规范草案。标题中的“标准”指这一拟议规范体系，
不表示已被外部标准组织采纳，也不声称获得 Isabelle 开发者或其所属机构的背书。

**版本：** 草案 0.1
**状态：** 仅为设计规范，尚无 ISIP 运行时。严格内核 crate 已存在。自动化迁移前
的捆绑 HOL 采样记录为 `TransitionalStrictClosed: 0/125`、
`KernelTrustedClosed: 1/125`：仅 `HOL::TrueI` 经审计的源码投影、受检基础与
定义、Pure 传输及 owner replay 获得接受。独立 Pure/HOL fixture 不计入采样。
之后按 P1 合同恢复实施的原生 P2/P3/P4 闭环尚未重跑这份采样，也没有闭合更广泛的
HOL 可信门或授权实现 ISIP 运行时。
另行批准的[原生兼容计划](../status/ROADMAP.md#approved-native-compatibility-program)
以官方 Isabelle 能力（含 Isabelle/ML 与 PIDE）为目标；B 包仅有历史官方参考侧
基线，C–H 尚未验收。另行批准的编译期 Rust 原生插件方向既不是 ISIP 的实现，
也不代表广泛平台兼容已验收；ISIP 阶段不能替代官方 PIDE/ML 兼容。
**权威参考：** [AGENTS.md](../../AGENTS.md)、
[ADR-0004](../adr/ADR-0004-layered-platform-architecture-v2.md) 与实现现状
[PROJECT_STATUS.md](../status/PROJECT_STATUS.md)。

## 概述

ISIP 是项目拟议的一套面向编辑器无关、模型无关、传输无关的证明交互规范。其目标是为现代证明工程平台定义语义模型、运行时行为、证据格式、线协议和集成规范，使人类开发者、IDE、AI Agent 和自动化证明器能够通过单一无头运行时协同工作。

ISIP 不是单一的 RPC 协议，而是一个分层规范体系。

## 七份规范的规划

目前仅有本总览与 [ISIP-000](ISIP-000-architecture.zh.md) 草案（另有对应
[英文总览](ISIP.md) 与 [英文 ISIP-000](ISIP-000-architecture.md)）。
ISIP-100 至 ISIP-600 只是规划中的标题与范围，尚无规范正文或运行时实现。

| 规范 | 标题 | 范围 |
|------|------|------|
| [ISIP-000](ISIP-000-architecture.zh.md) | 架构与可信边界 | 系统分层、TCB 定义、依赖方向 |
| ISIP-100（规划） | 语义模型 | DocumentRevision、ProofSnapshot、Goal、Fact、Action、Transition |
| ISIP-200（规划） | 运行时模型 | 状态生命周期、分支、推测执行、取消、租约 |
| ISIP-300（规划） | 证据与信任模型 | 证明轨迹、证书、内核验收、oracle/admit、信任策略 |
| ISIP-400（规划） | 线协议 | JSON-RPC 2.0 方法、通知、错误码、能力协商 |
| ISIP-500（规划） | 集成规范 | LSP、MCP、A2A、Native SDK、CLI/CI 映射 |
| ISIP-600（规划） | 安全与一致性 | 权限、沙箱、审计、威胁模型、兼容性等级 |

### 依赖方向

```text
ISIP-500 集成层（LSP, MCP, A2A, CLI, Native）
    ↓ 依赖于
ISIP-400 线协议
    ↓ 依赖于
ISIP-200 运行时 + ISIP-300 证据
    ↓ 依赖于
ISIP-100 语义模型
    ↓ 依赖于
ISIP-000 架构 + 内核 TCB
```

**关键规则：** 内核（Layer 0）**不得**依赖 ISIP、MCP、LSP、A2A、JSON-RPC 或 AI。所有 ISIP 规范描述的是内核**之上**的内容，绝不侵入内核。这是规划的依赖模型，并非已实现 ISIP 一致性。

## 分层架构

```text
┌─────────────────────────────────────────────────────┐
│ IDE │ AI 主机 │ 多 Agent │ CLI/CI │ Web/Cloud       │
├─────────┬──────────┬──────────┬──────────┬───────────┤
│   LSP   │   MCP    │   A2A    │ ISIP-CLI │ Native SDK│  ← ISIP-500
├─────────┴──────────┴──────────┴──────────┴───────────┤
│                    ISIP-Wire                         │  ← ISIP-400
├─────────────────────────────────────────────────────┤
│           规划中的 ISIP 运行时与语义                  │  ← ISIP-100/200（规划）
│  文档运行时 │ 证明运行时 │ 搜索运行时                   │
│  分支运行时 │ 制品运行时 │ 信任服务                     │
├─────────────────────────────────────────────────────┤
│              逻辑后端 / 精化                          │  ← Layer 1，非 ISIP-300
│  Pure/HOL │ DTT │ 分离逻辑 │ SMT/SAT 检查器           │
├─────────────────────────────────────────────────────┤
│          密封内核 API / 证书检查器                     │  ← ISIP-000 边界
└─────────────────────────────────────────────────────┘
```

ISIP-300 是规划中的跨层证据与信任模型，并非逻辑后端层。上图为目标架构，
并不表示 ISIP 服务已部署或符合规范。

## 身份模型

ISIP 规划四类身份；以下名称为设计示例，并不表示运行时类型已存在：

| 类别 | 示例 | 属性 |
|------|------|------|
| **内容身份** | `TheorySnapshotId`, `TrustedArtifactId` | 不可变，由规范内容计算 |
| **运行时句柄** | `ProofSnapshotHandle`, `TaskId` | 会话内有效，不透明，非持久 |
| **可变引用** | `BranchId`, `SessionId` | 指向当前内容身份 |
| **外部引用** | JSON-RPC 中的 `"thm:abc"` | 仅查询，不授予定理权限 |

## 信任模型

核心公式：

```text
权威快照
    +
类型化动作
    ↓
推测性转换 + 状态差异 + 信任增量
    ↓
选中的证据
    ↓
独立检查（重放或证书验证）
    ↓
内核验收的制品
```

规划中的 ISIP-300 将定义四个子模型：
- **逻辑依赖：** 使用的公理、定义、定理
- **来源追溯：** 方法、求解器、Agent、源版本
- **信任负担：** admit、oracle、未检查的外部结果
- **证据状态：** 证书、推导重放、内核验收

## 六条规范性要求

1. **内核不得依赖 ISIP、MCP、LSP、A2A、JSON-RPC 或 AI。**
2. **外部标识符不得构成定理权限。**
3. **推测状态不得直接扩展可信理论。**
4. **StateDiff 不得作为状态的权威表示。**
5. **搜索可以是不确定的，但选中的证据必须可独立检查。**
6. **跨逻辑复用必须要求显式的翻译证据。**

## 规划中的 ISIP 阶段（与原生兼容 A–H 包不同）

ISIP **仍仅为设计**；一条采样可信 HOL token 不代表更广泛的 HOL 可信闭环，
也不足以授权实现 ISIP 运行时。捆绑采样结果为 `TransitionalStrictClosed: 0/125`、
`KernelTrustedClosed: 1/125`，只来自 `HOL::TrueI` 的窄范围审计源码投影。
独立 Pure/HOL fixture 不计入采样；此路径未执行其他 HOL/ML 命令。

| ISIP 阶段 | 前置条件 | 内容 |
|-----------|---------|------|
| **阶段 0（当前）** | 无 | 本总览与 ISIP-000 草案；ISIP-100、ISIP-300 仍在规划中 |
| **阶段 1：可观察** | 更广泛的 TCB 闭环；单独 1/125 不充分 | `proof/getSnapshot`、`proof/getGoals`、`proof/getContext`、诊断 |
| **阶段 2：事务式** | 阶段 1 | `ProofSnapshotId`、`LogicalAction`、`StateTransition`、`StateDiff` |
| **阶段 3：分支+Agent** | 阶段 2 | `fork`、`moveHead`、`tryBatch`、`explore`、预算、取消、MCP Profile |
| **阶段 4：证据感知** | 阶段 3 | 推导重放、证书检查、制品持久化、理论扩展 |
| **阶段 5：多逻辑** | 阶段 4 | 第二逻辑后端、TranslationEvidence、A2A Profile |

详见 [ROADMAP.md](../status/ROADMAP.md) 的 TCB 前置条件与另行批准的原生兼容计划。
自动化历史 A 包结果见 [xtask 迁移记录](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)，
2026-10-14 原生自动化结果见[当前验证记录](../status/PROJECT_STATUS.md#native-rust-automation-verification-2026-10-14)；
当前命令见[工程工作流](../guides/DEVELOPMENT.md#engineering-workflow)。

## ISIP 不管辖的内容

- 内核内部数据结构
- `accept_closed_theorem` 的实现方式
- 表示定理的 Rust 类型
- AI 模型选择或训练
- Isar 语言语法
- 具体证明方法实现
- 构建系统或包管理

## 参考文献

- [ISIP-000: 架构与可信边界](ISIP-000-architecture.zh.md)
- [ADR-0004: 分层平台架构 v2](../adr/ADR-0004-layered-platform-architecture-v2.md)
- [PROJECT_STATUS.md](../status/PROJECT_STATUS.md)
- [AGENTS.md](../../AGENTS.md)
