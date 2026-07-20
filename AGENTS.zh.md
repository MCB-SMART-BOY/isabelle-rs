# Isabelle-rs 代理指南（中文摘要）

> 完整英文版见 [AGENTS.md](AGENTS.md)。本文为中文摘要，以英文原文为权威参考。

## 项目定位

Isabelle-rs 是一个受 Isabelle/Pure 启发的 Rust LCF 证明内核研究原型，**不是** Isabelle 的完整 Rust 重写。

当前可信指标：

```text
TransitionalStrictClosed: 1/125  （过渡期迁移分类）
KernelTrustedClosed:      0/125  （真正的新内核可信定理）
```

## 双内核边界

```text
src/kernel/  → 目标 TCB 核心（严格、不可变、零警告）
src/core/    → 遗留隔离区（仅限 bug 修复和迁移适配）
```

## 平台架构（四层）

| 层 | 职责 |
|----|------|
| 0 — TCB | `isabelle-kernel`：不可变定理构造、验收、重放。零警告，无异步。 |
| 1 — 逻辑 | Pure/HOL 精化、已检查判断、逻辑基础 |
| 2 — 运行时 | 无头文档/证明引擎（未来） |
| 3 — 适配器 | CLI/LSP/Agent（无定理权限） |

## ISIP 愿景

ISIP（Isabelle 结构化交互与证明标准）是项目的长期交互模型。详见 `docs/isip/ISIP.zh.md`。**当前仅为设计文档**，TCB 闭合前不实施。

## 警告策略

- TCB：**零警告**（`RUSTFLAGS="-D warnings"` 强制实施）
- 根 crate：跟踪基线，禁止净增警告
- 永不恢复 `#![allow(warnings)]`

## 验证入口

```bash
scripts/dev-check.sh strict      # 严格内核门禁
scripts/dev-check.sh checkpoint  # strict + 聚焦测试
scripts/dev-check.sh core        # 125 定理样本快照
scripts/dev-check.sh docs        # 文档策略检查
```

## 关键规则

- 切勿自动提交、修改、推送或重写历史
- 保留无关工作，报告脏状态
- TCB 变更需要独立审查
- 并行代理不得编辑相同的可信敏感文件
