# Isabelle-rs 项目状态（中文摘要）

> 完整英文版见 [PROJECT_STATUS.md](PROJECT_STATUS.md)。本文为中文摘要。

## 当前定位

Isabelle-rs 是一个受 Isabelle/Pure 启发的 Rust LCF 证明内核原型，重点研究 oracle 足迹追踪、闭合定理验收和证明对象重放。其研究价值在于提供一个小型 Rust 原生环境来研究定理构造边界，而非追求 Isabelle/HOL 功能对等。

## 可信指标

```text
TransitionalStrictClosed: 1/125  （HOL::TrueI 遗留迁移）
KernelTrustedClosed:      0/125  （生产路径未接通）
```

## 已完成（2026-07-21 检查点）

- 递归 `is_concrete_type`（嵌套类型变量检测）
- `is_monomorphic_instance_of` 使用 `BTreeMap<TypeVarId, Ty>`
- 原子化 `AxiomDependencyId`（替换双重条目编码）
- `prove_true_i` 通过已验收 `True_def` + `theorem_ref` 链
- TCB 零警告门禁
- 10 个 TCB 攻击测试（5 polytype, 1 axiom dep, 4 definition）

## 未完成

- `ConservativeDefinition` 已通过 `DefinitionId` 原子化，存储在 `TheoryExtension::DefineConst`，重放时沿 owner 祖先链查找证书
- `PolyType::new` 验证参数排序一致性并要求每个声明的参数都出现在 body 中；`monomorphic_instance_matches` 依据参数授权实例
- 内核→遗留转换器使用 Debug 字符串
- 生产 source→kernel 桥接未实现
- `KernelTrustedClosed` 仍为 0/125

## 完成度估算

| 范围 | 估算 |
|------|------|
| 完整 Isabelle/HOL + Isar + PIDE | 15%-25% |
| 最小端到端 Pure 可信内核 | 45%-55% |
| Oracle 足迹 + 闭合定理验收 | 65%-75% |

## 下一步优先级

1. 统一 `TypeInstantiation` 为 `TypeVarId`
2. 补齐 axiom/definition 攻击测试矩阵
3. 接通实际 source → CProp → 实际理论 → TrueI 令牌
4. 设计 ISIP 标准规范（设计文档，不实现运行时）
5. ISIP（Isabelle 结构化交互与证明标准）定义五阶段平台演进：

| 阶段 | 前置条件 |
|------|---------|
| 0: 设计 | 当前（ISIP-000, ISIP-100, ISIP-300 草案） |
| 1: 可观察 | TCB 闭合 |
| 2: 事务式 | 阶段 1 |
| 3: 分支+Agent | 阶段 2 |
| 4: 证据感知 | 阶段 3 |
| 5: 多逻辑 | 阶段 4 |

详见 `docs/isip/ISIP.zh.md`。
