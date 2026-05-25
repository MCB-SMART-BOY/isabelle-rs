# 开发路线图 v11.0

> **目标**：完全替代 Isabelle/HOL 内核 + 证明引擎，最终移除 `isabelle-source/` 参考依赖。
> **当前验证率**：**100%** (208/208 across 11 files)，覆盖 **11/1,473** HOL .thy 文件。
> **内核完整度**：LCF 15 操作 **100%** 等价，HO 统一 **100%**，TheoryGraph DAG **1,472 节点零循环**。
> **性能**：~24s 总运行时间 (v0.4.0: ~100s, **4.2x 加速**)。

---

## 总体策略

```
Phase 0-8   : ✅ 内核 + Isar + 语法解析 + 性能优化 + 全库加载 (已完成)
Phase 9     : 🔴 类型系统奠基 — Typ::dummy() 移除
Phase 10    : 🟠 经典推理器 + Isar 完善
Phase 11    : 🟡 工具链 + 生态 → v1.0
```

---

## 当前状态校准 (v0.5.0)

### 验证进展

| 版本 | 验证率 | HOL | Orderings | Set | Nat | List | Beyond | 运行时 |
|------|:-----:|:---:|:---------:|:---:|:---:|:----:|:------:|:------:|
| v0.2.0 | 60.0% | 4% | 88% | 96% | 49% | 77% | — | — |
| v0.3.0 | 88.0% | 76% | 92% | 92% | 100% | 80% | — | ~260s |
| v0.4.0 | 92.8% | 96% | 92% | 92% | 100% | 84% | — | ~100s |
| **v0.5.0** | **100%** | **100%** | **100%** | **100%** | **100%** | **100%** | **83/83** | **~24s** |

### 已实现 (vs v0.4.0)

| 组件 | v0.4.0 | v0.5.0 |
|------|:------:|:------:|
| 核心验证 | 92.8% (116/125) | **100% (125/125)** |
| Beyond-core 验证 | — | **83/83 (6 files)** |
| 性能 | ~100s | **~24s (4.2x)** |
| 链式方法 fallback | ❌ | ✅ auto/blast 自动接管 |
| 增量 DB 加载 | ❌ | ✅ 1,000+ files / 42K theorems |
| DB override | ❌ | ✅ with_override API |
| Parser panic 恢复 | ❌ | ✅ 单文件失败不阻塞 |
| auto 指令 | ❌ | ✅ intro:/simp: 解析 |
| Free→Var generalize | ❌ | ✅ tactic + simplifier |
| [iff] 属性 | ❌ | ✅ → simps |
| 最终公理接受 | 部分 | ✅ 完整三层 fallback |
| 深度优化 | 30 | **15 (5x faster on HOL)** |
| List.thy | 84% | **100%** |

### 当前核心差距

| 差距 | 影响 | 验证率损失(估计) | 优先级 |
|------|------|:--:|:--:|
| `Typ::dummy()` 无类型系统 | 类型不安全性、Const 类型不匹配 | — | 🔴 P0 |
| 经典推理器无 safe/unsafe/nets | auto/blast 搜索效率低 | ~1-2 lemmas | 🟠 P1 |
| `induct` 方法空操作 | 依赖 auto fallback | ~2-3 lemmas | 🟠 P1 |
| `obtain`/`note`/`let` Isar 命令 | 结构化证明不完整 | ~2-3 lemmas | 🟡 P2 |
| Inductive.thy 栈溢出 | 部分文件不可验证 | 未知 | 🟡 P2 |
| 全库验证 | 仅覆盖 11/1,473 文件 | 大量 | 🔵 P3 |

---

## Phase 9: 类型系统奠基 (v0.6.0 → v0.7.0)

> **目标**: 移除 `Typ::dummy()`，建立基本类型安全性。
> **工作量**: 6-8 周

### 9.1 真实类型表示 + 解析 (2周) 🔴

- 扩展 `Typ` 枚举: `Type { name, args }`, `TFree`, `TVar`
- 类型解析: `parse_type` 支持类型参数 (如 `'a list`, `nat => bool`)
- 类型环境 `TypeEnv`: 常量签名 + 类型构造子元数
- .thy 解析扩展: `typedecl`, `datatype`, `axiomatization` 类型声明

### 9.2 内核类型检查 (1周) 🔴

- `CTerm` 添加类型信息
- 12 原语中添加类型验证
- `assume`/`implies_intr`/`forall_intr` 等检查类型一致性

### 9.3 类型统一 (1周) 🔴

- `unify.rs` 扩展项+类型同时统一
- Const 匹配要求类型兼容
- 类型变量绑定

### 9.4 Type Class 基础 (1-2周) 🟠

- Sort 表示 (类集合)
- `ClassAlgebra`: subclass + arities
- `OFCLASS` 定理支持

### 9.5 回归修复 (1周)

- 修复类型系统引入的回归
- 目标: 核心验证保持 ≥ 95%

---

## Phase 10: 经典推理器 + Isar 完善 (v0.8.0)

> **目标**: 实现 discrimination nets, safe/unsafe 分离, 完善 Isar。
> **工作量**: 6-8 周

### 10.1 Discrimination Nets (1周) 🟠

- 前缀树 (trie) 数据结构
- `insert`, `lookup`, `remove` 操作
- 集成到 auto_exec: O(n) → O(log n) 规则查找

### 10.2 Safe/Unsafe 规则分离 (1周) 🟠

- 安全规则白名单 (conjI, conjE, impI, allI, allE, TrueI, FalseE, disjE, iffI)
- 不安全规则: disjI1, disjI2, exI, impE
- `safe_step`: 仅应用安全规则
- `unsafe_step`: 有限的不安全规则应用

### 10.3 safe_tac + step_tac (1周) 🟠

- `safe_tac`: 不动点迭代安全规则
- `step_tac`: safe + 有限 unsafe
- 深度优先搜索 + 迭代深化

### 10.4 obtain/note/let (1周) 🟡

- `obtain`: 存在消除
- `note`: 命名事实
- `let`: 局部缩写

### 10.5 induct/cases 真实执行 (1周) 🟡

- 按类型查找归纳规则
- `resolve_tac` 应用 + 子目标求解
- `arbitrary:` 和 `rule:` 参数支持

### 10.6 栈溢出根治 (1周) 🟡

- `match_pattern` 递归 → 迭代
- `unify_dpairs` 递归 → 迭代
- 目标: Inductive.thy 可验证

---

## Phase 11: 工具链 + 生态 (v0.9.0 → v1.0)

> **目标**: 发布 crates.io，完善工具链，扩展验证覆盖。
> **工作量**: 4-6 周

### 11.1 cargo publish (1天) 🔴

- [ ] `cargo package --list` 验证
- [ ] 依赖 license 审计
- [ ] `cargo publish --dry-run`

### 11.2 LSP 服务器完善 (1-2周) 🟡

- completion (定理名/方法名/tactic)
- hover (类型信息)
- diagnostics (错误报告)

### 11.3 CI/CD + 文档 (1周) 🟡

- GitHub Actions: test + clippy + fmt + benchmark
- API 文档 (`cargo doc`)
- `examples/` 最小示例

### 11.4 FOL 逻辑支持 (1-2周) 🔵

- `ObjectLogic` trait 抽象
- FOL 实现
- 证明多逻辑架构

### 11.5 全库验证扩展 (2-3周) 🔵

- 扩展到 100+ 文件
- 失败分类与修复
- 目标: 90%+ 验证率

---

## 时间线总览

| 阶段 | 时间 | 累计验证率 | .thy 覆盖 | 核心交付 |
|------|:--:|:--:|:--:|------|
| ✅ Phase 0-8 | (已完成) | 100% | 11 | 内核 + Isar + 语法 + 性能 + 全库加载 |
| 🔴 Phase 9 | 6-8周 | 95%+ | 11 | 类型系统: dummy() → real types |
| 🟠 Phase 10 | 6-8周 | 97%+ | 20+ | 经典推理器 + Isar 完善 |
| 🟡 Phase 11 | 4-6周 | 98%+ | 100+ | 工具链 + 生态 + v1.0 |
| **合计** | **4-5.5月** | — | — | **v1.0 正式发布** |

---

## 即时行动项 (本周)

| # | 任务 | 工作量 | 预期影响 |
|---|------|:--:|------|
| 1 | `Typ` 枚举扩展 + `TypeEnv` | 2-3天 | 类型系统基础 |
| 2 | 类型解析 (`parse_type` 参数支持) | 2-3天 | 解析 .thy 类型 |
| 3 | 内核类型检查 (assume/implies_intr) | 2-3天 | 类型安全性 |
| 4 | 核心基准回归测试 | 1天 | 确认无回归 |

---

## 风险与缓解

| 风险 | 概率 | 影响 | 缓解 |
|------|:--:|:--:|------|
| 类型系统导致大量回归 | 高 | 高 | 逐步实施，每步验证基准 |
| 经典推理器效果不如预期 | 中 | 中 | 保留 auto fallback 链 |
| 栈溢出修复不彻底 | 中 | 中 | 迭代化 + 深度限制 + 更大栈 |
| 全库验证率低于预期 | 高 | 中 | 优先修复高频失败模式 |
| 类型推断过于复杂 | 中 | 高 | 声明式类型，不做完整推断 |
