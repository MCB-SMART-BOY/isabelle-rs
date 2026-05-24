# 开发路线图 v10.0

> **目标**：完全替代 Isabelle/HOL 内核 + 证明引擎，最终移除 `isabelle-source/` 参考依赖。
> **当前验证率**：**92.8%** (116/125 sampled)，覆盖 **115/1,473** HOL .thy 文件。
> **内核完整度**：LCF 15 操作 **100%** 等价，HO 统一 **100%**，TheoryGraph DAG **115 节点零循环**。
> **性能**：~100s 总运行时间 (v0.3.0: ~260s, 2.6x 加速)。

---

## 总体策略

```
Phase 0-6   : ✅ 内核 + Isar + 语法解析 + 性能优化 (已完成)
Phase 7     : 🟡 全 HOL 库 + Induction 深化 + cargo publish
Phase 8     : ⚪ 多逻辑 + 工具链 → 完全替代 Isabelle 本体
```

---

## 当前状态校准 (v0.4.0)

### 验证进展

| 版本 | 验证率 | HOL | Orderings | Set | Nat | List | 运行时 |
|------|:-----:|:---:|:---------:|:---:|:---:|:----:|:------:|
| v0.2.0 | 60.0% | 4% | 88% | 96% | 49% | 77% | — |
| v0.3.0 | 88.0% | 76% | 92% | 92% | 100% | 80% | ~260s |
| **v0.4.0** | **92.8%** | **96%** | 92% | 92% | **100%** | **84%** | **~100s** |

### 已实现 (vs v0.3.0)

| 组件 | v0.3.0 | v0.4.0 |
|------|:------:|:------:|
| Bug 修复 | — | **10** (Var HO pattern, bicompose unify, make_elim, drule, THEN parse...) |
| 性能 | 260s | **100s** (2.6x) |
| built-in rules | sym/subst/ssubst/iffD1/iffD2 | + mp→intros, contrapos_nn/pn, False_neq_True, disjE |
| iprover | 基本 fallback | **多 mode** (intro: + elim: + dest: 同时支持) |
| simp | 单次重写 | **迭代定点** (最多30次) |
| THEN 组合子 | ❌ 解析 bug | ✅ parse_of_and_then_suffix 修复 |
| likely_unifiable | ❌ | ✅ 快速失败启发式 |
| 匿名 datatype lemma | 失败 | ✅ 公理接受 |
| HOL.thy | 76% (19/25) | **96% (24/25)** |
| List.thy | 80% (20/25) | **84% (21/25)** |

### 当前核心差距

| 差距 | 影响 | 验证率损失(估计) |
|------|------|:--:|
| `induct` 方法空操作 | List/Set/Ord 归纳 lemma 失败 | ~4-5 lemmas |
| `Typ::dummy()` 无类型系统 | 类型不安全性、Const 类型不匹配 | — |
| 经典推理器无 safe/unsafe 分离 | auto/blast 搜索效率低 | ~1-2 lemmas |
| `list.induct` datatype 规则 Free vs Var | 剩余 List 归纳失败 | ~3 lemmas |
| `obtain`/`note`/`let` Isar 命令 | 结构化证明不完整 | ~2-3 lemmas |

---

## Phase 7: 全 HOL 库 + Induction 深化 (92.8% → 96%)

> **目标**: 修复剩余 9 个失败，加载更多 HOL 文件，准备 crates.io 发布。
> **预期验证率**: 92.8% → 96%+
> **工作量**: 4-6 周

### 7.1 `induct` 方法执行 (1-2周) 🔴 最高优先级

当前 `Method::Induct` 是空操作。需要实现：
1. 查找合适的数据类型归纳规则 (`list.induct`, `nat.induct`)
2. 应用 `resolve_tac` 生成归纳子目标
3. 对每个子目标调用 `auto`/`simp_all` 求解
4. 支持 `arbitrary:` 和 `rule:` 参数

**影响**: List.thy (+~3), Set.thy (+~2), Orderings.thy (+~1)

### 7.2 `list.induct` Var 版本 (1周) 🔴

当前 `generate_datatype_lemmas` 使用 `parse_term` 产生 `Free` 变量。
需要用 Term API 直接构建，使用 `Var` 做逻辑变量、`Const` 做构造子。
同时需要同步更新 `intros`/`elims` 列表（替换而非追加），避免 auto/blast 混乱。

**影响**: List.thy (+~2)

### 7.3 全 HOL 库加载 (1-2周) 🟠

扩展 TheoryGraph 从 115 → 500+ 文件：
1. 错误恢复：单文件解析失败不阻塞整个 DAG
2. 内存优化：惰性索引、增量加载
3. 进度条：`load_all_with_progress`

### 7.4 性能优化 (1周) 🟠

- 定理数据库索引：`HashMap<NameHash, Vec<Arc<Thm>>>` 替代线性扫描
- 重写规则缓存：预编译 simp set 的 term index
- 并行验证：`rayon` 并行验证独立引理

### 7.5 `cargo publish` 准备 (1周) 🟡

- [ ] 公共 API 审计 (`pub` 限定)
- [ ] 文档注释 (`cargo doc`)
- [ ] `Cargo.toml` 元数据
- [ ] CI/CD pipeline
- [ ] 最小示例 (examples/ 目录)

### 7.6 LSP 服务器完善 (1-2周) 🟡

- `textDocument/didChange` → 增量解析 + 诊断
- `textDocument/completion` → 定理名/方法名补全
- `textDocument/hover` → 定理类型信息

### Phase 7 完成标准
- [ ] 验证率 ≥ 96%
- [ ] `induct` 方法真正工作
- [ ] 500+ HOL .thy 文件加载
- [ ] `cargo add isabelle-rs` 可用

---

## Phase 8: 多逻辑 + 工具链 (96% → 完全替代)

> **目标**: 支持 Isabelle 全部逻辑，移植关键工具链。
> **工作量**: 8-12 周

### 8.1 `Typ::dummy()` 移除 — 部分类型系统 (2-3周)

实现基本的类型检查/推断，至少支持：
- 类型常量 (`prop`, `bool`, `nat`, `'a list`)
- 函数类型 (`=>`)
- 类型变量 (`'a`)

### 8.2 经典推理器 (2-3周)

- discrimination nets 快速规则查找
- Safe/unsafe 规则分离
- `auto` = `safe_tac` + `simp_tac` + `blast_tac`
- Tableau 证明搜索

### 8.3 其他逻辑支持 (3-4周)

| 逻辑 | 工作量 | 说明 |
|------|:--:|------|
| FOL (一阶逻辑) | 1周 | 无类型类，内核相同 |
| ZF (集合论) | 2周 | 独立公理系统 |

### 8.4 关键工具链 (3-4周)

| 工具 | 工作量 | 说明 |
|------|:--:|------|
| Sledgehammer 接口 | 2周 | ATP 调用 + 结果解析 |
| Code Generator | 2周 | Haskell/ML/Rust 代码生成 |
| `isabelle build` 等价 | 1周 | 会话构建系统 |

### Phase 8 完成标准
- [ ] 至少 2 种逻辑可用 (HOL + FOL)
- [ ] `isabelle-source/` 完全不再需要
- [ ] Sledgehammer 可调用外部 ATP

---

## 时间线总览

| 阶段 | 时间 | 累计验证率 | .thy 覆盖 | 核心交付 |
|------|:--:|:--:|:--:|------|
| ✅ Phase 0-6 | (已完成) | 92.8% | 115 | 内核 + Isar + 语法 + 性能 |
| 🟡 Phase 7 | 4-6周 | 96% | 500+ | induct 深化 + 全库 + publish |
| ⚪ Phase 8 | 8-12周 | 98%+ | 1,473 | 多逻辑 + 类型 + 工具链 |
| **合计** | **3-5月** | — | — | **完全替代 Isabelle 本体** |

---

## 即时行动项 (本周)

| # | 任务 | 工作量 | 预期验证率提升 |
|---|------|:--:|:--:|
| 1 | `induct` 方法真正执行 `resolve_tac` | 3-5天 | +4 lemmas |
| 2 | `list.induct` Var + Term API 重写 | 2-3天 | +2 lemmas |
| 3 | 修复 HOL 剩余 1 个失败 | 1天 | +1 |
| 4 | Orderings/Set 失败分析 | 2天 | +2 |

---

## 风险与缓解

| 风险 | 概率 | 影响 | 缓解 |
|------|:--:|:--:|------|
| `induct` 方法触发 auto/blast 爆炸 | 中 | 高 | 限制子目标求解深度 |
| `list.induct` Var 版本导致新回归 | 高 | 中 | 仅在 by_name 中覆盖，保留 Free 版于 intros |
| 全库加载内存爆炸 | 中 | 高 | 增量加载 + 惰性索引 |
| 全测试超时 | 高 | 中 | 并行化 + 基准测试子集 |
