# Isabelle-rs

> Isabelle proof assistant kernel, rewritten in Rust. Fully parses and loads all core HOL theories.

## 愿景

Isabelle 是目前最强大的交互式定理证明器之一。Isabelle-rs 用 Rust 重写其内核和基础设施，目标是：

- **完整保留** Isabelle 的 `.thy` 语法和 Isar 证明语言
- **完整保留** LCF 可信内核架构（`Thm` 无公开构造器）
- **完整替换** 底层为 Rust，提供更好的性能、安全性和可嵌入性
- **标准 LSP** 替代 PIDE，支持任意现代编辑器

## 当前状态

| 组件 | 状态 | 说明 |
|------|:--:|------|
| 可信内核 | ✅ | **13 条推理规则**，零 panic，零 warning |
| Term 解析器 | ✅ | 完整 Isabelle 语法（量词、case、if、let、集合、列表、范围） |
| Tokenizer | ✅ | 原生 `\<...>` 符号 + 全部 ASCII 操作符 |
| 定理加载 | ✅ | **2436/2436 源声明 100% 覆盖** |
| 多行引理解析 | ✅ | assumes/shows/fixes/obtains/cartouche |
| 定理数据库 | ✅ | 2,548 条已索引（intro/elim/simp/by-name） |
| 内核基础设施 | ✅ | `instantiate` + `bicompose` + 目标状态访问 |
| 文档模型 | 🚧 | Snapshot-based incremental checking |
| LSP 服务器 | 🚧 | 7 个 handlers + Isabelle 扩展 |
| 证明引擎 | 🔵 下一步 | Tactic 层重写（`&Thm -> Vec<Thm>`） |
| 理论 DAG | 🔵 规划中 | 拓扑排序加载全部 100+ 个 .thy 文件 |
| Isar 执行 | 🔵 规划中 | proof/qed、have/show、case/induct |

### 定理覆盖明细

| 理论文件 | 源声明 | 覆盖 |
|----------|--------|:--:|
| HOL.thy | 254 | **100%** |
| Orderings.thy | 153 | **100%** |
| Nat.thy | 360 | **100%** |
| Set.thy | 412 | **100%** |
| List.thy | 1,257 | **100%** |
| **合计** | **2,436** | **100%** |

## 快速开始

```bash
# 构建
cargo build

# 运行测试（170 个，全部通过）
cargo test

# 运行 LSP 服务器
cargo run -- --lsp
```

## 架构

```
.thy 源文件
    ↓ parse_lemmas()        ← 完整 Isabelle 语法解析器
ParsedLemma { name, theorem }
    ↓ ThmKernel::assume()   ← LCF 可信内核（当前全部为 assume，非验证）
HolTheoremDb                ← 分类索引（intro/elim/simp）
    ✅ Phase 1a 完成
ThmKernel::instantiate      ← 将统一结果应用到定理
ThmKernel::bicompose        ← 核心 resolution 操作（所有 tactic 的基础）
    🔵 Phase 1b 当前
Tactic = Thm → Vec<Thm>    ← 对齐 Isabelle 架构
    🔵 Phase 1c
simp / auto                 ← 证明引擎
```

## 路线图

详见 [docs/ROADMAP.md](docs/ROADMAP.md)

| 阶段 | 目标 |
|------|------|
| ✅ 完成 | 定理表示层：100% 源声明覆盖 |
| Phase 1 | 证明引擎 MVP：simp + auto 可用 |
| Phase 2 | 自我验证：用原始 proof 脚本重新验证已加载定理 |
| Phase 3 | 理论 DAG：拓扑排序加载全部 .thy 文件 |
| Phase 4 | 库化：`cargo add isabelle-rs` |

## 文档

- [架构设计](docs/ARCHITECTURE.md)
- [开发路线图](docs/ROADMAP.md)
- [开发者指南](docs/DEVELOPMENT.md)
- [Isabelle 对照](docs/ISABELLE_COMPARISON.md)
