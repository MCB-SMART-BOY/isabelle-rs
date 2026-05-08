# Architecture

## 总览

```
                        Editor (VSCode / Emacs / Neovim / ...)
                           │
                           │ LSP (JSON-RPC 2.0 over stdio)
                           │  · standard methods (hover, completion, ...)
                           │  · custom extensions ($/isabelle/proofState, ...)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│                    server/  (LSP Server)                     │
│  ┌──────────────┐  ┌──────────────┐  ┌────────────────────┐  │
│  │ lsp_types.rs │  │ transport.rs │  │ isabelle_ext.rs    │  │
│  │ LSP 3.17     │  │ JSON-RPC     │  │ custom extensions  │  │
│  │ type defs    │  │ over stdio   │  │ (proofState, etc.) │  │
│  └──────────────┘  └──────────────┘  └────────────────────┘  │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐    │
│  │               handler.rs (Request Router)            │    │
│  │  initialize / shutdown / didOpen / didChange /       │    │
│  │  hover / completion / definition / proofGoals        │    │
│  └──────────────────────┬───────────────────────────────┘    │
└─────────────────────────┼────────────────────────────────────┘
                          │
                          ▼
┌──────────────────────────────────────────────────────────────┐
│                  fleche/  (Incremental Engine)                │
│                                                              │
│  ┌─────────────────┐    ┌──────────────────┐                 │
│  │ CommandExecutor │    │ Fleche           │                 │
│  │ (trait)         │    │ · open_file()    │                 │
│  │ · execute(cmd)  │    │ · update_file()  │                 │
│  └─────────────────┘    │ · check_file()   │                 │
│                         │ · get_proof()    │                 │
│                         └────────┬─────────┘                 │
└──────────────────────────────────┼───────────────────────────┘
                                   │
                                   ▼
┌──────────────────────────────────────────────────────────────┐
│                 document/  (Document Model)                   │
│                                                              │
│  Document ──owns──▶ Node (one per file)                      │
│                 ▶ versioned                                  │
│                 ▶ snapshot-based                             │
│                                                              │
│  Node ──contains──▶ [Command, Command, ...]                  │
│      ──contains──▶ [Snapshot, Snapshot, ...]                 │
│                                                              │
│  Command: source text + kind (Lemma, Proof, Apply, ...)      │
│  Snapshot: diagnostics + proof state (immutable checkpoint)  │
└──────────────────────────────────┬───────────────────────────┘
                                   │
                                   ▼
┌──────────────────────────────────────────────────────────────┐
│                    core/  (Trusted Kernel)                    │
│                                                              │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐     │
│  │ types.rs │  │ term.rs  │  │ logic.rs │  │ sign.rs  │     │
│  │          │  │          │  │          │  │          │     │
│  │ Sort     │  │ Term     │  │ Pure.imp │  │ Signature│     │
│  │ Typ      │  │ de Bruijn│  │ Pure.all │  │ TypeSig  │     │
│  │ Algebra  │  │          │  │ Pure.eq  │  │          │     │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘     │
│                                                              │
│  ┌──────────────────┐  ┌──────────────────────────────┐      │
│  │ theory.rs        │  │ thm.rs                       │      │
│  │                  │  │                              │      │
│  │ Theory           │  │ ThmKernel (ONLY constructor) │      │
│  │ ProofContext     │  │ · assume    · reflexive      │      │
│  │ add_theorem()    │  │ · symmetric · transitive     │      │
│  │ lookup_theorem() │  │ · β-conv    · implies_intr   │      │
│  └──────────────────┘  │ · implies_elim · trivial     │      │
│                        └──────────────────────────────┘      │
│                                                              │
│                    ┌──────────────────┐                      │
│                    │ TCB Boundary     │                      │
│                    │ (Trusted Code)   │                      │
│                    │ ThmKernel is the │                      │
│                    │ ONLY way to      │                      │
│                    │ produce a Thm    │                      │
│                    └──────────────────┘                      │
└──────────────────────────────────────────────────────────────┘
```

## 模块对照：Isabelle Pure → Isabelle-rs

| Isabelle Pure (ML) | 行数 | Isabelle-rs (Rust) | 状态 |
|---|---|---|---|
| `term.ML` | 1,143 | `core/term.rs` | ✅ |
| `type.ML` | 729 | `core/types.rs` | ✅ |
| `sorts.ML` | 506 | `core/types.rs` (ClassAlgebra) | ✅ |
| `logic.ML` | 693 | `core/logic.rs` | ✅ |
| `sign.ML` | 597 | `core/sign.rs` | ✅ |
| `theory.ML` | — | `core/theory.rs` | ✅ |
| `context.ML` | 864 | `core/theory.rs` (ProofContext) | ✅ |
| `thm.ML` | 2,752 | `core/thm.rs` | ✅ (9/9 rules) |
| `unify.ML` | 668 | `core/unify.rs` | ✅ |
| `envir.ML` | 428 | `core/envir.rs` | ✅ |
| `term_subst.ML` | — | `core/term_subst.rs` | ✅ |
| `tactic.ML` + `tactical.ML` | — | `core/tactic.rs` | ✅ |
| `pattern.ML` | 526 | `core/pattern.rs` | ❌ |
| `proofterm.ML` | 2,248 | `core/proofterm.rs` | ❌ |
| `Isar/proof.ML` | 1,370 | `isar/proof.rs` | ✅ |
| `Isar/toplevel.ML` | 788 | `isar/toplevel.rs` | ✅ |
| `raw_simplifier.ML` | 1,576 | `core/simplifier.rs` | ✅ |
| `PIDE/*` | ~10,000 | `server/*` (LSP) | ✅ (替代) |
| Integration | — | `fleche/engine.rs` → `RealExecutor` | ✅ (内核集成) |
| `Syntax/*` | ~4,000 | `syntax/*` | ❌ |
| `HOL/*` | ~100,000 | `hol/*` | ❌ |

## 三层架构

### 第一层：可信内核 (core/)

内核是 Isabelle-rs 的 **Trusted Computing Base (TCB)**。这一层的任何 bug 都可能导致 `False` 被证明。因此内核设计遵循：

1. **最小化**：只有 9 条原始推理规则，尽可能小以减少 bug 面
2. **抽象性**：`Thm` 没有公开构造函数
3. **不可变性**：`Theory`、`Signature` 都是不可变的（通过 clone-on-extend）
4. **可审计性**：每个 `Thm` 携带 `Derivation` 记录来源

#### 数据流

```
Theory (签名 + 公理)
    │
    ▼
ProofContext (局部 fix/assume)
    │
    ▼
CTerm (经过签名的项)
    │
    ▼
ThmKernel.assume(ct) → Thm  ← 唯一创建 Thm 的途径
    │
    ├── ThmKernel.implies_intr → Thm (discharge)
    ├── ThmKernel.implies_elim → Thm (modus ponens)
    ├── ThmKernel.reflexive → Thm
    ├── ThmKernel.symmetric → Thm
    ├── ThmKernel.transitive → Thm
    ├── ThmKernel.combination → Thm
    ├── ThmKernel.abstraction → Thm
    └── ThmKernel.beta_conversion → Thm
```

### 第二层：文档模型 (document/ + fleche/)

文档模型负责管理 `.thy` 文件的编辑状态。受以下设计影响：

- **Isabelle PIDE**: `Document.Node`, `Command`, versioned snapshots
- **Lean 4**: per-command `Snapshot` tree, `InfoTree`
- **Coq-lsp/Flèche**: cache-aware incremental checking, fork-point diff

#### 增量检查流程

```
文件编辑
    │
    ▼
┌─────────────────┐
│ 1. 解析为命令    │  按 Isabelle 语法拆分 Commands
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 2. 计算 fork    │  新旧命令列表 diff → 最后一个不变的位置
│    point        │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 3. 保留旧快照    │  fork point 之前的 Snapshot 全部保留
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 4. 重新执行      │  从 fork point+1 开始，逐条执行命令
│    后续命令      │  产生新的 Snapshot
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 5. 发布诊断      │  publishDiagnostics → LSP Client
└─────────────────┘
```

### 第三层：LSP 服务器 (server/)

将文档模型和内核的能力暴露为标准 LSP 接口。

#### 标准 LSP 方法

| LSP Method | Isabelle-rs 实现 |
|---|---|
| `initialize` | 声明服务器能力（hover, completion, proofGoals） |
| `shutdown` | 清理状态 |
| `textDocument/didOpen` | 打开文件 → parse → check → publishDiagnostics |
| `textDocument/didChange` | 增量更新文件 → re-check → publishDiagnostics |
| `textDocument/didClose` | 关闭文件，释放资源 |
| `textDocument/hover` | 返回光标处的类型信息 |
| `textDocument/completion` | 返回自动补全候选项 |
| `textDocument/definition` | 跳转到定义 |
| `textDocument/publishDiagnostics` | 推送错误/警告 |

#### Isabelle 自定义 LSP 扩展

参照 Coq-lsp (`coq-lsp/*`) 和 Lean 4 (`$/lean/*`)：

| 扩展方法 | 方向 | 用途 |
|---|---|---|
| `$/isabelle/proofStateChanged` | Server→Client | 证明状态变化推送 |
| `$/isabelle/commandProgress` | Server→Client | 命令执行进度（forked/running/finished） |
| `$/isabelle/outputMessage` | Server→Client | Output 面板消息 |
| `isabelle/proofStep` | Client→Server | 前进一步 |
| `isabelle/proofUndo` | Client→Server | 撤销一步 |
| `isabelle/waitForChecking` | Client→Server | 等待检查完成 |

## 关键设计决策

### 为什么用 de Bruijn 而不是命名表示？

Isabelle 内部使用 de Bruijn 索引表示绑定变量。这避免了 α-等价性的复杂检查，使替换操作更简单。缺点是可读性差，但我们可以通过 pretty printer 恢复名字。

### 为什么用 Arc<str> 而不是 String？

理论中的常量名（如 `Pure.imp`）会被引用数千次。`Arc<str>` 允许共享不可变的字符串切片，减少内存分配。未来可以考虑引入全局字符串 interner 进一步优化。

### 为什么 Theory 用 Arc 包装？

Isabelle 的理论是不可变的——扩展理论创建新理论。`Arc<Theory>` 允许在多个证明上下文中安全共享同一个理论对象。当创建新理论时，通过 `Signature::extend()` 创建派生的签名。

### PIDE vs LSP 的选择

详见 [ISABELLE_COMPARISON.md](./ISABELLE_COMPARISON.md#pide-vs-lsp)。

## 测试策略

- **内核测试**：每条推理规则至少一个正向测试（正确输入产生期望输出）和一个负向测试（错误输入触发 panic）
- **文档模型测试**：fork point 计算、命令分类
- **Flèche 测试**：有效文件零诊断、无效文件检测错误
- **未来**：引入 QuickCheck 风格的随机测试生成（随机 term/type → 执行推理规则 → 验证不变量）
