# Isabelle 功能对照

## 核心设计：不变与变化

| 方面 | 原始 Isabelle | Isabelle-rs | 说明 |
|------|:---:|:---:|------|
| **.thy 文件语法** | ✅ | ✅ 不变 | `theory Foo imports Bar begin ... end` |
| **Isar 语言** | ✅ | ✅ 不变 | `lemma`, `proof`, `qed`, `have`, `show` 等 |
| **LCF 可信任内核** | ✅ | ✅ 不变 | `Thm` 无公开构造器 |
| **Pure 元逻辑** | ✅ | ✅ 不变 | `Pure.all`, `Pure.imp`, `Pure.eq` |
| **de Bruijn 表示** | ✅ | ✅ 不变 | 绑定变量用索引 |
| **实现语言** | SML + Scala | **Rust** | 变化 |
| **编辑器协议** | PIDE (XML/YXML) | **LSP 3.17** (JSON-RPC) | 变化 |
| **编辑器生态** | jEdit + VSCode 插件 | **任意 LSP 编辑器** | 变化 |
| **构建系统** | Isabelle/Scala + Poly/ML | Cargo + Rust | 变化 |

## PIDE vs LSP

Isabelle 的 PIDE 与标准 LSP 的详细对比：

### PIDE 能做什么，LSP 如何替代？

| PIDE 功能 | 标准 LSP | Isabelle-rs 方案 |
|-----------|:--:|------|
| 文档同步 | ✅ `textDocument/didChange` | 直接使用 |
| 诊断推送 | ✅ `textDocument/publishDiagnostics` | 直接使用 |
| 类型 Hover | ✅ `textDocument/hover` | 直接使用 |
| 跳转定义 | ✅ `textDocument/definition` | 直接使用 |
| 命令执行状态 (`running`/`finished`) | ❌ | `$/isabelle/commandProgress` 扩展 |
| 证明目标推送 | ❌ | `$/isabelle/proofStateChanged` 扩展 |
| Output 面板 | ❌ | `$/isabelle/outputMessage` 扩展 |
| 逐步执行 | ❌ | `isabelle/proofStep` / `proofUndo` 扩展 |
| 嵌套语言 markup | ❌ | `textDocument/semanticTokens` (标准) |
| 撤销/重做 | ❌ | 扩展 + 文档版本管理 |

### 架构对比

```
原始 Isabelle (PIDE):
  Editor → XML/YXML → Scala Wrapper → Poly/ML Process
  (专用)   (自定义)    (JVM)          (SML)

Isabelle-rs (LSP):
  Editor → JSON-RPC → Rust Server → Flèche Engine → Rust Kernel
  (任意)   (标准)     (原生)        (增量)          (原生)
```

### 关键优势

1. **编辑器无关**：任何支持 LSP 的编辑器都能使用，不需要专门插件
2. **原生性能**：Rust 编译为原生代码，无需 JVM 或 Poly/ML 运行时
3. **生态系统**：可以使用 Rust 的整个包生态系统（serde, tokio, rowan, tower...）
4. **类型安全**：Rust 的类型系统在编译期捕获比 SML 更多的错误
5. **工具链**：cargo build/test/bench/doc 统一工具链

## 模块完成度对照

参见 [ARCHITECTURE.md](./ARCHITECTURE.md#模块对照isabelle-pure--isabelle-rs) 中的对照表。

## 测试对照

```
原始 Isabelle:
  · 内核有少量单元测试（主要在 Pure/Examples/）
  · 主要通过 HOL 理论库的构建验证正确性（回归测试）
  · 没有 fuzzing 或 property-based testing

Isabelle-rs:
  · 每条推理规则 + 类型操作都有单元测试（30 个）
  · 未来：proptest/quickcheck 随机测试
  · 未来：与 Isabelle 的 cross-validation（相同输入 → 相同输出）
```

## 性能预期

| 操作 | Isabelle (SML) | Isabelle-rs (Rust) | 预期 |
|------|:---:|:---:|------|
| Term 构造 | 堆分配 (SML) | 堆分配 (Box/Arc) | 相近 |
| Term 比较 | 递归遍历 | 递归遍历 | 相近 |
| 定理检查 | 即时的 (LCF) | 即时的 (LCF) | 相同 |
| 解析 | Earley Parser (SML) | Earley Parser (Rust) | 更快 |
| I/O | 通过 Scala 层 | 原生 Rust | 更快 |
| 内存占用 | Poly/ML GC | Rust ownership | 更低 |
| 启动时间 | JVM + Poly/ML 初始化 | 原生二进制 | 更快 |

> 注：当前 Isabelle-rs 不追求性能优化（如 Arena 分配、Hash Consing）。这些可以在后续引入，而不影响正确性。

## 与其他现代证明助手的对比

| 特性 | Isabelle-rs | Lean 4 | Coq-lsp | Rocq (原 Coq) |
|------|:---:|:---:|:---:|:---:|
| 实现语言 | Rust | Lean (自举) | OCaml | OCaml |
| 编辑器协议 | LSP | LSP | LSP | LSP (via coq-lsp) |
| 内核架构 | LCF | 类型检查器 | 类型检查器 | 类型检查器 |
| 证明语言 | Isar | Tactic + Term | Ltac2 / SSReflect | Ltac / Ltac2 |
| 自动化 | 强 (sledgehammer) | 强 (aesop, omega) | 中 (auto, lia) | 中 (auto, lia) |
| 增量检查 | ✅ (Flèche) | ✅ (Snapshot) | ✅ (Flèche) | ✅ (coq-lsp) |
