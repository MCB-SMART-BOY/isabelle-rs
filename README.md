# Isabelle-rs

> Isabelle proof assistant, rewritten in Rust with modern toolchain integration.

## 愿景 (Vision)

**保持 Isabelle 的功能和语法完全不变，用 Rust 重写内核，用 LSP 替换 PIDE，让任意现代编辑器都能成为 Isabelle IDE。**

Isabelle 是目前最强大的交互式定理证明器之一，但其底层实现（Standard ML + Scala）和编辑器协议（PIDE）与现代开发工具链存在隔阂。Isabelle-rs 的目标不是创造一个新的证明助手，而是：

- **完全保留** Isabelle 的语法（`.thy` 文件、Isar 语言）
- **完全保留** Isabelle 的逻辑（Pure 元逻辑 + HOL/ZF/FOL 对象逻辑）
- **完全保留** Isabelle 的可信内核（LCF 架构）
- **替换** 底层实现为 Rust（更好的性能、安全、生态系统）
- **替换** PIDE 为 LSP（任意编辑器支持）

## 核心原则 (Core Principles)

1. **LCF 可信任内核不可侵犯**：`Thm` 类型没有公开构造函数，所有定理必须通过 `ThmKernel` 的推理规则产生。这是 Isabelle 正确性的基石，不可动摇。

2. **签名先行**：每个常量必须在签名中声明。不存在"凭空创造"的常量。这对应 Isabelle 的 `sign.ML`。

3. **Pure 是最小引导理论**：只声明 `Pure.all`、`Pure.imp`、`Pure.eq` 三个元逻辑常量和 `prop` 类型，不含任何公理。所有对象逻辑（HOL 等）在其上构建。

4. **标准 LSP 优于自定义协议**：Isabelle 的 PIDE 协议功能强大但与编辑器生态隔离。Isabelle-rs 使用标准 LSP 3.17 + 少量 Isabelle 专用扩展（参考 Coq-lsp 和 Lean 4）。

5. **增量检查**：受 Flèche (Coq-lsp) 和 Lean 4 Snapshot 启发，实现基于快照的增量文档检查。

## 项目状态

| 模块 | 状态 | 说明 |
|------|:--:|------|
| 类型系统 (types) | ✅ | Sort, Typ, ClassAlgebra |
| Lambda 项 (term) | ✅ | de Bruijn 表示 |
| Pure 元逻辑 (logic) | ✅ | `==>` / `!!` / `==` |
| 签名系统 (sign) | ✅ | 常量声明 + 类型检查 |
| 理论管理 (theory) | ✅ | Theory, ProofContext |
| LCF 内核 (thm) | ✅ | 9 条推理规则 |
| 文档模型 (document) | 🚧 | Command, Snapshot, Node |
| 增量引擎 (fleche) | 🚧 | Flèche 风格增量检查 |
| LSP 服务器 (server) | 🚧 | LSP 3.17 + 自定义扩展 |
| 高阶统一 (unify) | ❌ | Tier 1 |
| Isar 语言 | ❌ | Tier 2 |
| HOL 逻辑 | ❌ | Tier 6 |

## 快速开始

```bash
# 构建
cargo build

# 运行演示模式（展示内核、类型系统、理论系统）
cargo run

# 运行 LSP 服务器模式（供编辑器连接）
cargo run -- --lsp

# 运行测试
cargo test
```

## 编辑器配置

### VSCode

安装 LSP 客户端插件后，在 `.vscode/settings.json` 添加：

```json
{
  "lsp": {
    "isabelle-rs": {
      "command": ["/path/to/isabelle-rs", "--lsp"],
      "filetypes": ["isabelle"]
    }
  }
}
```

### Emacs (eglot)

```elisp
(add-to-list 'eglot-server-programs
             '(isabelle-mode . ("/path/to/isabelle-rs" "--lsp")))
```

### Neovim (nvim-lspconfig)

```lua
require('lspconfig').isabelle_rs.setup {
    cmd = { '/path/to/isabelle-rs', '--lsp' },
    filetypes = { 'isabelle' }
}
```

## 文档索引

- [架构设计](./docs/ARCHITECTURE.md)
- [开发路线图](./docs/ROADMAP.md)
- [Isabelle 功能对照](./docs/ISABELLE_COMPARISON.md)
- [开发者指南](./docs/DEVELOPMENT.md)
