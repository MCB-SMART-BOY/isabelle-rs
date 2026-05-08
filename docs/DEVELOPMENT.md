# Developer Guide

## 目录结构

```
isabelle-rs/
├── Cargo.toml             # Rust 项目配置
├── src/
│   ├── main.rs            # 入口：demo 模式 / --lsp 模式
│   ├── core/              # 可信内核 (Trusted Computing Base)
│   │   ├── types.rs       #   Sort, Typ, ClassAlgebra
│   │   ├── term.rs        #   Term (de Bruijn λ-项)
│   │   ├── logic.rs       #   Pure 元逻辑 (==>, !!, ==)
│   │   ├── sign.rs        #   Signature (常量表 + 类型签名)
│   │   ├── theory.rs      #   Theory + ProofContext
│   │   └── thm.rs         #   ThmKernel (LCF 推理规则)
│   ├── document/          # 文档模型
│   │   └── document.rs    #   Document, Node, Command, Snapshot
│   ├── fleche/            # 增量检查引擎
│   │   └── engine.rs      #   Flèche, CommandExecutor
│   └── server/            # LSP 服务器
│       ├── lsp_types.rs   #   LSP 3.17 类型定义
│       ├── transport.rs   #   JSON-RPC over stdio
│       ├── handler.rs     #   请求路由与生命周期
│       └── isabelle_ext.rs #  Isabelle 专用 LSP 扩展
├── docs/                  # 文档
│   ├── README.md          #   项目概览
│   ├── ARCHITECTURE.md    #   架构设计
│   ├── ROADMAP.md         #   开发路线图
│   ├── ISABELLE_COMPARISON.md # 功能对照
│   └── DEVELOPMENT.md     #   本文件
└── isabelle-source/       # Isabelle 原始源码（参考）
    └── src/Pure/          #   82K 行 SML 内核
```

## 设计约定

### 命名约定

| 概念 | Isabelle (ML) | Isabelle-rs (Rust) |
|------|---------------|---------------------|
| 类型表达式 | `typ` | `Typ` |
| 项 | `term` | `Term` |
| 定理 | `thm` | `Thm` |
| 签名 | `sign` | `Signature` |
| 理论 | `theory` | `Theory` |
| 证明上下文 | `Proof.context` | `ProofContext` |
| 环境 | `Envir.envir` | `Envir` (TBD) |
| 策略 | `tactic` | `Tactic` (TBD) |

### 错误处理

内核层使用 `assert!` / `panic!` 处理逻辑错误（如"不是等式"、"未声明的常量"），因为内核出现这种错误意味着 bug，无法恢复。

上层（文档模型、LSP 服务器）使用 `Result<T, E>` 或 `Option<T>` 进行正常的错误处理。

### 命名空间

Isabelle 使用分层命名，如 `Pure.imp`、`HOL.eq`。Rust 版本直接将这些名称作为字符串存储：
```rust
Term::const_("Pure.imp", ...)  // 元逻辑蕴涵
Term::const_("HOL.eq", ...)    // 对象逻辑相等
```

### 不变性

`Theory` 和 `Signature` 通过 `clone()` 创建扩展版本，原始版本保持不变。这对应 Isabelle 的"理论是不可变的"原则：
```rust
let extended_sig = original_sig.extend();
// original_sig 仍然有效
```

## 如何添加新功能

### 添加新的推理规则

1. 在 `core/thm.rs` 的 `ThmKernel` 中添加方法
2. 该方法的输入只能是 `CTerm` 或 `Thm`（不能从外部构造）
3. 添加正向测试（正确输入）和负向测试（错误输入应 panic）
4. 如果规则是派生的（不是原始的），标记为 `// Derived rule`

### 添加新的 LSP 功能

1. 如果是标准 LSP 方法：在 `server/lsp_types.rs` 添加类型，在 `server/handler.rs` 添加处理方法
2. 如果是 Isabelle 扩展：在 `server/isabelle_ext.rs` 添加类型和常量
3. 在 `docs/ARCHITECTURE.md` 的 LSP 表格中更新状态

### 添加新模块

使用 Isabelle 的模块名称作为 Rust 模块名称：

```
Isabelle: src/Pure/unify.ML  →  Isabelle-rs: src/core/unify.rs
Isabelle: src/Pure/Isar/proof.ML  →  Isabelle-rs: src/isar/proof.rs
```

## 测试

### 运行所有测试

```bash
cargo test
```

### 运行特定模块的测试

```bash
cargo test core::thm      # 只测试定理内核
cargo test core::logic    # 只测试 Pure 逻辑
```

### 测试约定

- 内核测试放在对应模块文件的 `#[cfg(test)] mod tests` 中
- 每个推理规则至少一个正向测试
- 使用 `prop("A")` 等辅助函数简化构造

### 与 Isabelle 对照测试

在 `isabelle-source/` 中运行 Isabelle 获得期望输出：

```bash
cd isabelle-source
bin/isabelle console -r
> Thm.assume (Thm.cterm_of @{context} @{prop "A"});
```

将输出与 Rust 版本的 `ThmKernel::assume(...)` 的结果对比。

## 编码风格

- 使用 Rust 2024 edition
- 遵循标准 Rust 命名约定（snake_case 函数，CamelCase 类型）
- 对 Isabelle 的概念保留原始名称（如 `mk_implies`，不翻译为 `make_implication`）
- 注释使用中文（用户面向）或英文（代码注释）
- 每个文件以 `//!` 文档注释开头，说明对应 Isabelle 源文件

## 常用命令

```bash
# 开发构建
cargo build

# 发布构建
cargo build --release

# 运行演示
cargo run

# 运行 LSP 服务器（stdin/stdout 模式）
cargo run -- --lsp

# 测试
cargo test

# 查看文档
cargo doc --open

# 格式化
cargo fmt

# Lint
cargo clippy
```
