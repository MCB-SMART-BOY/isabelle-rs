# 开发者指南

## 环境要求

- Rust 1.80+
- cargo

## 构建与测试

```bash
# 构建库和二进制
cargo build

# 运行全部测试（170 个）
cargo test

# 仅运行文档测试
cargo test --doc

# 运行特定测试
cargo test --lib -- test_load_real_hol --nocapture
```

## 项目结构

```
src/
├── core/           # LCF 可信内核（最小化，不可侵犯）
├── hol/            # HOL 理论加载器 + 定理数据库
├── isar/           # Isabelle/Isar 解析（tokenizer, term parser, proof）
├── kernel/         # 派生规则 + 数据管理
├── document/       # Snapshot-based 文档模型
├── fleche/         # Flèche 风格增量检查引擎
├── server/         # LSP 3.17 服务器
├── session/        # 会话管理 (Actor 模型)
├── syntax/         # Rowan CST 解析器
├── theory/         # SQLite 缓存 + CLI 构建工具
├── wasm/           # WASM 运行时 + 插件 SDK
├── lib.rs          # Crate 入口
└── main.rs         # 二进制入口
```

## 添加新的 Isabelle 符号支持

### 模式 1：ASCII 操作符（简单）

1. `token.rs`：添加字符到 symbol match
2. `term_parser.rs`：添加二元/前缀操作符 handler
3. 测试

### 模式 2：`\<...>` 原生符号（推荐）

tokenizer 已原生支持，无需 `convert_syntax`。只需：

1. `term_parser.rs`：添加 `s.is_sym("\\<name>")` handler
2. 测试

### 模式 3：Cartouche 内容（`\<open>...\<close>`）

`convert_syntax` 中已处理：`\<open>` → `"`, `\<close>` → `"`。

## 引理加载调试

```rust
// 查看哪些引理未被加载
cargo test --lib -- test_per_file_stats --nocapture

// 查看特定引理的解析状态
cargo test --lib -- test_load_real_hol --nocapture
```

## 常用模式

### 优雅降级操作符

所有二元操作符应在 RHS 解析失败时返回部分结果：

```rust
if s.is_sym("=") {
    s.adv();
    if let Some(rhs) = parse_trm(s) { // 不传播 None
        head = make_binary(..., head.clone(), rhs);
    }
    return Some(head); // 即使 RHS 失败也返回
}
```

### 向前看（peek）检测

使用 `s.tokens.get(s.pos + 1)` 而非消费 token：

```rust
let next_is_range = s.tokens.get(s.pos + 1).map_or(false, |t| {
    matches!(&t.kind, TokenKind::Symbol(s) if s.as_ref() == ".")
});
```

### Term 构造

- `Term::free(name, typ)` — 自由变量
- `Term::const_(name, typ)` — 常量
- `Term::abs(name, typ, body)` — lambda 抽象
- `Term::app(func, arg)` — 函数应用
- `Typ::dummy()` — 占位类型（当前所有 term 使用）
