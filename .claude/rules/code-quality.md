---
description: Code quality standards. Clippy, rustfmt, unsafe audit, lint levels, code review checklist, technical debt management.
globs: "**/*.rs"
alwaysApply: true
version: 1.0
updated: 2026-05-29
---

# Code Quality Rules

> "Any fool can write code that a computer can understand. Good programmers write code that humans can understand." — Martin Fowler

## 触发条件

始终应用 — 代码审查、提交前检查、重构时。

## 铁律

1. **0 clippy warnings** — `cargo clippy -- -D warnings` 必须通过
2. **rustfmt 统一格式** — `cargo fmt -- --check` 必须通过
3. **`#[deny(unsafe_code)]` 仅在 `unsafe` 模块中允许**
4. **每个 `unsafe` 块必须有 SAFETY 注释**
5. **函数长度 ≤ 200 行** (超过则提取子函数)
6. **文件长度 ≤ 2000 行** (超过则拆分模块)

## 必须启用的 Lint

```rust
// lib.rs 或 main.rs 顶部
#![deny(
    unused_must_use,        // 忽略 Result 是 bug
    unused_imports,         // 未使用的导入
    unused_variables,       // 未使用的变量
    unreachable_code,       // 不可达代码
    deprecated,             // 使用了弃用 API
    rust_2018_idioms,       // Rust 2018+ 惯用写法
    missing_docs,           // 缺少文档 (pub items)
)]
#![warn(
    clippy::all,            // 所有 clippy lint
    clippy::pedantic,       // 迂腐级 clippy lint
    clippy::nursery,        // 实验性 clippy lint
    clippy::cargo,          // Cargo.toml lint
)]
```

## Clippy 分类

| 级别 | 含义 | 操作 |
|------|------|------|
| `clippy::correctness` | 明确的 bug | 立即修复 |
| `clippy::perf` | 性能问题 | 修复或文档说明 |
| `clippy::style` | 代码风格 | 按项目风格调整 |
| `clippy::complexity` | 过度复杂 | 简化或文档说明 |
| `clippy::pedantic` | 过于迂腐 | 逐条判断 |

## 模式 1: rustfmt 配置

```toml
# rustfmt.toml (项目根目录)
max_width = 100
tab_spaces = 4
edition = "2024"
use_small_heuristics = "Max"
newline_style = "Unix"
format_strings = true
imports_granularity = "Crate"
group_imports = "StdExternalCrate"
reorder_imports = true
```

## 模式 2: Unsafe 审计

```rust
// ✅ 安全模式: unsafe 块最小化 + SAFETY 注释
impl HolTheoremDb {
    pub fn get() -> &'static HolTheoremDb {
        DB_OVERRIDE.with(|cell| {
            if let Some(ptr) = *cell.borrow() {
                // SAFETY: ptr 指向调用者提供的 HolTheoremDb,
                // 调用者保证在 with_override 闭包执行期间 db 存活。
                // DB_OVERRIDE 是 thread_local!, 不会跨线程访问。
                unsafe { &*ptr }
            } else {
                GLOBAL_DB.get().expect("HolTheoremDb not initialized")
            }
        })
    }
}

// ❌ 危险模式: 大 unsafe 块 + 无注释
unsafe {
    let db = &*ptr;
    db.do_thing();
    db.do_other();
    // 为什么安全？不知道
}
```

## 模式 3: 函数复杂度控制

```rust
// ✅ 推荐: 提取子函数
pub fn process_span(&mut self, span: &CommandSpan) -> Result<()> {
    match span.kind {
        CommandKind::Theory => self.process_theory(span),
        CommandKind::Lemma => self.process_lemma(span),
        CommandKind::Proof => self.process_proof(span),
        CommandKind::Definition => self.process_definition(span),
        // ... 每个分支调用独立方法
    }
}

fn process_theory(&mut self, span: &CommandSpan) -> Result<()> {
    // 聚焦于 theory 处理逻辑
}

// ❌ 避免: 巨型 match 体
pub fn process_span(&mut self, span: &CommandSpan) -> Result<()> {
    match span.kind {
        CommandKind::Theory => {
            // 50 行 theory 处理逻辑 ...
        }
        CommandKind::Lemma => {
            // 80 行 lemma 处理逻辑 ...
        }
        // ... 总计 500+ 行
    }
}
```

## 模式 4: 命名约定

| 类别 | 约定 | 示例 |
|------|------|------|
| 类型/Enum/Trait | PascalCase | `ThmKernel`, `IsabelleError` |
| 函数/方法 | snake_case | `certify_term`, `apply_safe_rules` |
| 常量 | SCREAMING_SNAKE_CASE | `MAX_DEPTH`, `DEFAULT_BOUND` |
| 模块 | snake_case | `hol_loader`, `term_parser` |
| 临时变量 | 描述性命名 | `subgoal_thm` 而非 `t` |
| 构造函数 | `new` / `with_*` / `from_*` | `TheoryProcessor::with_parent()` |

## 模式 5: 注释哲学

```rust
// ✅ 解释 "为什么" 而非 "是什么"
// 使用 matching 而非 unification 避免意外实例化自由变量
let thm = ThmKernel::bicompose_match(rule, goal, 0)?;

// ❌ 重述代码
// 将 rule 和 goal 进行 bicompose 匹配，索引为 0
let thm = ThmKernel::bicompose_match(rule, goal, 0)?;

// ✅ 标记技术债务
// TODO(phase-21): 替换所有 Typ::dummy() 为从 TypeEnv 推导的类型
let free_var = Term::free("x", Typ::dummy());

// ✅ 标记已知限制
// FIXME: induction 仅支持单个 arbitrary 变量
// 参见: https://isabelle.in.tum.de/dist/library/Pure/Pure/Isar/method.html
```

## Technical Debt 标记

| 标记 | 含义 | 示例 |
|------|------|------|
| `TODO(phase-N)` | 计划在某 Phase 修复 | `TODO(phase-34): BNF Lfp integration` |
| `FIXME` | 已知 bug | `FIXME: panic on empty sort` |
| `HACK` | 临时变通方案 | `HACK: bypass type check for records` |
| `NOTE` | 值得注意的非显而易见行为 | `NOTE: OnceLock panics on reentrant init` |
| `XXX` | 需要讨论的设计决策 | `XXX: should this return Option or Result?` |

## 提交前检查清单

```bash
# 1. 格式检查
cargo fmt -- --check

# 2. Clippy (严格)
cargo clippy -- -D warnings

# 3. 编译 (无警告)
RUSTFLAGS="-D warnings" cargo build

# 4. 测试
cargo test

# 5. 核心验证基准
cargo test test_verify_all_core_files -- --nocapture

# 6. 文档
cargo doc --no-deps --document-private-items
```

## 反模式

| ❌ | ✅ |
|----|----|
| 函数 > 200 行 | 提取子函数 |
| 文件 > 2000 行 | 拆分为模块 |
| `unsafe` 无注释 | SAFETY 文档块 |
| 魔法数字 | 命名常量 |
| 无意义的变量名 (`t`, `x1`, `tmp`) | 描述性命名 |
| TODO 无上下文 | `TODO(phase-N): 描述` |
| 注释掉的代码 | 删除 (git history 可恢复) |
| `clone()` 无必要 | 借用或 `Arc::clone` |
