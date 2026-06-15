---
description: Error handling best practices for Rust. thiserror patterns, Result propagation, error type design, kernel invariants, panic-free guarantees.
globs: "**/*.rs"
alwaysApply: false
version: 1.0
updated: 2026-05-29
---

# Error Handling Rules

> "Errors are values, not exceptions." — Rust's core philosophy applied to theorem proving.

## 触发条件

添加新错误类型、修改 `src/core/error.rs`、或在任何模块中使用 `Result` 时应用。

## 铁律

1. **内核层禁止 `panic!` / `unwrap()` / `expect()`** — 必须返回 `Result<T, IsabelleError>`
2. **每个 Result 必须被使用** — 启用 `#[deny(unused_must_use)]`
3. **错误信息必须可操作** — 包含上下文 (变量名、类型、位置)
4. **不要吞掉错误** — 不要 `let _ = fallible()` 或 `if let Err(_) = ...`
5. **错误类型分层** — Kernel/Type/Proof/Parse/Io 各司其职

## 错误分层架构

```
IsabelleError (顶层)
├── KernelError    — 可信内核不变式违反 (不可恢复)
├── TypeError      — 类型系统错误
├── ProofError     — 证明搜索失败 (可重试)
├── Parse          — 语法错误
├── Io             — 文件/网络 I/O
└── Config         — 配置错误
```

## 模式 1: 使用 thiserror

```rust
// ✅ 推荐: thiserror 派生
#[derive(Error, Debug)]
pub enum KernelError {
    #[error("not a function type: {0:?}")]
    NotFunctionType(Typ),

    #[error("type mismatch: expected {expected:?}, got {actual:?}")]
    TypeMismatch { expected: Typ, actual: Typ },

    #[error("dummy type found in certified term for operation '{op}'")]
    DummyType { op: &'static str },
}

// ❌ 避免: 手写 Display + 丢失上下文
#[derive(Debug)]
enum BadError {
    TypeErr(String),  // 丢失类型信息
}
```

## 模式 2: 错误传播

```rust
// ✅ 推荐: ? 操作符 + 类型转换
fn reflexive(ct: &CTerm) -> Result<Thm> {
    let typ = ct.term_type();
    let t = ct.term().clone();
    let eq = Pure::mk_equals(typ.clone(), t.clone(), t);
    let ct_eq = CTerm::certify_annotated(eq)?;  // ← 自动向上转
    ThmKernel::assume(&ct_eq)
}

// ❌ 避免: 手动 unwrap
fn reflexive_bad(ct: &CTerm) -> Thm {
    let ct_eq = CTerm::certify_annotated(eq).unwrap(); // panic risk
    ThmKernel::assume(&ct_eq).unwrap()
}
```

## 模式 3: 错误附加上下文

```rust
// ✅ 推荐: .map_err() 附加上下文
fn load_theory(path: &Path) -> Result<Theory> {
    let source = std::fs::read_to_string(path)
        .map_err(|e| IsabelleError::Io(e))?;
    TheoryProcessor::process_source(&source)
        .map_err(|e| IsabelleError::Config(
            format!("in {}: {}", path.display(), e)
        ))
}

// ✅ 推荐: anyhow 风格的 bail! (轻量场景)
fn check_arity(name: &str, expected: usize, actual: usize) -> Result<()> {
    if expected != actual {
        return Err(TypeError::ArityMismatch {
            name: name.to_string(),
            expected,
            actual,
        }.into());
    }
    Ok(())
}
```

## 模式 4: 不可恢复 vs 可恢复

```rust
// 🔴 不可恢复 — 内核不变式违反 (应该不可能发生)
// 返回 Err(KernelError::...) → 调用者决定是否 abort
pub fn combination(thm_f: &Thm, thm_x: &Thm) -> Result<Thm> {
    let fn_typ = dest_fun_type(thm_f.prop.term())?;
    match fn_typ.dest_fun() {
        Some((_, cod)) => { /* 正常路径 */ }
        None => return Err(KernelError::NotFunctionType(fn_typ).into()),
    }
}

// 🟡 可恢复 — 证明搜索失败 (正常情况)
pub fn auto_exec(state: &Thm, depth: usize) -> Vec<Thm> {
    // 返回空 Vec 表示无法证明 (不是错误)
    if depth > 15 { return vec![]; }
    // ...
}
```

## 模式 5: 防御性编程

```rust
// ✅ 推荐: 前置条件检查
pub fn forall_intr(thm: &Thm, x: &Variable) -> Result<Thm> {
    // 检查 free_in
    if thm.hyps.iter().any(|h| free_in(x, h.term())) {
        return Err(KernelError::FreeVarInHypotheses {
            name: x.name().to_string()
        }.into());
    }
    // 检查是 forall 命题
    let (bound, body) = Pure::dest_all(thm.prop.term())
        .ok_or_else(|| KernelError::NotForall(thm.prop.term().clone()))?;
    // ... proceed
}

// ❌ 避免: 假设前置条件满足
fn forall_intr_bad(thm: &Thm, x: &Variable) -> Thm {
    let (_, body) = Pure::dest_all(thm.prop.term()).unwrap(); // panic if not forall
    // ...
}
```

## 模式 6: Option vs Result

| 场景 | 返回类型 | 示例 |
|------|---------|------|
| 预期可能失败 (正常) | `Option<T>` | `unify::matchers()`, `db.by_name.get()` |
| 意外失败 (错误) | `Result<T, E>` | `ThmKernel::combination()`, `CTerm::certify()` |
| 不含信息的失败 | `Option<T>` | `Pure::dest_equals(term)` |
| 需要信息的失败 | `Result<T, E>` | `Pure::dest_equals_with_type(term)` |

## 检查清单

- [ ] 新函数返回 `Result` 而非 `panic!`
- [ ] 所有 `unwrap()`/`expect()` 有文档说明为何不可能失败
- [ ] 错误变体包含足够的上下文信息
- [ ] 错误类型在正确的层级 (Kernel vs Proof vs Parse)
- [ ] `#[from]` 自动转换正确配置
- [ ] 顶层错误处理不吞掉错误

## 反模式

| ❌ | ✅ |
|----|----|
| `unwrap()` 在库代码 | `?` 传播 |
| `String` 作为错误类型 | 结构化枚举 |
| `eprintln!` + `return` | `Err(ProofError::...)` |
| 吞掉错误 (`let _ = ...`) | 显式处理或传播 |
| 通用 `anyhow::Error` | 特定于域的错误类型 |
| panic 在 proof search | 返回 `vec![]` 或 `None` |
