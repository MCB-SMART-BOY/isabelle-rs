---
description: Documentation standards. Rustdoc, architecture decision records, module-level docs, examples, doc tests.
globs: "**/*.rs"
alwaysApply: true
version: 1.0
updated: 2026-05-29
---

# Documentation Rules

> "Documentation is a love letter that you write to your future self." — Damian Conway

## 触发条件

始终应用 — 添加新模块、公共 API、或复杂逻辑时。

## 铁律

1. **所有 `pub` 项必须有 rustdoc** — 至少一行描述 + 示例
2. **每个模块必须有 `//!` 模块级文档** — 描述模块的职责和主要类型
3. **复杂算法必须有内联注释** — 解释为什么而非是什么
4. **doc tests 必须可编译和运行** — `cargo test --doc`
5. **架构决策必须有 ADR** — 非显而易见的设计选择

## 模式 1: 模块级文档

```rust
//! # LCF Trusted Kernel
//!
//! This module implements the Logic for Computable Functions (LCF) style
//! trusted kernel. All theorems (`Thm`) are created exclusively through
//! the 15 primitive inference rules in `ThmKernel`.
//!
//! ## Safety Guarantee
//!
//! - `Thm` has no public constructors — theorems cannot be fabricated
//! - `CTerm` requires certification (`certify`/`certify_annotated`)
//! - All kernel rules return `Result` — no panics on invalid input
//!
//! ## Key Types
//!
//! - [`Thm`] — A certified theorem (proposition + hypotheses + derivation)
//! - [`ThmKernel`] — The 15 primitive inference rules
//! - [`CTerm`] — A certified term with known type
//!
//! ## Example
//!
//! ```
//! use isabelle_rs::core::thm::{ThmKernel, CTerm};
//! use isabelle_rs::core::logic::Pure;
//!
//! let t = Term::free("A", Typ::base("bool"));
//! let ct = CTerm::certify_annotated(t).unwrap();
//! let thm = ThmKernel::assume(&ct).unwrap();
//! assert_eq!(thm.nprems(), 0);
//! ```
```

## 模式 2: 函数级文档

```rust
/// Apply the combination rule: from `f ≡ g` and `x ≡ y`, derive `f x ≡ g y`.
///
/// # Type Safety
///
/// The result equality type is the codomain of `f`'s type. On failure,
/// returns `Err(KernelError::NotFunctionType)` if `f` is not a function type.
///
/// # Example
///
/// ```
/// let thm_f = ...; // f ≡ g  where f: 'a => 'b
/// let thm_x = ...; // x ≡ y  where x: 'a
/// let result = ThmKernel::combination(&thm_f, &thm_x)?;
/// // result: f x ≡ g y  (type: 'b)
/// ```
///
/// # Errors
///
/// - `KernelError::NotFunctionType` — `f` is not a function type
/// - `KernelError::NotEquality` — either theorem is not an equality
pub fn combination(thm_f: &Thm, thm_x: &Thm) -> Result<Thm> {
    // ...
}
```

## 模式 3: 架构决策记录 (ADR)

```markdown
# ADR-001: Use OnceLock for lazy net construction

## Status
Accepted (Phase 10.1)

## Context
Discrimination nets are expensive to build (O(n log n)) but are only
needed when performing proof search. Building all nets at load time
increases startup latency by 40%.

## Decision
Use `std::sync::OnceLock` to lazily initialize nets on first access.

## Consequences
- ✅ Faster startup (only build nets when needed)
- ✅ No external dependency (standard library)
- ⚠️ First lookup is slower (builds the net)
- ⚠️ `OnceLock::get_or_init` panics on reentrant initialization
```

## 模式 4: Doc Tests

```rust
/// Simplify a theorem using the simplifier.
///
/// ```
/// use isabelle_rs::core::thm::ThmKernel;
/// use isabelle_rs::core::simplifier::Simplifier;
///
/// // x + 0 = x  (simplified)
/// let thm = Simplifier::rewrite(&goal, &simps).unwrap();
/// assert_eq!(thm.nprems(), 0);
/// ```
///
/// # Panics
///
/// Panics if the simplifier encounters an unhandled pattern.
/// (To be fixed in Phase 28)
pub fn rewrite(goal: &Thm, simps: &[Arc<Thm>]) -> Option<Thm> {
    // ...
}
```

## 模式 5: 错误文档

```rust
/// Errors that can occur during kernel operations.
#[derive(Error, Debug)]
pub enum KernelError {
    /// Returned when `combination()` is called with a non-function term.
    ///
    /// # Example
    ///
    /// ```
    /// // A: bool (not a function), so combination fails
    /// let result = ThmKernel::combination(&thm_a, &thm_x);
    /// assert!(matches!(result, Err(IsabelleError::Kernel(
    ///     KernelError::NotFunctionType(_)))));
    /// ```
    #[error("not a function type: {0:?}")]
    NotFunctionType(Typ),

    /// Returned when a dummy type is found where a proper type is required.
    ///
    /// This should never occur in production code — it indicates a bug
    /// where `Typ::dummy()` leaked into the kernel.
    #[error("dummy type found in certified term for operation '{op}'")]
    DummyType { op: &'static str },
}
```

## 文档层次

```
项目文档 (README.md)
├── 架构文档 (docs/ARCHITECTURE.md)
│   └── ADR (决策记录)
├── 开发者指南 (docs/DEVELOPMENT.md)
├── 路线图 (docs/ROADMAP.md)
├── 功能对比 (docs/ISABELLE_COMPARISON.md)
├── 变更日志 (CHANGELOG.md)
├── 规则文件 (.claude/rules/)
│   ├── 域规则 (kernel, isar, proof-methods, ...)
│   └── 工程规则 (error-handling, api-design, ...)
└── 内联文档 (rustdoc)
    ├── 模块级 (//!)
    ├── 函数级 (///)
    └── 内联注释 (//)
```

## 检查清单

- [ ] 每个 `pub` struct/enum/fn/trait 有 `///` 文档
- [ ] 每个 `.rs` 文件有 `//!` 模块文档
- [ ] 公共 API 有 `# Examples` 部分
- [ ] 可能失败的函数有 `# Errors` 部分
- [ ] 会 panic 的函数有 `# Panics` 部分
- [ ] `unsafe` 函数有 `# Safety` 部分
- [ ] doc tests 通过 (`cargo test --doc`)
- [ ] 复杂算法有解释性注释
- [ ] 非显而易见的设计选择有 ADR

## 反模式

| ❌ | ✅ |
|----|----|
| `/// Creates a new Foo.` | `/// Creates a new Foo with default configuration.` |
| 无示例的公共 API | 至少一个 `# Examples` doc test |
| `// increment i` | `// i tracks the number of remaining subgoals` |
| 过时的文档 | 及时更新 (或删除) |
| 注释解释 "做了什么" | 解释 "为什么这样做" |
| `// TODO: fix this` | `// TODO(phase-22): replace with proper type deduction` |
