---
description: API design principles for public kernel and Isar APIs. Semver, trait design, visibility, breaking changes, deprecation policy.
globs: src/core/thm.rs, src/core/types.rs, src/core/logic.rs, src/isar/method.rs, src/isar/proof.rs
alwaysApply: false
version: 1.0
updated: 2026-05-29
---

# API Design Rules

> "Good APIs are discovered, not designed." — But they still need deliberate design.

## 触发条件

添加/修改 `pub` API、设计新 trait、或计划 breaking change 时应用。

## 铁律

1. **内核 API 必须不可变** — `Thm`/`CTerm`/`ThmKernel` 公开接口仅增不减
2. **内部实现可改** — `pub(crate)` 和 `pub(super)` 不受兼容性约束
3. **Semver 严格执行** — 主版本号变更仅当内核 API breaking change
4. **Deprecation 先于 Removal** — 删除 API 前至少一个次版本标记 `#[deprecated]`
5. **所有 `pub` 项必须有 rustdoc** — 包含示例代码

## 可见性分层

```
pub            → 外部 crate 可用 (稳定承诺)
pub(crate)     → crate 内任意使用 (无兼容承诺)
pub(super)     → 仅父模块可见
pub(in path)   → 仅指定路径可见
无修饰          → 私有
```

### 实际应用

```rust
// ✅ 稳定 API: 内核公开接口
pub fn reflexive(ct: &CTerm) -> Result<Thm> { ... }     // pub
pub fn combination(thm_f: &Thm, thm_x: &Thm) -> Result<Thm> { ... } // pub

// ✅ 内部 API: 可自由重构
pub(crate) fn normalize_env(env: &mut Envir) { ... }    // pub(crate)
pub(super) fn apply_substitution(term: &Term, subst: &Subst) -> Term { ... } // pub(super)
```

## 模式 1: Trait 设计

```rust
// ✅ 推荐: 最小 trait 边界
pub trait Prover {
    fn prove(&self, goal: &Thm) -> Result<Thm>;
    fn name(&self) -> &'static str;
}

// ✅ 推荐: 使用关联类型而非泛型参数 (单实现)
pub trait TheoryStore {
    type Error;
    fn load(&self, name: &str) -> Result<Arc<Theory>, Self::Error>;
}

// ❌ 避免: 过大的 trait (trait bloat)
pub trait Everything: Prover + Parser + Printer + Checker + Serializer { ... }
```

## 模式 2: Builder 模式

```rust
// ✅ 推荐: Builder 模式用于复杂构造
pub struct TheoryProcessorBuilder {
    parent: Option<Arc<Theory>>,
    name: String,
    accept_all: bool,
    type_env: Option<TypeEnv>,
}

impl TheoryProcessorBuilder {
    pub fn new(name: impl Into<String>) -> Self { ... }
    pub fn with_parent(mut self, parent: Arc<Theory>) -> Self { ... }
    pub fn accept_all(mut self) -> Self { ... }
    pub fn build(self) -> TheoryProcessor { ... }
}
```

## 模式 3: 新类型包装

```rust
// ✅ 推荐: 语义化新类型
pub struct VarName(String);    // 不是裸 String
pub struct TheoremId(usize);   // 不是裸 usize

// ❌ 避免: 裸类型丢失语义
fn lookup(name: &str, idx: usize) -> Option<Thm> { ... }
// name 是什么? idx 是什么? 无法从签名得知
```

## 模式 4: 工厂函数优于直接构造

```rust
// ✅ 推荐: 工厂函数封装构造逻辑
impl CTerm {
    pub fn certify(term: Term) -> Result<Self> { ... }
    pub fn certify_typed(term: Term, typ: Typ) -> Result<Self> { ... }
    pub fn certify_annotated(term: Term) -> Result<Self> { ... }
}

// ❌ 避免: 暴露构造器 (破坏封装)
let cterm = CTerm { term, max_idx, term_type }; // 可能构造非法状态
```

## 模式 5: 错误类型作为 API 的一部分

```rust
// ✅ 推荐: 公共错误类型在 API 中暴露
pub fn certify(term: Term) -> Result<CTerm, TypeError> { ... }
//                   调用者知道可能得到 TypeError

// ❌ 避免: 过于宽泛的错误
pub fn certify(term: Term) -> Result<CTerm, Box<dyn Error>> { ... }
//                   调用者无法匹配具体错误
```

## Breaking Change 分类

| 变更 | 兼容性 | 示例 |
|------|:---:|------|
| 新增 `pub` 函数 | ✅ 兼容 | `ThmKernel::new_func()` |
| 新增 `pub` trait 方法 (有默认实现) | ✅ 兼容 | `fn new_method(&self) {}` |
| 新增 enum 变体 | ⚠️ 非穷尽匹配会 break | `KernelError::NewVariant` |
| 新增 trait 方法 (无默认实现) | ❌ Breaking | trait 实现者必须添加 |
| 删除 `pub` 函数 | ❌ Breaking | 需要 `#[deprecated]` 过渡 |
| 改变函数签名 | ❌ Breaking | 参数/返回类型变化 |
| 改变 trait 约束 | ❌ Breaking | 泛型约束改变 |
| 缩小可见性 | ❌ Breaking | `pub` → `pub(crate)` |

## 版本策略

```
0.x.y → 无兼容性承诺 (开发阶段)
  - x: 重大功能 (Phase 完成)
  - y: Bug fix / 小改进

1.0.0 → 稳定 API 承诺
  - major: Breaking changes
  - minor: 向后兼容的新功能
  - patch: Bug fixes

当前: v0.7.0 → 不做向后兼容承诺
目标: v1.0.0 → 内核 API 冻结
```

## 检查清单

- [ ] 所有 `pub` 项有 rustdoc
- [ ] 新 API 有使用示例
- [ ] Trait 边界最小化
- [ ] 构造器正确封装
- [ ] 错误类型可被调用者匹配
- [ ] 无意外暴露的内部类型
- [ ] `#[deprecated]` 标记包含替代方案

## 反模式

| ❌ | ✅ |
|----|----|
| `pub` 暴露内部字段 | `pub(crate)` + getter |
| 泛型参数过多 (>3) | 关联类型或具体化 |
| trait 方法过多 (>10) | 拆分为多个 trait |
| 返回 `Box<dyn Error>` | 具体错误类型 |
| `&String` 参数 | `&str` |
| `&Vec<T>` 参数 | `&[T]` |
