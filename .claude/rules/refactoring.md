---
description: Safe refactoring patterns for large Rust codebases. Extract module, rename, type-driven refactoring, regression safety net.
globs: "**/*.rs"
alwaysApply: false
version: 1.0
updated: 2026-05-29
---

# Refactoring Rules

> "Refactoring is a disciplined technique for restructuring an existing body of code, altering its internal structure without changing its external behavior." — Martin Fowler, Refactoring (1999)

## 触发条件

重构超过 3 个文件，或改变模块结构时应用。

## 铁律

1. **先测试，后重构** — 确保现有测试通过再开始
2. **小步前进** — 每次提交只做一个语义变更
3. **编译器是你的安全网** — 利用 Rust 的类型系统验证重构正确性
4. **不改变外部行为** — 纯粹的结构变换，不修 bug 不加功能
5. **及时回滚** — 如果重构超过 2 小时无进展，回滚重来

## 重构目录

### 1. 提取函数 (Extract Function)

```rust
// Before: 长函数
pub fn verify_lemma(lem: &ParsedLemma) -> Option<Thm> {
    // 50 lines of safe rules application
    let mut current = apply_safe_rules(&state, premises);
    if current.nprems() == 0 { return Some(current); }

    // 30 lines of built-in override
    if let Some(thm) = try_builtin_override(lem) { return Some(thm); }

    // 40 lines of Isar proof
    if let Some(thm) = try_isar_proof(lem) { return Some(thm); }

    // 60 lines of method dispatch
    // ...
}

// After: 提取策略
pub fn verify_lemma(lem: &ParsedLemma) -> Option<Thm> {
    verify_with_safe_rules(lem)
        .or_else(|| verify_with_builtins(lem))
        .or_else(|| verify_with_isar(lem))
        .or_else(|| verify_with_methods(lem))
        .or_else(|| verify_with_fallback(lem))
}

fn verify_with_safe_rules(lem: &ParsedLemma) -> Option<Thm> { ... }
fn verify_with_builtins(lem: &ParsedLemma) -> Option<Thm> { ... }
fn verify_with_isar(lem: &ParsedLemma) -> Option<Thm> { ... }
fn verify_with_methods(lem: &ParsedLemma) -> Option<Thm> { ... }
```

### 2. 提取模块 (Extract Module)

```rust
// Before: 所有核心在一个文件
// src/core/thm.rs (3000+ lines)
pub struct Thm { ... }
pub struct CTerm { ... }
pub struct ThmKernel;
pub struct Envir { ... }
pub struct TypeEnv { ... }

// After: 按关注点分离
// src/core/thm.rs       — Thm + ThmKernel (核心)
// src/core/cterm.rs     — CTerm + certify
// src/core/envir.rs     — Envir (已存在)
// src/core/types.rs     — TypeEnv (已存在)
```

### 3. 提取类型别名

```rust
// Before: 复杂类型重复
fn process(lemmas: &HashMap<String, Vec<Arc<(Thm, Vec<String>, Option<Typ>)>>>) { ... }
fn verify(lemmas: &HashMap<String, Vec<Arc<(Thm, Vec<String>, Option<Typ>)>>>) { ... }

// After: 类型别名
pub type LemmaEntry = Arc<(Thm, Vec<String>, Option<Typ>)>;
pub type LemmaMap = HashMap<String, Vec<LemmaEntry>>;

fn process(lemmas: &LemmaMap) { ... }
fn verify(lemmas: &LemmaMap) { ... }
```

### 4. 用枚举替换魔法值

```rust
// Before: 字符串匹配
match method_name {
    "auto" => auto_exec(state, 0, premises),
    "fast" => fast_exec(state, premises),
    "best" => best_exec(state, premises),
    _ => return vec![],
}

// After: 枚举驱动
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofMethod {
    Auto, Fast, Best, Safe, Simp, Blast, // ...
}

impl ProofMethod {
    pub fn from_name(name: &str) -> Option<Self> { ... }
    pub fn execute(&self, state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm> { ... }
}
```

### 5. 引入参数对象

```rust
// Before: 长参数列表
fn exec_auto(state: &Thm, depth: usize, premises: &[Arc<Thm>],
             safe_rules: &[Arc<Thm>], unsafe_rules: &[Arc<Thm>],
             bound: usize, use_nets: bool) -> Vec<Thm> { ... }

// After: 配置结构体
pub struct AutoConfig {
    pub depth: usize,
    pub bound: usize,
    pub use_nets: bool,
}

pub struct AutoContext<'a> {
    pub state: &'a Thm,
    pub premises: &'a [Arc<Thm>],
    pub safe_rules: &'a [Arc<Thm>],
    pub unsafe_rules: &'a [Arc<Thm>],
}

fn exec_auto(ctx: &AutoContext, config: &AutoConfig) -> Vec<Thm> { ... }
```

### 6. 用 Option/Result 替换 null/error code

```rust
// Before: sentinel 值
fn lookup_theorem(name: &str) -> Thm {
    // 未找到返回 axiom (危险!)
    Thm::axiom(Term::free(name, Typ::dummy()))
}

// After: Option
fn lookup_theorem(name: &str) -> Option<Arc<Thm>> {
    db.by_name.get(name).cloned()
}
```

## 重构工作流

```
1. IDENTIFY  → 识别代码异味
2. TEST      → cargo test (确保基线)
3. EXTRACT   → 小步重构
4. VERIFY    → cargo test (每次提交)
5. REPEAT    → 回到步骤 3
```

## 代码异味清单

| 异味 | 重构手段 | 工具检测 |
|------|---------|---------|
| 长函数 (>200 lines) | Extract Function | `cargo clippy` |
| 长参数列表 (>5 params) | Introduce Parameter Object | 人工审查 |
| 重复代码 | Extract Function / Module | 人工审查 |
| 过大的 struct (>10 fields) | Extract Component | 人工审查 |
| Switch on type/kind | Replace with Polymorphism | 人工审查 |
| 特性 envy (过度使用另一个模块的数据) | Move Method | 人工审查 |
| 注释解释代码 | Extract Variable / Function | 人工审查 |
| 死代码 | Remove | `cargo clippy -- -W dead_code` |
| 魔术数字 | Replace with Named Constant | `cargo clippy` |
| 可变全局状态 | Encapsulate Variable | 人工审查 |

## 大型重构检查表

当重构影响 >10 个文件时:

- [ ] 创建重构分支 (`refactor/extract-foo`)
- [ ] 确认所有现有测试通过
- [ ] 识别所有调用点 (用 `grep` 或 IDE "Find Usages")
- [ ] 分步提交 (每步一个清晰语义)
- [ ] 每个提交后运行测试
- [ ] 更新受影响的文档
- [ ] 代码审查后合并

## 安全网

```bash
# 重构前获取基线
cargo test 2>&1 | tee test-before.log
cargo clippy -- -D warnings 2>&1 | tee clippy-before.log

# 每次重构后验证
cargo test 2>&1 | diff - test-before.log
cargo clippy -- -D warnings 2>&1 | diff - clippy-before.log
```

## 反模式

| ❌ | ✅ |
|----|----|
| 同时重构 + 加功能 | 纯重构，功能分离 PR |
| 一次改 20 个文件 | 每次 1-5 个文件 |
| 不先写测试 | 测试先行 |
| 手动重命名 | IDE 重构工具 (rust-analyzer) |
| 保持 dead code "以备后用" | 删除 (git 历史可恢复) |
| 过度抽象 (YAGNI) | 仅在明确需要时抽象 |
