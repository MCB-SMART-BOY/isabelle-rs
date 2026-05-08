# V1 → V3 Migration Plan

## 原则

```
1. 每次只改一个文件
2. 每次 cargo test 必须全绿
3. arena.rs 基础设施已就位，逐步接入
4. 不使用批量正则脚本
```

## Step 0: V1 恢复 ← 当前

恢复所有文件到最后一个已知工作状态（117 tests）。

## Step 1: arena.rs 接入 (零代码改动)

```
· arena.rs 已存在，但不被任何模块使用
· 状态: ✅ 完成
```

## Step 2: Symbol = Arc<str> 别名

```
在 types.rs 中:
  pub type Symbol = Arc<str>;
  pub type Class = Symbol;
  
改动: 零。只是添加类型别名。
测试: 全部通过 (Symbol 就是 Arc<str>)
```

## Step 3: 逐模块替换 Arc<str> → Symbol

```
每次只改一个文件:

Module 1: types.rs
  · Sort.classes: BTreeSet<Arc<str>> → BTreeSet<Symbol>
  · Typ name fields: Arc<str> → Symbol
  · 影响: 零 (Symbol = Arc<str>)

Module 2: term.rs
  · Term name fields: Arc<str> → Symbol
  · 影响: 调用者不需要改动 (Symbol 实现所有 Arc<str> trait)

Module 3: logic.rs
  · dest_implies/dest_equals/dest_all 中的 name.as_ref() 比较
  · 改为: *name == intern("Pure.imp") (O(1) 比较)

Module 4: sign.rs
  · Signature 内部 HashMap<Arc<str>, ..> → HashMap<Symbol, ..>
  · const_type() / is_declared() 使用 intern()

Module 5-25: 剩余模块，逐个迁移
```

## Step 4: thread_local! interning

```
一旦所有模块使用 Symbol:
  · 添加 thread_local! { static SYMBOLS: SymbolTable }
  · intern(s) 返回 Symbol (u32)
  · Symbol 不再是 Arc<str> 别名，而是 u32
  · 改动: 构造器不变 (intern() 内部处理)
```

## Step 5: 完整 Arena (远期)

```
· TermId 替代 Box<Term>
· TypeId 替代 Typ enum
· 每个 FileWorker 独立 Arena
```

## 检查清单

```
每次 Step 完成后:
□ cargo test --all
□ cargo clippy --all
□ 所有测试全绿
□ 无新增 warning
```
