# V1 → V3 Migration Plan

## 原则

```
1. 每次只改一个文件
2. 每次 cargo test 必须全绿
3. arena.rs 基础设施已就位，逐步接入
4. 不使用批量正则脚本
```

## Step 0: V1 恢复 ← ✅ 完成 (2025年7月)

恢复所有文件到最后一个已知工作状态（127 tests, 1 pre-existing failure）。

## Step 1: arena.rs 接入 (零代码改动)

```
· arena.rs 已存在，但不被任何模块使用
· 状态: ✅ 完成

## Step 2: Symbol = Arc<str> 别名 ✅ 完成

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

## Phase 2 (额外): 模块合并 ✅ 完成 (2025年7月)

```
· kernel/derived.rs ← drule.rs + more_thm.rs + conjunction.rs + bires.rs (7 tests)
· kernel/data.rs    ← facts.rs + consts.rs + net.rs (7 tests)
· 原文件保留在 core/ 中，通过 kernel/mod.rs 桥接
· 新测试全部通过 (127/128, 1 pre-existing failure)
```

## Phase 3: Session Actor ✅ 完成 (2025年7月)

```
· session/file_worker.rs — FileWorker with Document + CommandExecutor + Toplevel
· session/session.rs     — Session managing HashMap<uri, FileWorkerHandle>
· fleche/engine.rs       — Fleche now delegates to Session (backward compatible)
· 通信: tokio::mpsc (commands) + oneshot (replies)
· 5 个集成测试全部通过
· 旧 Mutex<Document> 瓶颈已消除 (Document 现在是 FileWorker 独占)
```

## Phase 4: Tactic AST ✅ 完成 (2025年7月)

```
· core/tactic.rs — Box<dyn Fn> → enum Tactic { All, No, Assume, Resolve, Then, OrElse, Repeat, Every, First }
· Tactic::apply(&self, &Goal) → Vec<Vec<Goal>>  (解释器)
· Tactic::simplify(self) → Self  (代数化简)
· Debug + Display impl (可打印 tactic 结构)
· isar/method.rs — 适配 tactic::assume_tac().apply(&goal)
· 10 个测试全部通过 (含 3 个 simplify 测试)
```

## Phase 5: LSP Tower ✅ 完成 (2025年7月)

```
· lsp/handlers/  — 7 个独立 handler 模块 (lifecycle, document, hover, completion, definition, proof_goals)
· lsp/router.rs  — HashMap dispatch table (method → handler fn)
· HandlerContext — 共享上下文 (tx + fleche + lifecycle), 提供 send_result/send_error/publish_diagnostics
· server/handler.rs — 精简为薄层, 委托给 Router
· server/transport.rs — outgoing_tx 公开以便 HandlerContext 使用
· 5 个新测试 (router dispatch + lifecycle handler)
· 141 测试通过, 1 预存失败
```

## Phase 6: Rowan CST ✅ 完成 (2025年7月)

```
· Cargo.toml — 添加 rowan = "0.15"
· syntax/parser.rs — SyntaxKind (35 variants) + IsabelleLanguage + CstBuilder + SyntaxTree
· syntax/ast.rs     — CST→AST bridge (from_syntax)
· syntax/syntax_phases.rs — 管道 parse_ast / parse_cst
· 11 个新测试 (5 parser + 3 ast + 3 syntax_phases)
· 152 测试通过, 1 预存失败
```

## Phase 7: WASM 插件 ✅ 完成 (2025年7月)

```
· wasm/mod.rs      — Plugin trait + PluginContext
· wasm/runtime.rs  — WasmRuntime (wasmtime 29, fuel metering, memory isolation)
· wasm/host.rs     — 2 host functions (host_lookup, host_debug) + ThmTable
· wasm/sdk.rs      — PluginGoal, PluginTerm, PluginResult (serde types)
· isar/method.rs   — Method::WasmPlugin variant + "wasm:" prefix parsing
· 7 个新测试全部通过
· 159 测试通过, 1 预存失败
```

## Phase 8: 持久化 + Web + CLI ✅ 完成 (2025年7月)

```
· theory/cache.rs  — SQLite TheoryCache (SHA256 hash, store/lookup/list/remove, 3 tests)
· src/lib.rs        — 库入口 (re-export 13 个模块)
· src/main.rs       — 精简为薄入口 (import from isabelle_rs)
· src/bin/isabelle-build.rs — CLI build 工具 (clap, 4 个选项)
· Cargo.toml        — rusqlite, clap, bincode, sha2; 2 个 binary target
· 162 测试通过, 1 预存失败
```

## 检查清单

```
每次 Step 完成后:
□ cargo test --all
□ cargo clippy --all
□ 所有测试全绿
□ 无新增 warning
```
