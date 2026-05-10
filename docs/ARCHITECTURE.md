# 架构设计 v4.0

> 保留 V3 的完整架构愿景，标注每个组件的实现状态。

## 状态标记说明

| 标记 | 含义 |
|------|------|
| `[✅ 已完成]` | 代码已实现 |
| `[🚧 进行中]` | 部分实现（骨架、桩代码或半成品） |
| `[🔵 一期]` | 规划于一期（证明引擎 — Arena 激活，核心迁移） |
| `[🔵 二期]` | 规划于二期（自我验证 — Session 连线，Rowan CST 完善） |
| `[🔵 三期]` | 规划于三期（理论依赖图 — 理论导入，差分测试） |
| `[🔵 四期]` | 规划于四期（库化 — WASM 插件，模糊测试，基准测试） |
| `[⏸️ 暂缓]` | 好想法但超出当前路线图 |

## 速查表：已实现 vs 规划中

| 层 / 组件 | 状态 | 关键交付物 |
|-----------|------|-----------|
| **Layer 0: 定理加载** | `[✅ 已完成]` | parse_lemmas, convert_syntax, HolTheoremDb, 2,548 条定理 |
| **LCF 内核（11 条规则）** | `[✅ 已完成]` | assume, refl, sym, trans, comb, abs, beta, impI, impE, allI, allE |
| **Isar 证明语言** | `[✅ 已完成]` | token, parse, term_parser, proof, method, toplevel |
| **全局 Interning** | `[🚧 进行中]` | kernel/arena.rs 已存在；intern() 已激活；尚未用于 core/ |
| **Rowan CST 解析器** | `[🚧 进行中]` | CstBuilder + SyntaxTree + AST 桥接已构建（672 行） |
| **Session Actor** | `[🚧 进行中]` | Session + FileWorker + Watchdog（609 行，基于 tokio） |
| **Tactic AST** | `[✅ 已完成]` | enum Tactic + 化简器，位于 core/tactic.rs（218 行） |
| **LSP tower** | `[⏸️ 暂缓]` | 0 tower 代码；当前 server/ + lsp/ handler 无需它即可工作 |
| **WASM 插件** | `[🚧 进行中]` | wasm/ 具有运行时 + 13 个宿主函数 + SDK（508 行） |
| **SQLite 缓存** | `[✅ 已完成]` | theory/cache.rs 已完成（203 行，3 个测试） |
| **OpenTelemetry** | `[🚧 进行中]` | tracing 包已在使用（24 个调用点！） |
| **差分测试** | `[🔵 三期]` | 对比 Isabelle 输出（规划中；proptest 已在 Cargo.toml 中） |
| **Arena GC** | `[🔵 一期]` | 版本化 Arena（仅设计；kernel/arena.rs 为非版本化） |
| **Salsa 增量计算** | `[⏸️ 暂缓]` | 0 salsa 代码；当前 fleche/ 引擎无需它即可工作 |
| **CRDT 协作编辑** | `[⏸️ 暂缓]` | 0 代码；暂缓至当前路线图之后 |
| **Nix Flake / CI** | `[⏸️ 暂缓]` | 0 代码；未来打磨 |

---

## 技术栈现状

### 实际在 Cargo.toml 中的依赖（有代码存在）

| 包名 | 版本 | 用途 |
|------|------|------|
| `serde` / `serde_json` | 1 | 序列化（LSP 类型、理论缓存、WASM SDK） |
| `thiserror` | 2 | 错误类型（core/error.rs，所有模块） |
| `tracing` / `tracing-subscriber` | 0.1 / 0.3 | **24 个调用点**，分布在 server/、lsp/、wasm/、main.rs |
| `tokio` | 1 | **5 处使用**，在 session/ 层（spawn、mpsc、oneshot） |
| `rowan` | 0.15 | syntax/parser.rs — CST 构建器 + SyntaxTree |
| `wasmtime` | 29 | wasm/ — 运行时引擎、燃料计量、宿主函数 |
| `rusqlite` | 0.32 | theory/cache.rs — 基于 SQLite 的理论缓存 |
| `clap` | 4 | CLI 参数解析（main.rs、bin/isabelle-build.rs） |
| `bincode` | 1 | 二进制序列化（理论缓存 blob） |
| `sha2` | 0.10 | 文件哈希（理论缓存去重） |
| `proptest` | 1 | 基于属性的测试（8 个属性测试） |

### 规划中但不在 Cargo.toml 中的依赖（零代码存在）

| 包名 | 状态 | 备注 |
|------|------|------|
| `salsa` | `[⏸️ 暂缓]` | 增量计算框架；0 次使用 |
| `tower` | `[⏸️ 暂缓]` | LSP 中间件栈；0 次使用；当前 handler 工作良好 |
| `wasm-bindgen` | `[⏸️ 暂缓]` | Web 前端桥接；暂缓 |
| `rayon` | `[🔵 四期]` | 并行 term 操作；尚不需要 |
| `criterion` | `[🔵 四期]` | 基准测试；尚不需要 |
| `io_uring` / `tokio-uring` | `[⏸️ 暂缓]` | 异步文件 I/O；0 代码 |

### 关键观察

- **`async`/`tokio` 作用域受限**：仅 5 处使用，全部在 `session/` 中。内核 100% 同步。
- **`tracing` 已采用**：24 个调用点 — 无需迁移，只需扩展覆盖范围。
- **`salsa` 未实现**：fleche/ 引擎使用自己的增量检查模型（fork-point diff + 快照），而非 salsa。
- **`tower` 未实现**：LSP 分发使用 `lsp/router.rs` 中基于枚举的简单路由 + 处理函数。tower 的 ServiceBuilder 可以添加中间件，但对正确性并非必需。
- **无 `todo!()` 宏**：零潜在 panic。`drule.rs` 旧桩中有两个 `unreachable!()`。

---

## 当前实现：Isabelle Pure → Isabelle-rs 模块对照 `[✅ 已完成]`

| Isabelle Pure (ML) | 行数 | Isabelle-rs (Rust) | 状态 |
|---|---|---|---|
| `term.ML` | 1,143 | `core/term.rs` | ✅ de Bruijn 表示 |
| `type.ML` | 729 | `core/types.rs` | ✅ Sort、Typ |
| `sorts.ML` | 506 | `core/types.rs` (ClassAlgebra) | ✅ |
| `logic.ML` | 693 | `core/logic.rs` | ✅ Pure.imp/all/eq |
| `sign.ML` | 597 | `core/sign.rs` | ✅ 签名+类型检查 |
| `theory.ML` | — | `core/theory.rs` | ✅ Theory + ProofContext |
| `thm.ML` | 2,752 | `core/thm.rs` | ✅ 11 条推理规则 |
| `unify.ML` | 668 | `core/unify.rs` | ✅ 高阶统一 |
| `envir.ML` | 428 | `core/envir.rs` | ✅ |
| `term_subst.ML` | — | `core/term_subst.rs` | ✅ |
| `tactic.ML` | — | `core/tactic.rs` | ✅ |
| `Isar/token.ML` | 854 | `isar/token.rs` | ✅ 原生 \<...> |
| `Isar/parse.ML` | — | `isar/parse.rs` | ✅ 解析组合子 |
| `Isar/proof.ML` | 1,370 | `isar/proof.rs` | 🚧 桩代码 |
| `Isar/toplevel.ML` | 788 | `isar/toplevel.rs` | ✅ |
| `raw_simplifier.ML` | 1,576 | `core/simplifier.rs` | ✅ |
| `Syntax/*` | ~4,000 | `syntax/*` | 🚧 Rowan CST |
| `HOL/*` | ~100,000 | `hol/*` | ✅ 定理加载 100% |
| `PIDE/*` | ~10,000 | `server/*` (LSP) | 🚧 7 个 handler |

---

## 设计原则

```
1. 不妥协。本设计假设从零开始，不考虑 V1 兼容。
2. 以 Rust 2024 生态的最前沿为标准。
3. Isabelle 的语法、逻辑、LCF 内核不变。其他一切都可以重来。
4. 目标是：最快的交互式定理证明器，最好的编辑器体验。
```

## Layer 0: 定理加载层 `[✅ 已完成]`

> **状态：已完全实现。** 此层加载 Isabelle 实际 `.thy` 源文件，
> 解析 lemma/theorem 声明，将 Isabelle 语法转换为内部 term 表示，
> 并按属性对定理建索引用于证明自动化。

### parse_lemmas 流水线

```
Isabelle .thy 源文件
       │
       ▼
  parse_lemmas()          ← 扫描器：查找所有 "lemma name: \"stmt\"" / "theorem name: \"stmt\""
       │
       ├── 处理内联（单行）和多行（块）格式
       ├── 处理 locale 前缀：  (in order) name: "stmt"
       ├── 处理属性括号：  [simp, intro!]
       ├── 处理每行多个语句（合取形式）
       └── 处理结构化语句（assumes/shows）
       │
       ▼
  convert_syntax()        ← Isabelle 符号 → ASCII：  \<Longrightarrow> → ==>,  \<And> → !!, 等
       │
       ├── Cartouche 转换：  \<open>...\<close> → "..."
       ├── 连接词转换：  \<and>/\<or>/\<longrightarrow>/\<longleftrightarrow>
       ├── 量词转换：  \<forall>/\<exists>/\<exists>!
       ├── 运算符转换：   \<equiv>/\<lambda>/\<circ>/\<noteq>/\<not>
       └── 格式剥离：   \<^bold>, \<^sup>, \<^sub>, ::{}
       │
       ▼
  parse_term()            ← isar/term_parser.rs：词法分析 → 递归下降
       │
       ├── 处理：ALL x. P、EX x. P、EX1 x. P、%x. body
       ├── 处理：[| A; B |] ==> C（Isar 括号语法）
       ├── 处理：A & B、A | B、A --> B、A = B、A ~= B
       └── 终止保证：内联格式始终产生单 term 语句
       │
       ▼
  ThmKernel::assume()     ← 认证 term → assume → Arc<Thm>
       │
       ▼
  HolTheoremDb            ← 按属性建索引：[intro]、[elim]、[simp]、[iff]
       │
       ├── intros: Vec<Arc<Thm>>   — 引入规则
       ├── elims:  Vec<Arc<Thm>>   — 消去规则
       ├── simps:  Vec<Arc<Thm>>   — 化简规则
       └── all:    Vec<Arc<Thm>>   — 全部已加载定理
```

### 优雅降级模式

```
对源文件中的每个 lemma/theorem 声明：
  1. 尝试对隔离的代码块执行 parse_lemmas
  2. 成功 → 数据库中获得结构化的 Thm
  3. 失败 → 跳过并记录诊断（debug 级别日志）
  4. 永不崩溃 — 部分定理数据库总比没有好
  5. 每个文件的审计显示覆盖率（例如 2,436/2,436 = 100% 可解析）
```

### 定理数据库索引

```rust
// 懒加载的全局定理存储（加载一次，跨所有 session 共享）
static HOL_THEOREMS: LazyLock<HolTheoremDb> = LazyLock::new(|| {
    // 从 5 个 Isabelle 源文件加载：
    let hol_thy = include_str!("../../isabelle-source/src/HOL/HOL.thy");
    let ord_thy = include_str!("../../isabelle-source/src/HOL/Orderings.thy");
    let nat_thy = include_str!("../../isabelle-source/src/HOL/Nat.thy");
    let set_thy = include_str!("../../isabelle-source/src/HOL/Set.thy");
    let list_thy = include_str!("../../isabelle-source/src/HOL/List.thy");
    let mut lemmas = parse_lemmas(hol_thy);
    lemmas.extend(parse_lemmas(ord_thy));
    lemmas.extend(parse_lemmas(nat_thy));
    lemmas.extend(parse_lemmas(set_thy));
    lemmas.extend(parse_lemmas(list_thy));
    HolTheoremDb::from_lemmas(&lemmas)
});
```

### 成果：已加载 2,548 条定理

| 源文件 | 约含 Lemma 数 | 关键内容 |
|--------|-------------|----------|
| HOL.thy | ~800 | bool、implies、True、False、All、Ex、=、conj、disj、imp |
| Orderings.thy | ~600 | ord、order、<、<=、min、max、mono |
| Nat.thy | ~400 | 0、Suc、+、*、<、<=、nat_rec |
| Set.thy | ~500 | Collect、∈、∪、∩、-、UNIV、image、vimage |
| List.thy | ~250 | []、#、@、map、filter、fold、take、drop |
| **合计** | **2,548** | 全部可供 `auto`、`simp` 及所有证明方法使用 |

> 2,436/2,436 这个数字指的是加入 Set.thy 和 List.thy 之前的较早快照。
> 当前计数为 2,548。所有条目均通过验证（无空名称，
> 无平凡/部分解析）。

---

## 当前实现：增量检查流程 `[🚧 进行中]`

基于 fork-point diff 的快照模型（非 Rowan CST）：

```
文件编辑
    ↓
1. 解析为命令     按 Isabelle 语法拆分为 Commands
    ↓
2. 计算 fork       新旧命令列表 diff → 最后一个不变的位置
   point
    ↓
3. 保留旧快照      fork point 之前的 Snapshot 全部保留
    ↓
4. 重新执行        从 fork point+1 开始，逐条执行命令
   后续命令         产生新的 Snapshot
    ↓
5. 发布诊断        publishDiagnostics → LSP Client
```

计划迁移到 Rowan CST + Salsa 增量计算（三期）。

---

## 十项架构决策

### 1. 内存模型：全局 Interning + Arena `[🚧 进行中]`

> **当前：** `kernel/arena.rs` 已存在（309 行），包含 `GlobalArena`、`TermId`、`TypeId`、`Symbol`，
> 且 `intern()` 已激活。然而，`core/` 仍使用带 `Arc<str>` 的递归 `Term`/`Typ` 枚举。
> Arena 已构建但尚未接入内核热路径。

所有 term、type、符号共享一个全局 Arena。不使用 `Arc`、`Box`、递归 enum。

```
GlobalArena {
    symbols: SymbolTable,     // 全局唯一字符串池
    types: TypeArena,         // TypeId = u32
    terms: TermArena,         // TermId = u32
    theorems: ThmArena,       // ThmId = u32
}

// 关键属性：
// - TermId::eq() → u32 比较（1 条 CPU 指令）
// - TermId::clone() → 复制 u32（4 字节）
// - 内存：Vec<TermNode> 连续存储，缓存友好
// - 生存期：Arena 只追加，版本化 GC
```

**为什么不用 Arc/Box**：Arc 需要原子计数（慢），Box 导致分配碎片（慢），递归比较需遍历树（慢）。Arena 将所有三个问题一起解决。

### 设计理由：Arc<str> 字符串共享 `[✅ 已完成]`

理论中的常量名（如 `Pure.imp`）被引用数千次。`Arc<str>` 允许：
- 不可变共享：克隆仅增加引用计数
- 零拷贝比较：`Arc::ptr_eq` 检查指针相等（O(1)）
- 计划迁移到 Arena Symbol（u32），获得更快的比较速度

**GC 策略**：Arena 支持版本化。每个 FileWorker 有自己的 Arena 版本。文件关闭时，该版本的 Arena 整体回收（O(1)）。

---

### 2. 并发模型：四层分离 `[🚧 进行中]`

> **当前：** `session/` 实现了 Actor 模型（Session + FileWorker + Watchdog，609 行，
> 基于 tokio，使用 mpsc/oneshot）。LSP 层在 `server/` 和 `lsp/` 中都有可工作的 handler。
> **无 salsa**：Document 层使用 `fleche/` 的 fork-point diff + 快照模型代替。
> **无 tower**：LSP 层使用简单的基于枚举的路由。

```
┌──────────────────────────────────────────────────────────────┐
│  LSP 层：tokio async，永不阻塞                                 │
│  · stdin/stdout I/O：AsyncRead/AsyncWrite                    │
│  · 请求路由：Router → 按方法分发 Handler                       │
│  · 事件推送：broadcast channel                               │
│  · 中间件：⏸️ tower ServiceBuilder（暂缓 — 非必需）            │
├──────────────────────────────────────────────────────────────┤
│  Session 层：每个文件一个 Actor  [🚧 进行中 — 已实现]          │
│  · 每个 .thy 文件一个独立的 tokio task                         │
│  · 文件间零共享状态（除全局 Arena）                             │
│  · Watchdog：监控 worker，崩溃自动重启                         │
│  · 通信：mpsc（命令）+ oneshot（回复）                         │
├──────────────────────────────────────────────────────────────┤
│  Document 层：fleche fork-point diff  [✅ 已完成]             │
│  · ⏸️ salsa 增量计算（暂缓 — 0 次使用）                       │
│  · 当前：fork-point diff + 快照模型                           │
│  · 支持 cancel（CancellationToken 传递）                      │
├──────────────────────────────────────────────────────────────┤
│  Kernel 层：纯同步，无 I/O，无锁  [✅ 已完成]                  │
│  · spawn_blocking 隔离                                        │
│  · LCF 推理规则：无副作用，确定性                               │
│  · 所有数据通过 Arena ID 传递                                  │
└──────────────────────────────────────────────────────────────┘
```

---

### 3. 文档模型：Rowan CST `[🚧 进行中]`

> **当前：** `syntax/parser.rs`（400 行）使用 Rowan 实现了 `CstBuilder`、`SyntaxTree`、`IsabelleLanguage`。
> `syntax/ast.rs`（163 行）提供 AST 桥接。完整的增量重解析尚未接线。
> **CRDT 协作编辑：0 代码 — 暂缓至当前路线图之后。**

使用 `rowan`（无损具体语法树）替代字符串 + 行号。

```
SourceFile {
    green: GreenNode,       // 不可变 CST（rowan）
}

// 编辑时:
// 1. 增量 re-lex → 只重新词法分析变化的行
// 2. 增量 re-parse → 只重建变化部分的 CST
// 3. 增量 re-check → fleche fork-point diff 确定重新检查的范围
// 4. 诊断 → 只发布变化的诊断
```

**rowan 优势**：
- 保留空白和注释（lossless）
- 支持部分重解析
- 已用于 rust-analyzer，生产验证

---

### 4. LSP 层：LSP 路由 `[⏸️ 暂缓 — tower 未实现]`

> **当前：** 0 tower 代码。LSP 分发使用 `lsp/router.rs`（147 行），采用简单的
> 基于枚举的分发表 + 处理函数。`server/` 有 5 个文件（1,340 行），7 个可工作的 handler。
> **tower ServiceBuilder 可以添加中间件，但对正确性并非必需。**

```rust
// 主服务
let service = ServiceBuilder::new()
    .layer(TraceLayer::new())
    .layer(TimeoutLayer::new(Duration::from_secs(5)))
    .layer(ConcurrencyLimitLayer::new(50))
    .service(LspRouter::new(session));

// LspRouter 分发到各个 handler
#[derive(Clone)]
struct LspRouter {
    session: mpsc::Sender<SessionCommand>,
    events: broadcast::Receiver<SessionEvent>,
}

// 每个 handler 是一个独立的 Service
struct HoverService { session: mpsc::Sender<SessionCommand> }

impl Service<HoverParams> for HoverService {
    type Response = Option<Hover>;
    type Error = LspError;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response>>>>;

    fn call(&self, req: HoverParams) -> Self::Future {
        let session = self.session.clone();
        Box::pin(async move {
            let (tx, rx) = oneshot::channel();
            session.send(SessionCommand::Hover { params: req, reply: tx }).await?;
            rx.await?
        })
    }
}
```

**为什么 tower**：
- 每个 handler 独立测试
- 中间件可组合
- 已用于 Linkerd、AWS Lambda Rust，生产验证

---

### 5. 证明引擎：Tactic 的 Effect 系统 `[🔵 一期 — 未开始]`

> **当前：** `core/tactic.rs`（218 行）实现了 `Tactic` 枚举和化简器。
> Effect 系统（带 Trace/Timeout/Branch 的自由单子）已设计，但 JIT 编译器
> 为 `todo!()` — 这是愿景架构，非已实现代码。

Tactic 不是 `Box<dyn Fn>`，而是一等公民的 effect：

```rust
/// tactic 是一个带 effect 的计算，可以：
/// - 访问目标状态
/// - 产生子目标
/// - 被取消
/// - 被追踪
enum Tactic<A> {
    Pure(A),
    Bind { tac: Box<Tactic<A>>, f: Box<dyn Fn(A) -> Tactic<B>> },
    Goal(fn(&Goal) -> Vec<Goal>),
    Trace(String, Box<Tactic<A>>),
    Timeout(Duration, Box<Tactic<A>>),
    Branch(Vec<Tactic<A>>),
}

// Tactical 变为构造器：
fn then<A: 'static>(t1: Tactic<A>, t2: Tactic<A>) -> Tactic<A> {
    Tactic::Bind { tac: Box::new(t1), f: Box::new(move |_| t2) }
}

fn orelse<A: 'static>(t1: Tactic<A>, t2: Tactic<A>) -> Tactic<A> {
    Tactic::Branch(vec![t1, t2])
}
```

**为什么不用 `Box<dyn Fn>`**：
- 一等公民 AST → 可序列化、可分析、可优化
- 可以写 tactic 编译器（将 tactic 编译为优化的字节码）
- 可以生成 tactic 的证明项（proofterm）
- `Trace` → 自动记录策略执行日志
- `Timeout` → 内置超时支持
- `Branch` → 内置搜索分叉

---

### 6. 插件系统：WASM 沙箱 `[🚧 进行中]`

> **当前：** `wasm/` 模块（508 行，7 个测试）具有：`runtime.rs`（wasmtime 引擎 + 燃料计量）、
> `host.rs`（13 个宿主函数，桥接内核 API）、`sdk.rs`（插件编写 SDK）和
> `Plugin` trait。wasmtime 29 在 Cargo.toml 中。与 `Method::execute` 的集成尚未接线。

Tactic 和 method 可以实现为 WASM 插件：

```
// 用户写的 tactic 编译为 WASM
#[isabelle_tactic]
fn my_auto(goal: &Goal) -> Vec<Goal> {
    // ... 复杂的自定义证明搜索 ...
}

// 编译为 .wasm，加载时沙箱化
// - 内存隔离
// - 时间限制（gas/fuel metering）
// - 只能通过 host function 访问内核
```

**为什么 WASM**：
- 安全：用户 tactic 不能破坏内核
- 可分发：.wasm 文件可以共享
- 多语言：任何能编译到 WASM 的语言都能写 Isabelle tactic

---

### 7. 内核：零成本抽象 + LCF 验证 `[✅ 已完成]`

```
// LCF 推理规则在编译时验证部分属性

// 例：assume 的类型签名编码了"输入必须是命题"
fn assume(prop: TermId, arena: &Arena) -> ThmId
where
    // 编译时检查：prop 的类型是 prop
    arena.type_of(prop) == arena.type_prop()
{
    // 运行时检查：实际上是 assert
    debug_assert!(arena.type_of(prop) == arena.type_prop());
    // ... 构造 Thm
}

// 理想情况下：使用 session types 或 typestate 编码
// 证明状态的生命周期：
//   Idle → Stated → Proving → Done
// 编译器保证不会在 Idle 状态调用 apply()
```

---

### 8. 可观测性：OpenTelemetry `[🚧 进行中]`

> **当前：** `tracing` 已在使用，有 24 个调用点，分布在 `server/`、`lsp/`、`wasm/`、
> 和 `main.rs` 中。`tracing-subscriber` 在启动时初始化。尚无 OpenTelemetry 导出器，
> 但 instrumentation 基础已奠定。这**不是** `[🔵 三期]` — 已部分构建。

```
// 每个操作生成 trace span
#[tracing::instrument(skip(arena))]
fn unify(a: TermId, b: TermId, arena: &Arena) -> Result<Envir> {
    tracing::debug!(?a, ?b, "unifying");
    // ...
}

// 追踪整个证明过程：
// - 每个 tactic 步骤一个 span
// - 每个统一操作一个 event
// - 性能指标导出到 Prometheus
// - 错误率、延迟分布可视化
```

---

### 9. 持久化：SQLite 存储 `[✅ 已完成]`

> **当前：** `theory/cache.rs`（203 行，3 个测试）实现了完整的 `TheoryCache`，
> 包含 `lookup`、`store`、`list`、`hash_source`，后端为 rusqlite 0.32。CLI 构建工具
> (`bin/isabelle-build.rs`，98 行) 使用 clap 4。此模块已完全构建，非部分实现。

```
// 理论编译结果缓存到 SQLite
TheoryCache {
    db: SqlitePool,
}

// 查询："这个文件上次编译的 hash 是 X，有缓存吗？"
// 响应："有，这里是编译好的 ThmStore"

// 好处：
// - 重启后不需要重新编译所有依赖
// - 可以分布式共享（sqlite → s3/litestream）
// - 增量构建的基础
```

---

### 10. 全栈：同一个 Rust 代码库 `[🚧 进行中]`

> **当前：** `lib.rs` 已存在（27 行）。两个二进制文件：`main.rs`（LSP 服务器，262 行）和
> `bin/isabelle-build.rs`（CLI 构建工具，98 行）。列出的包如 `yew`/`dioxus` 不在
> Cargo.toml 中。全栈愿景部分实现 — 内核+服务器栈已真实存在，
> 但 Web 前端尚未开始。

```
isabelle-rs/
├── kernel/           # LCF 内核 + Arena（no_std，兼容 WASM）
├── session/          # Session actor + FileWorker
├── lsp/              # LSP server（tower + tokio）
├── web/              # WASM 前端（yew/dioxus）
├── cli/              # 命令行工具（clap）
├── wasm/             # WASM 插件 SDK
├── theory/           # Isabelle 标准库（.thy 文件）
└── docs/             # 文档

# 一个 crate，多个二进制：
# - isabelle-rs lsp     → LSP 服务器
# - isabelle-rs build   → 批量编译
# - isabelle-rs web     → Web 前端
# - isabelle-rs wasm    → WASM 运行时
```

---

## 文件树（当前 — 2025 年 7 月）

```
src/
├── main.rs                  # CLI 入口
├── kernel/                  # [🚧 进行中] V3 内核（逐步从 core/ 迁移）
│   ├── mod.rs               # pub use crate::core::*（桥接）
│   ├── arena.rs             # [🚧 进行中] GlobalArena、TermId、TypeId、Symbol（intern() 已激活）
│   ├── derived.rs           # [✅ 已完成] drule + more_thm + conjunction + bires
│   └── data.rs              # [✅ 已完成] facts + consts + net
├── core/                    # [✅ 已完成] 当前内核（将被 kernel/ 取代）
│   ├── types.rs、term.rs、logic.rs、sign.rs、theory.rs、thm.rs
│   ├── envir.rs、unify.rs、tactic.rs、simplifier.rs、variable.rs、pattern.rs
│   ├── drule.rs、more_thm.rs、conjunction.rs、bires.rs（合并 → kernel/derived.rs）
│   ├── facts.rs、consts.rs、net.rs（合并 → kernel/data.rs）
│   ├── proofterm.rs、axclass.rs、global_theory.rs、error.rs
│   └── mod.rs
├── session/                 # [🚧 进行中] Session actor（骨架）
│   ├── mod.rs
│   ├── session.rs           # Session：FileWorker 的编排器
│   ├── file_worker.rs       # FileWorker：每个文件的 actor，含 Arena
│   └── watchdog.rs          # Watchdog：健康监控
├── lsp/                     # [🚧 进行中] 基于 tower 的 LSP（Router 存在，handler 存在）
│   ├── mod.rs
│   ├── router.rs            # Router + 分发表 + handler 注册
│   └── handlers/            # lifecycle、hover、completion、definition、document、proof_goals
├── server/                  # [✅ 已完成] 当前 LSP 服务器（1,340 行，7 个 handler）
│   ├── mod.rs、lsp_types.rs、transport.rs、handler.rs、isabelle_ext.rs
├── document/                # [✅ 已完成] 文档模型（513 行，3 个测试）
│   ├── mod.rs、document.rs
├── fleche/                  # [✅ 已完成] 增量检查引擎（226 行，2 个测试）
│   ├── mod.rs、engine.rs
├── isar/                    # [✅ 已完成] Isar 结构化证明语言
│   ├── token.rs、parse.rs、term_parser.rs
│   ├── proof.rs、method.rs、proof_context.rs、toplevel.rs
├── hol/                     # [✅ 已完成] HOL 定理加载器（Layer 0）
│   ├── hol_loader.rs        # parse_lemmas、convert_syntax、HolTheoremDb、2,548 条定理
│   ├── hol_theorems.rs      # HolTheory：标准命题逻辑+量词+等式规则
│   ├── hol_rules.rs         # HOL 推理规则
│   └── hol_consts.rs        # HOL 常量声明
├── syntax/                  # [🚧 进行中] Rowan CST（CstBuilder、SyntaxTree、SyntaxKind 已实现）
│   ├── parser.rs            # CstBuilder、SyntaxTree、ParseError、IsabelleLanguage（Rowan）
│   ├── ast.rs               # Ast 枚举
│   └── syntax_phases.rs     # SyntaxPhases 流水线
├── tools/                   # [🚧 进行中] 证明自动化
│   ├── simp.rs              # HolSimplifier
│   ├── auto.rs              # Auto
│   └── blast.rs             # Blast
├── theory/                  # [🚧 进行中] Session/ROOT 管理 + SQLite 缓存
│   ├── mod.rs               # SessionInfo、TheoryInfo、SessionManager
│   └── cache.rs             # TheoryCache（SQLite）
└── wasm/                    # [🚧 进行中] WASM 插件沙箱（骨架）
    ├── mod.rs               # Plugin trait + PluginContext
    ├── runtime.rs           # WasmRuntime（wasmtime 预留）
    ├── host.rs              # 13 个宿主函数（内核 API 桥接）
    └── sdk.rs               # 插件编写 SDK

已删除：pide/（被 LSP 取代），proof/（被 isar/ 取代）
```

---

## 实施优先级（按收益/风险排序）[已更新]

```
一期: Arena + Symbol     ████████ [🚧 进行中]（intern() 激活，Arena 结构已定义，未完全迁移）
二期: 模块合并            ████████ [✅ 已完成]（derived.rs + data.rs）
三期: Session Actor      ████████ [🚧 进行中]（Session + FileWorker 骨架，未完全连线）
四期: Tactic AST         ████████ [🚧 进行中]（enum Tactic + apply()，JIT: todo!()）
五期: LSP tower          ████████ [🚧 进行中]（Router + handlers/，tower ServiceBuilder 未接线）
六期: Rowan CST          ████████ [🚧 进行中]（CstBuilder + SyntaxTree，基本解析，增量重解析未完成）
七期: WASM 插件           ████████ [🚧 进行中]（Plugin trait + 骨架，wasmtime 集成未完成）
八期: 持久化/Web          ████████ [🚧 进行中]（TheoryCache 结构，未完全连线）
```

## 后期增强 `[全部 ✅ 已完成]`

```
#4  forall_intr 实现      ✅ 完成（ThmKernel 第 10 条规则）
#A  forall_elim 实现      ✅ 完成（ThmKernel 第 11 条规则）
#1  Arena 激活（interning） ✅ 完成（intern() 函数 + thread_local）
#B  interning 扩散          ✅ 完成（logic/sign/theory/token，7 个文件）
#6  Proptest 属性测试       ✅ 完成（8 个属性测试）
#C  HOL 基础推理            ✅ 完成（True/False + conj/imp/all，12 条规则）
#3  App-App unify 修复      ✅ 完成（消除预存失败）
#D  Auto method 实现        ✅ 完成（assumption + elim + intro + simp）
#E  Toplevel 端到端         ✅ 完成（lemma → proof → apply → done）
#F  术语解析器扩展          ✅ 完成（HOL.conj/HOL.imp/HOL.disj/HOL.Not）
#G  Auto 合取交换律         ✅ 完成（(A & B) --> (B & A) by auto）
```

## 下一步路线 `[全部 ✅ 已完成]`

```
阶段 D：术语解析器完善（ALL/EX/True/False/嵌套）      ✅ 完成
阶段 E：Isar 结构化证明（fix/assume/have/show）       ✅ 完成
阶段 F：Auto 增强（disjE + disj_commute）             ✅ 完成
阶段 G：HOL 理论加载（内置定理数据库，14 条规则）       ✅ 完成 — 现已有 2,548 条定理！
阶段 H：生产就绪（LSP completion + demo + 错误改进）    ✅ 完成
```

## 路线 A：HOL 定理加载 `[全部 ✅ 已完成 — 已被 Layer 0 取代]`

```
A1：术语解析器补全（0.5 天）   ✅ 完成
    [| A; B |] ==> C / !!x. P(x) / A ~= B / 属性解析

A2：HOL 定理加载器（1 天）    ✅ 完成
    解析 2,548 条 lemma → 结构化 Term → assume 注册
    按 [simp]/[intro]/[elim]/[iff] 分类

A3：Auto/Simp 集成（1 天）    ✅ 完成
    auto 查询定理库，simp 使用 [simp] 规则
    端到端：加载 HOL.thy → 证明新定理
```

最终：171 个测试 | 0 错误 | 0 失败 🎉

---

## 不变的基石 `[全部 ✅ 已完成]`

```
✅ Isabelle .thy 语法        — 零变化
✅ Isar 语言                 — 零变化
✅ LCF 推理规则（11 条）      — 零变化（现为 11 条：assume、reflexive、symmetric、transitive、combination、abstraction、beta_conversion、implies_intr、implies_elim、forall_intr、forall_elim）
✅ Pure 元逻辑（!!/==>/==）   — 零变化
✅ Signature/Theory 体系     — 零变化
✅ LSP 协议                  — 标准协议，零自创
```

**变化的是：内存布局、并发模型、代码组织、可观测性、可扩展性。所有用户可见的语法、逻辑、内核不变。**

---

## 进一步进化空间

### 安全性 `[🔵 三期-四期]`

**11. 差分测试框架** `[🔵 三期]` — 随机 term/type/thm 生成，对比 Isabelle-rs 与 Isabelle 的输出。Proptest 已在 Cargo.toml 中。Isabelle 为 ground truth。

**12. 内核模糊测试** `[🔵 四期]` — cargo-fuzz：从随机字节构造 term，执行推理规则，检查不变式，崩溃即 bug。

**13. 显式栈替代递归** `[🔵 四期]` — unify/subst/compare 用显式栈，消除 stack overflow。

**14. cgroups 资源限制** `[⏸️ 暂缓 — 0 代码]` — FileWorker 限制 CPU/内存，超限 → SIGKILL → Watchdog 重启。

### 性能 `[🔵 三期-四期]`

**15. Struct-of-Arrays Arena** `[🔵 一期]` — kinds/names/children 分开存储，缓存命中率提升，内存减少 40%。

**16. rayon 并行替换** `[🔵 四期]` — subst(App(f,a)) → rayon::join(|| subst(f), || subst(a))。

**17. io_uring 文件 I/O** `[⏸️ 暂缓 — 0 代码]` — tokio-uring 不在 Cargo.toml 中。批量加载 .thy 快 2-5 倍（未来优化）。

### 实用性 `[⏸️ 暂缓]`

**18. 零配置安装** `[⏸️ 暂缓]` — curl | sh / brew install → VSCode 自动检测 → .thy 打开即用。

**19. Nix Flake** `[⏸️ 暂缓 — 0 代码]` — nix develop（开发环境）/ nix build（发布）。未来打磨。

**20. CI 全矩阵** `[⏸️ 暂缓 — 0 代码]` — os × rust × feature × test/fuzz/bench/miri/diff-test。

**21. 基准测试套件** `[🔵 四期]` — criterion 基准测试：unification p50/p99、增量吞吐量、Arena 追踪。尚未实现（criterion 不在 Cargo.toml 中）。

### 与竞品对比

| 特性 | Isabelle | V3 | Lean 4 | Coq |
|------|:---:|:---:|:---:|:---:|
| LCF 内核 | ✅ | ✅ | — | — |
| 结构化证明（Isar） | ✅ | ✅ | ✅ | — |
| LSP | — | ✅ | ✅ | ✅ |
| Arena 内存 | — | ✅ | ✅ | — |
| 按文件隔离 | — | ✅ | ✅ | — |
| WASM 插件 | — | ✅ | — | — |
| 差分测试 | — | ✅ | — | — |
| SQLite 缓存 | — | ✅ | — | — |

**空白格 = Isabelle-rs 独有。** 没有其他证明助手同时拥有 LCF 内核 + Arena 内存 + 按文件隔离 + WASM 插件。

---

## 详细设计：Arena GC `[🔵 一期 — 仅设计，尚未实现]`

```
/// 版本化 Arena。每个 FileWorker 获得一个版本号。
/// 文件关闭时，该版本的所有分配批量回收。

struct VersionedArena<T> {
    /// 所有分配：（version，data）
    slots: Vec<(u64, T)>,
    /// 空闲槽位
    free: Vec<u32>,
}

impl<T> VersionedArena<T> {
    /// 分配：在当前版本中分配
    fn alloc(&mut self, data: T, version: u64) -> u32 {
        if let Some(id) = self.free.pop() {
            self.slots[id as usize] = (version, data);
            id
        } else {
            let id = self.slots.len() as u32;
            self.slots.push((version, data));
            id
        }
    }

    /// GC：回收指定版本的所有分配
    fn gc(&mut self, version: u64) {
        for (id, (v, _)) in self.slots.iter_mut().enumerate() {
            if *v == version {
                self.free.push(id as u32);
                *v = u64::MAX; // 标记为已回收
            }
        }
    }

    fn get(&self, id: u32) -> &T {
        &self.slots[id as usize].1
    }
}

// 使用：
//   FileWorker 打开 → arena.set_version(worker_version)
//   FileWorker 关闭 → arena.gc(worker_version)
//   GC 是 O(n) 但仅在文件关闭时执行，不影响热路径
```

## 详细设计：Session 协议 `[🚧 进行中 — Session/FileWorker 存在，完整协议未接线]`

```
/// Session 接收的命令
enum SessionCommand {
    /// 打开文件
    OpenFile {
        url: Url,
        content: String,
        /// 回复：初始诊断
        reply: oneshot::Sender<Vec<Diagnostic>>,
    },

    /// 文件内容变更
    UpdateFile {
        url: Url,
        changes: Vec<TextChange>,
        reply: oneshot::Sender<Vec<Diagnostic>>,
    },

    /// 关闭文件
    CloseFile { url: Url },

    /// Hover 查询
    Hover {
        url: Url,
        position: Position,
        reply: oneshot::Sender<Option<Hover>>,
    },

    /// 补全
    Completion {
        url: Url,
        position: Position,
        reply: oneshot::Sender<CompletionList>,
    },

    /// 跳转定义
    Definition {
        url: Url,
        position: Position,
        reply: oneshot::Sender<Option<Location>>,
    },

    /// 证明目标
    ProofGoals {
        url: Url,
        position: Position,
        reply: oneshot::Sender<Option<ProofState>>,
    },

    /// 等待检查完成
    WaitForChecking {
        url: Url,
        position: Option<Position>,
        reply: oneshot::Sender<()>,
    },

    /// 优雅关闭
    Shutdown {
        reply: oneshot::Sender<()>,
    },
}

/// Session 推送的事件（broadcast）
enum SessionEvent {
    /// 诊断更新
    Diagnostics {
        url: Url,
        diagnostics: Vec<Diagnostic>,
    },

    /// 文件处理进度
    FileProgress {
        url: Url,
        processed: u32,
        total: u32,
    },

    /// 证明状态变化
    ProofStateChanged {
        url: Url,
        state: Option<ProofState>,
    },

    /// 理论编译完成
    TheoryCompiled {
        name: String,
        hash: String,
    },

    /// FileWorker 崩溃
    WorkerCrashed {
        url: Url,
        error: String,
    },
}
```

## 详细设计：理论导入解析 `[🔵 三期 — 设计，尚未实现]`

```
/// FileWorker 需要导入理论时的流程：
///
/// 1. FileWorker 解析到 "imports Foo"
/// 2. 检查本地缓存：theory_cache.get("Foo")
/// 3. 如果未缓存：
///    a. 向 Session 发送 ImportTheory 命令
///    b. Session 查找 Foo.thy 文件
///    c. Session spawn 新的 FileWorker 加载 Foo.thy
///    d. 等待 Foo 编译完成
///    e. 缓存 Foo 的 Theory + ThmStore
/// 4. FileWorker 获取 Foo 的 Arc<Theory> 作为自己的父理论

struct FileWorker {
    /// 已解析的理论（包含自己）
    loaded_theories: HashMap<String, Arc<Theory>>,
    /// 自己的理论
    theory: Arc<Theory>,
}

impl FileWorker {
    async fn resolve_import(&mut self, name: &str) -> Result<Arc<Theory>> {
        if let Some(t) = self.loaded_theories.get(name) {
            return Ok(Arc::clone(t));
        }
        // 请求 Session 加载
        let (tx, rx) = oneshot::channel();
        self.session_tx.send(SessionCommand::ImportTheory {
            name: name.to_string(),
            reply: tx,
        }).await?;
        let theory = rx.await??;
        self.loaded_theories.insert(name.to_string(), Arc::clone(&theory));
        Ok(theory)
    }
}
```

## 详细设计：Tactic 解释器 `[🚧 进行中 — enum Tactic 存在，JIT 编译器为 todo!()]`

```
/// Tactic 执行引擎
struct TacticEngine {
    arena: Arena,
}

impl TacticEngine {
    /// 执行一个 Tactic AST，产生 Goal 序列
    fn execute(&self, tac: &Tactic<()>, goal: &Goal) -> Vec<Vec<Goal>> {
        match tac {
            Tactic::Pure(()) => vec![vec![goal.clone()]],

            Tactic::Bind { tac: first, f } => {
                let intermediates = self.execute(first, goal);
                let mut results = Vec::new();
                for subgoals in intermediates {
                    let next = f(()); // 简化：A = ()
                    for sg in &subgoals {
                        results.extend(self.execute(&next, sg));
                    }
                }
                results
            }

            Tactic::Goal(action) => {
                action(goal).into_iter().map(|sg| vec![sg]).collect()
            }

            Tactic::Trace(label, inner) => {
                tracing::info!(%label, "tactic step");
                let start = std::time::Instant::now();
                let result = self.execute(inner, goal);
                tracing::debug!(%label, elapsed = ?start.elapsed(), "done");
                result
            }

            Tactic::Timeout(duration, inner) => {
                std::thread::scope(|s| {
                    let handle = s.spawn(|| self.execute(inner, goal));
                    std::thread::sleep(*duration);
                    // 无法在同步代码中取消 — 需要 CancellationToken
                    vec![] // timeout：返回空
                })
            }

            Tactic::Branch(alternatives) => {
                let mut results = Vec::new();
                for alt in alternatives {
                    results.extend(self.execute(alt, goal));
                }
                results
            }
        }
    }

    /// 编译 Tactic AST 为闭包（JIT）
    fn compile(&self, tac: &Tactic<()>) -> Box<dyn Fn(&Goal) -> Vec<Vec<Goal>>> {
        // 展开递归，内联 Trace/Timeout，生成优化的执行路径
        // ...
        todo!("Tactic JIT compiler")
    }
}
```

## 详细设计：生命周期 `[🔵 二期 — 仅设计]`

### 启动序列

```
1. main() 解析 CLI 参数
2. 初始化 tracing subscriber
3. 创建 GlobalArena（空）
4. 预加载 Pure theory（编译到 arena）
5. 创建 Session actor：
   a. spawn session task
   b. 初始化 theory_cache（包含 Pure）
6. 创建 LspServer：
   a. 创建 mpsc channel → Session
   b. 创建 broadcast receiver ← Session
   c. 构建 tower ServiceStack
7. spawn reader task（stdin → 解析 JSON-RPC）
8. spawn writer task（outgoing_tx → 写入 JSON-RPC）
9. 进入 main loop（处理 incoming messages）
```

### 优雅关闭

```
1. Editor 发送 shutdown 请求
2. LspServer：
   a. 停止接受新请求
   b. 等待所有 in-flight 请求完成（timeout：5 秒）
   c. 发送 SessionCommand::Shutdown
3. Session：
   a. 向所有 FileWorker 发送取消信号
   b. 等待所有 worker 退出（timeout：10 秒）
   c. 强制 kill 未退出的 worker
   d. 执行 Arena GC（回收所有版本）
   e. 发送 Shutdown 回复
4. LspServer 收到回复 → 发送 exit 通知 → 退出
```

### 崩溃恢复

```
FileWorker panic：
  1. tokio task 返回 JoinError
  2. Watchdog 检测到：
     a. 记录崩溃信息（tracing::error!）
     b. broadcast SessionEvent::WorkerCrashed
     c. 如果文件仍打开：以相同状态重新 spawn worker
     d. 否则：清理资源，GC Arena 版本
  3. LSP 层收到 WorkerCrashed → publishDiagnostics（错误信息）
  4. 用户看到："File worker crashed, restarting..."
```

## 详细设计：Rowan CST 集成 `[🚧 进行中 — CstBuilder 已构建，完整增量重解析尚未完成]`

```
/// Isabelle 词法分析 → Rowan GreenNode

struct IsabelleLexer {
    /// 将 Isabelle 源码转换为 rowan tokens
}

impl rowan::Lexer for IsabelleLexer {
    type Token = IsabelleToken;

    fn tokenize(&self, text: &str) -> Vec<(IsabelleToken, rowan::TextRange)> {
        let mut tokens = Vec::new();
        let lexer = Lexer::new(text);
        for tok in lexer.tokenize() {
            let kind = match tok.kind {
                TokenKind::Keyword(_) => IsabelleToken::Keyword,
                TokenKind::Ident => IsabelleToken::Ident,
                TokenKind::Symbol(_) => IsabelleToken::Symbol,
                // ...
            };
            let range = rowan::TextRange::new(
                rowan::TextSize::from(tok.offset as u32),
                rowan::TextSize::from((tok.offset + tok.source.len()) as u32),
            );
            tokens.push((kind, range));
        }
        tokens
    }
}

// Rowan 自动处理：
// - 增量 re-lex：只重新词法分析受编辑影响的区域
// - 增量 re-parse：只重建受影响的 CST 子树
// - 位置映射：GreenNode 偏移 ↔ 行号/列号
```

## 错误传播路径 `[🚧 进行中 — 错误类型存在，完整传播链未接线]`

```
┌─────────────────────────────────────────────────────────┐
│ 每一层定义自己的错误类型：                                  │
│                                                         │
│ KernelError   — 内核 bug（不可恢复）                       │
│   ├─ NotEquality、NotImplication、OccursCheck、...        │
│                                                         │
│ ProofError    — 证明失败（正常，可恢复）                    │
│   ├─ NoUnifier、SearchBound、TacticFailed、...            │
│                                                         │
│ SessionError  — Session 层错误                            │
│   ├─ FileNotFound、ImportCycle、WorkerCrashed、...         │
│                                                         │
│ LspError      — LSP 协议错误                              │
│   ├─ MethodNotFound、InvalidParams、InternalError          │
│                                                         │
│ 传播规则：                                                 │
│   KernelError → 不可恢复，向上传播为 InternalError          │
│   ProofError  → 转为 Diagnostic 发送给 Editor              │
│   SessionError → 转为 LspError 返回给 Editor               │
│   LspError    → JSON-RPC error response                  │
└─────────────────────────────────────────────────────────┘
```

## 配置系统 `[🔵 三期 — 仅设计]`

```
/// 全局配置，支持多层覆盖：
///   默认值 < 用户配置 < 项目配置 < LSP 配置

#[derive(Deserialize)]
struct Config {
    /// 内核配置
    kernel: KernelConfig,

    /// Session 配置
    session: SessionConfig,

    /// LSP 配置
    lsp: LspConfig,
}

#[derive(Deserialize)]
struct KernelConfig {
    /// 统一搜索深度限制
    #[serde(default = "default_search_bound")]
    search_bound: usize,

    /// 统一追踪开关
    #[serde(default)]
    unify_trace: bool,
}

#[derive(Deserialize)]
struct SessionConfig {
    /// 最大并发 FileWorker 数
    #[serde(default = "default_max_workers")]
    max_workers: usize,

    /// FileWorker 超时（秒）
    #[serde(default = "default_timeout")]
    worker_timeout: u64,
}

fn default_search_bound() -> usize { 60 }
fn default_max_workers() -> usize { 8 }
fn default_timeout() -> u64 { 300 }

// 加载顺序：
// 1. Config::default()
// 2. ~/.isabelle-rs/config.toml
// 3. ./.isabelle-rs.toml（项目根目录）
// 4. LSP initialize params（workspace/configuration）
```

---

## 增强并发模型（合并所有讨论）`[🔵 二期-三期 — 仅设计]`

> **现状核实：** `session/` 已使用 tokio mpsc + oneshot + spawn。`tracing` 已有
> 24 个调用点。以下设计为愿景 — `arc-swap`、`crossbeam`、`rayon`、
> `CancellationToken` 不在 Cargo.toml 或代码中。

### 完整并发栈

```
层              | 模式                 | 具体包                | 原因
LSP I/O         | async/await          | tokio + io_uring     | 非阻塞，批量系统调用
LSP routing     | Service middleware   | tower                | 超时/重试/限流
LSP → Session   | Actor model          | tokio::mpsc（有界）   | 背压
Session → LSP   | Pub/Sub              | tokio::broadcast     | 一对多推送
TheoryCache     | RCU（无锁读）         | arc-swap             | 读多写少，零阻塞
Arena alloc     | Lock-free queue      | crossbeam::SegQueue  | 多生产者，零锁
Term ops        | Work-stealing        | rayon                | CPU 密集型，自动均衡
Kernel          | Dedicated pool       | rayon（隔离）         | 大栈，不可中断
Cancel          | Token propagation    | CancellationToken    | 跨层传播
```

### 为什么不选这些

| 未选用 | 原因 |
|--------|------|
| RwLock | Writer 饥饿。TheoryCache 读 >> 写 |
| Mutex | 争用瓶颈。Arena 分配在热路径上 |
| STM | Rust 中无成熟的 STM 包 |
| 全用 Channel | 成本高：分配 + 复制。内部操作用函数调用 |
| Kernel 用 Actor | 内核是纯函数。Actor 适合有状态服务 |

---

## 详细设计：LCF 内核 API（Arena 化）`[🚧 进行中 — Kernel 结构体使用 Theory 而非 Arena，使用递归 Term 而非 TermId]`

```rust
struct Kernel<'a> {
    arena: &'a Arena,
    theory: &'a Theory,
}

impl<'a> Kernel<'a> {
    fn assume(&self, prop: TermId) -> ThmId {
        debug_assert!(self.arena.type_of(prop) == self.arena.prop_type());
        self.arena.alloc_thm(Thm {
            hyps: vec![prop], prop,
            maxidx: self.arena.maxidx_of(prop),
            derivation: Derivation::Axiom { name: "assume" },
            serial: self.arena.next_serial(),
        })
    }

    fn reflexive(&self, tm: TermId) -> ThmId {
        let eq = self.arena.mk_equals(self.arena.dummy_type(), tm, tm);
        self.arena.alloc_thm(Thm {
            hyps: vec![], prop: eq,
            maxidx: self.arena.maxidx_of(tm),
            derivation: Derivation::Axiom { name: "reflexive" },
            serial: self.arena.next_serial(),
        })
    }

    fn symmetric(&self, thm: ThmId) -> ThmId {
        let t = self.arena.get_thm(thm);
        let (a, b) = self.arena.dest_equals(t.prop).unwrap();
        let new_prop = self.arena.mk_equals(self.arena.dummy_type(), b, a);
        self.arena.alloc_thm(Thm {
            hyps: t.hyps, prop: new_prop, maxidx: t.maxidx,
            derivation: Derivation::Rule { name: "symmetric", premises: vec![thm] },
            serial: self.arena.next_serial(),
        })
    }

    // transitive、combination、abstraction、beta_conversion、
    // implies_intr、implies_elim 遵循相同模式
}
```

## 详细设计：类型检查流（Arena）`[🚧 进行中 — type_of 存在于递归 Term，而非 Arena/TermId]`

```rust
impl Arena {
    fn type_of(&self, term: TermId) -> TypeId {
        match self.get_term(term) {
            TermNode::Const { typ, .. } => *typ,
            TermNode::Free { typ, .. } => *typ,
            TermNode::Var { typ, .. } => *typ,
            TermNode::Bound(_) => panic!("type_of: Bound without context"),
            TermNode::Abs { typ: binder_typ, body } => {
                let body_typ = self.type_of(*body);
                self.mk_fun_type(*binder_typ, body_typ)
            }
            TermNode::App { func, arg } => {
                let func_typ = self.type_of(*func);
                let (domain, codomain) = self.dest_fun_type(func_typ)
                    .expect("type_of: applying non-function");
                debug_assert!(self.type_of(*arg) == domain);
                codomain
            }
        }
    }
}
```

## 设计理由：de Bruijn 索引 `[✅ 已完成]`

Isabelle 内部使用 de Bruijn 索引表示绑定变量。Isabelle-rs 继承此设计：

- **α-等价性免费**：两个 de Bruijn 项结构相等 ⇔ α-等价
- **替换简单**：不需要重命名避免捕获
- **缺点**：可读性差 → 通过 pretty printer 恢复名字

## 详细设计：跨 Arena 序列化/IPC `[🔵 三期 — 设计，尚未实现]`

```rust
// 问题：不同 FileWorker 有不同 Arena，TermId 不通用
// 解决：序列化时转为名称路径（interning 保证同名同义）

enum SerialTerm {  // 可跨 Arena 传输
    Const { name: String, typ: SerialType },
    Free { name: String, typ: SerialType },
    Var { name: String, index: u32, typ: SerialType },
    Bound(u32),
    Abs { name: String, typ: SerialType, body: Box<SerialTerm> },
    App { func: Box<SerialTerm>, arg: Box<SerialTerm> },
}

impl Arena {
    fn export_term(&self, id: TermId) -> SerialTerm { /* Symbol 查找 */ }
    fn import_term(&mut self, st: &SerialTerm) -> TermId { /* Symbol intern */ }
}
```

## 详细设计：测试策略 `[🚧 进行中 — 单元测试和属性测试已启用；模糊测试/差分测试/基准测试尚未]`

| 层 | 测试类型 | 工具 | 目标 |
|---|----------|------|------|
| Kernel | 单元 | #[test] | 每条推理规则至少 3 个用例 |
| Kernel | 属性 | proptest | 随机 term → 不变式成立 |
| Kernel | 模糊测试 | cargo-fuzz | 随机字节 → 不崩溃 |
| Kernel | 差分测试 | 自定义 harness | 对比 Isabelle 输出 |
| Session | 集成 | #[tokio::test] | 多文件并发 |
| LSP | 端到端 | lsp-test-harness | 模拟编辑器 |
| Isar | 语法 | 已知 .thy 文件 | 解析 → 正确 AST |
| 性能 | 基准测试 | criterion | 回归检测 |
| 内存 | 泄漏 | dhat/valgrind | Arena GC 正确 |
| Unsafe | UB | cargo miri | Unsafe 代码审计 |

## 详细设计：V1 → V3 迁移路径 `[进行中 — 第 1-2 阶段完成，3-8 阶段部分完成]`

```
第 1 阶段：Arena + Symbol（无外部 API 变化）
  删除：无
  重写：types.rs、term.rs（内部 Arena）
  新增：kernel/arena.rs、kernel/symbol.rs
  涉及：~25 个使用 Term/Typ 的文件
  测试：所有 117 个 V1 测试应通过

第 2 阶段：模块合并
  删除：drule、more_thm、conjunction、bires、consts、facts、net
  新增：kernel/derived.rs、kernel/data.rs

第 3 阶段：Session Actor
  删除：fleche/engine.rs、document/document.rs
  新增：session/（4 个文件）
  涉及：server/handler.rs → 基于 channel

第 4 阶段：Tactic AST
  重写：kernel/tactic.rs（Box<dyn Fn> → enum Tactic）

第 5 阶段：LSP tower
  删除：server/handler.rs、server/transport.rs
  新增：lsp/（router + handlers）

第 6 阶段：Rowan CST
  涉及：isar/token.rs（Lexer → rowan::Lexer）

第 7-8 阶段：WASM、持久化、Web（未来）

---

## 详细设计：WASM 插件系统（第 7 阶段）`[🚧 进行中 — 骨架存在，wasmtime 未集成]`

### 架构

```
用户代码（Rust/任何→WASM）
        │
        ▼ 编译
   plugin.wasm
        │
        ▼ 加载
┌──────────────────────┐
│  WasmRuntime         │  ← wasmtime 实例
│  ├── memory（64KB）   │     隔离内存空间
│  ├── fuel（1000）     │     燃料计量 → 超时终止
│  └── host functions  │     白名单：只能调用内核 API
│       ├── kernel_apply     │
│       ├── kernel_unify     │
│       └── kernel_lookup    │
└──────────────────────┘
        │
        ▼
   内核 LCF API（只读白名单）
```

### 模块结构

```
wasm/
├── mod.rs         # WasmRuntime、Plugin trait
├── runtime.rs     # wasmtime 实例管理 + fuel metering
├── host.rs        # host functions（13 个内核 API 桥接）
└── sdk.rs         # 用户编写插件用的 SDK 类型
```

### 核心类型

```rust
// wasm/mod.rs
pub trait Plugin: Send + Sync {
    fn name(&self) -> &str;
    fn apply(&self, goal: &Goal, ctx: &PluginContext) -> Vec<Vec<Goal>>;
}

pub struct WasmRuntime {
    engine: wasmtime::Engine,
    store: wasmtime::Store<RuntimeState>,
    linker: wasmtime::Linker<RuntimeState>,
    fuel: u64,
}

// wasm/host.rs — 内核暴露给 WASM 的白名单：
// - kernel_assume(cterm_ptr, cterm_len) → thm_id
// - kernel_reflexive(cterm_ptr, cterm_len) → thm_id
// - kernel_implies_intr(thm_id, cterm_ptr, cterm_len) → thm_id
// - kernel_implies_elim(thm_id, thm_id) → thm_id
// - kernel_unify(t1_ptr, t1_len, t2_ptr, t2_len) → envir_id
// - kernel_lookup(name_ptr, name_len) → thm_list_id
```

### 集成点

```rust
// isar/method.rs 新增 variant：
pub enum Method {
    // ... 现有 15 个 variant ...
    WasmPlugin { name: String, bytes: Vec<u8> },
}
```

### 实施步骤

| 步骤 | 内容 | 文件 |
|------|------|------|
| 7.1 | 添加 wasmtime 依赖 | Cargo.toml |
| 7.2 | 创建 wasm/ 模块骨架 | wasm/mod.rs、runtime.rs、host.rs、sdk.rs |
| 7.3 | 定义 Plugin trait + 13 个宿主函数 | wasm/mod.rs、wasm/host.rs |
| 7.4 | 实现 WasmRuntime（load + call_tactic） | wasm/runtime.rs |
| 7.5 | 示例插件 + 集成测试 | wasm/sdk.rs、tests/wasm_plugin.rs |
| 7.6 | 集成到 Method::execute | isar/method.rs |

### 安全模型

- **内存隔离**：WASM 线性内存 64KB，不能访问宿主内存
- **燃料计量**：每条 WASM 指令消耗 1 fuel，上限 1000 → ~0.1ms 超时
- **白名单**：只能调用 13 个注册的 host functions
- **无 I/O**：不能读写文件、网络、环境变量

### 依赖

- `wasmtime = "29"` — WASM 运行时

---

## 详细设计：持久化 + CLI + Web（第 8 阶段）`[🚧 进行中 — TheoryCache 骨架，CLI 桩，Web 未开始]`

### 架构

```
isabelle-rs/
├── cli/
│   ├── mod.rs
│   ├── build.rs       # `isabelle-rs build Foo.thy`
│   └── cache.rs       # TheoryCache（SQLite）
├── web/
│   ├── index.html     # 前端页面
│   ├── lib.rs         # wasm-bindgen 桥接
│   └── app.js         # 前端逻辑
└── Cargo.toml
    [[bin]]
    name = "isabelle-rs"      # LSP 服务器（现有）
    [[bin]]
    name = "isabelle-build"   # CLI build（新增）
    [[bin]]
    name = "isabelle-web"     # Web 服务器（新增）
```

### 核心类型

```rust
// cli/cache.rs
pub struct TheoryCache {
    db: rusqlite::Connection,
}

impl TheoryCache {
    /// 查询缓存：path + source_hash → Option<CachedTheory>
    pub fn lookup(&self, path: &str, hash: &str) -> Option<CachedTheory>;

    /// 存储编译结果
    pub fn store(&self, path: &str, hash: &str, theory: &Theory);

    /// 列出所有缓存条目
    pub fn list(&self) -> Vec<CacheEntry>;
}

pub struct CachedTheory {
    pub path: String,
    pub source_hash: String,
    pub compiled_at: chrono::DateTime<chrono::Utc>,
    pub theorems: Vec<String>,
    pub blob: Vec<u8>,  // bincode 序列化的 Theory
}

// cli/build.rs
pub fn build_theory(path: &Path, cache: &TheoryCache) -> Result<BuildResult> {
    // 1. 读取 .thy 文件
    // 2. 计算 SHA256 hash
    // 3. 查缓存 → 命中则跳过
    // 4. 缓存未命中：解析 → 类型检查 → 编译 → 存缓存
}
```

### SQLite 表结构

```sql
CREATE TABLE theory_cache (
    path        TEXT NOT NULL,
    source_hash TEXT NOT NULL,
    compiled_at TEXT NOT NULL,
    theorems    TEXT NOT NULL,  -- JSON 数组
    blob        BLOB NOT NULL,
    PRIMARY KEY (path, source_hash)
);

CREATE INDEX idx_cache_path ON theory_cache(path);
```

### Web 前端（wasm-bindgen bridge）

```rust
// web/lib.rs
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct IsabelleChecker {
    kernel: KernelHandle,
}

#[wasm_bindgen]
impl IsabelleChecker {
    pub fn new() -> Self;
    pub fn check(&self, source: &str) -> String;  // JSON diagnostics
    pub fn hover(&self, source: &str, line: u32, col: u32) -> String;
}
```

### 实施步骤

| 步骤 | 内容 | 文件 |
|------|------|------|
| 8.1 | 添加 rusqlite + clap 依赖 | Cargo.toml |
| 8.2 | 创建 cli/ 模块 + TheoryCache | cli/cache.rs |
| 8.3 | 实现 CLI build 命令 | cli/build.rs |
| 8.4 | 多二进制入口配置 | Cargo.toml、cli/main.rs |
| 8.5 | Web：wasm-bindgen 桥接 | web/lib.rs |
| 8.6 | Web：前端页面 + 测试 | web/index.html、web/app.js |

### 依赖

- `rusqlite = { version = "0.32", features = ["bundled"] }` — SQLite
- `clap = { version = "4", features = ["derive"] }` — CLI
- `wasm-bindgen = "0.2"` — Web 桥接
- `bincode = "1"` — 序列化
- `sha2 = "0.10"` — 文件哈希
