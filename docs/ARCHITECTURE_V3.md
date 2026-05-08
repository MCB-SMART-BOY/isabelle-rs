# Architecture V3 — Zero Compromise

## 设计原则

```
1. 不妥协。本设计假设从零开始，不考虑 V1 兼容。
2. 以 Rust 2024 生态的最前沿为标准。
3. Isabelle 的语法、逻辑、LCF 内核不变。其他一切都可以重来。
4. 目标是：最快的交互式定理证明器，最好的编辑器体验。
```

## 十项架构决策

### 1. 内存模型：全局 Interning + Arena

所有 term、type、符号共享一个全局 Arena。不使用 `Arc`、`Box`、递归 enum。

```
GlobalArena {
    symbols: SymbolTable,     // 全局唯一字符串池
    types: TypeArena,         // TypeId = u32
    terms: TermArena,         // TermId = u32
    theorems: ThmArena,       // ThmId = u32
}

// 关键属性：
// - TermId::eq() → u32 比较 (1 CPU 指令)
// - TermId::clone() → 复制 u32 (4 bytes)
// - 内存: Vec<TermNode> 连续存储, 缓存友好
// - 生存期: Arena append-only, 版本化 GC
```

**为什么不用 Arc/Box**：Arc 需要原子计数（慢），Box 导致分配碎片（慢），递归比较需遍历树（慢）。Arena 将所有三个问题一起解决。

**GC 策略**：Arena 支持版本化。每个 FileWorker 有自己的 Arena 版本。文件关闭时，该版本的 Arena 整体回收（O(1)）。

---

### 2. 并发模型：四层分离

```
┌──────────────────────────────────────────────────────────────┐
│  LSP Layer:  tokio async, 永不阻塞                           │
│  · stdin/stdout I/O: AsyncRead/AsyncWrite                    │
│  · 请求路由: Router → per-method Handler                     │
│  · 事件推送: broadcast channel                               │
│  · 中间件: tower ServiceBuilder (tracing, timeout, rate)     │
├──────────────────────────────────────────────────────────────┤
│  Session Layer: Actor per file                               │
│  · 每个 .thy 文件一个独立 tokio task                          │
│  · 文件间零共享状态 (除全局 Arena)                             │
│  · Watchdog: 监控 worker, 崩溃自动重启                        │
│  · 通信: mpsc (命令) + oneshot (回复)                         │
├──────────────────────────────────────────────────────────────┤
│  Document Layer: salsa 增量计算                               │
│  · #[salsa::tracked] 函数自动形成依赖图                        │
│  · 输入变化 → 自动失效 → 只重算变化部分                         │
│  · 支持 cancel (CancellationToken 传递到 salsa 查询)          │
├──────────────────────────────────────────────────────────────┤
│  Kernel Layer: 纯同步, 无 IO, 无锁                            │
│  · spawn_blocking 隔离                                        │
│  · LCF 推理规则: 无副作用，确定性                               │
│  · 所有数据通过 Arena ID 传递                                  │
└──────────────────────────────────────────────────────────────┘
```

---

### 3. 文档模型：CRDT-ready + Rowan CST

使用 `rowan`（lossless concrete syntax tree）替代字符串 + 行号。

```
SourceFile {
    green: GreenNode,       // 不可变 CST (rowan)
}

// 编辑时:
// 1. 增量 re-lex → 只重词法分析变化的行
// 2. 增量 re-parse → 只重建变化部分的 CST
// 3. 增量 re-check → salsa 自动确定重算范围
// 4. 诊断 → 只发布变化的诊断

// CRDT 准备:
// - GreenNode 是位置无关的 (通过相对偏移索引子节点)
// - 支持 OT (Operational Transform) 或 CRDT 合并
// - 为未来的协作编辑做准备
```

**rowan 优势**：
- 保留空白和注释（lossless）
- 支持部分重解析
- 已用于 rust-analyzer，生产验证

---

### 4. LSP 层：tower Service 栈

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
- 已用于 Linkerd、AWS Lambda Rust、生产验证

---

### 5. 证明引擎：Effect System for Tactics

Tactic 不是 `Box<dyn Fn>`，而是一等公民的 effect：

```rust
/// A tactic is an effectful computation that can:
/// - Access the goal state
/// - Produce subgoals
/// - Be cancelled
/// - Be traced
enum Tactic<A> {
    Pure(A),
    Bind { tac: Box<Tactic<A>>, f: Box<dyn Fn(A) -> Tactic<B>> },
    Goal(fn(&Goal) -> Vec<Goal>),
    Trace(String, Box<Tactic<A>>),
    Timeout(Duration, Box<Tactic<A>>),
    Branch(Vec<Tactic<A>>),
}

// Tacticals become constructors:
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

### 6. 插件系统：WASM 沙箱

Tactic 和 method 可以实现为 WASM 插件：

```
// 用户写的 tactic 编译为 WASM
#[isabelle_tactic]
fn my_auto(goal: &Goal) -> Vec<Goal> {
    // ... 复杂的自定义证明搜索 ...
}

// 编译为 .wasm，加载时沙箱化
// - 内存隔离
// - 时间限制 (gas/fuel metering)
// - 只能通过 host function 访问内核
```

**为什么 WASM**：
- 安全：用户 tactic 不能破坏内核
- 可分发：.wasm 文件可以共享
- 多语言：任何能编译到 WASM 的语言都能写 Isabelle tactic

---

### 7. 内核：零成本抽象 + const 验证

```
// LCF 推理规则在编译时验证部分属性

// 例：assume 的类型签名编码了"输入必须是命题"
fn assume(prop: TermId, arena: &Arena) -> ThmId
where
    // 编译时检查: prop 的类型是 prop
    arena.type_of(prop) == arena.type_prop()
{
    // 运行时检查: 实际是 assert
    debug_assert!(arena.type_of(prop) == arena.type_prop());
    // ... 构造 Thm
}

// 理想情况下: 使用 session types 或 typestate 编码
// 证明状态的生命周期:
//   Idle → Stated → Proving → Done
// 编译器保证不会在 Idle 状态调用 apply()
```

---

### 8. 可观测性：OpenTelemetry

```
// 每个操作生成 trace span
#[tracing::instrument(skip(arena))]
fn unify(a: TermId, b: TermId, arena: &Arena) -> Result<Envir> {
    tracing::debug!(?a, ?b, "unifying");
    // ...
}

// 追踪整个证明过程:
// - 每个 tactic 步骤一个 span
// - 每个统一操作一个 event
// - 性能指标导出到 Prometheus
// - 错误率、延迟分布可视化
```

---

### 9. 持久化：SQLite 存储

```
// 理论编译结果缓存到 SQLite
TheoryCache {
    db: SqlitePool,
}

// 查询: "这个文件上次编译的 hash 是 X, 有缓存吗?"
// 响应: "有, 这里是编译好的 ThmStore"

// 好处:
// - 重启后不需要重新编译所有依赖
// - 可以分布式共享 (sqlite → s3/litestream)
// - 增量构建的基础
```

---

### 10. 全栈：同一个 Rust 代码库

```
isabelle-rs/
├── kernel/           # LCF 内核 + Arena (no_std, WASM 兼容)
├── session/          # Session actor + FileWorker
├── lsp/              # LSP server (tower + tokio)
├── web/              # WASM 前端 (yew/dioxus)
├── cli/              # 命令行工具 (clap)
├── wasm/             # WASM 插件 SDK
├── theory/           # Isabelle 标准库 (.thy 文件)
└── docs/             # 文档

# 一个 crate, 多个二进制:
# - isabelle-rs lsp     → LSP 服务器
# - isabelle-rs build   → 批量编译
# - isabelle-rs web     → Web 前端
# - isabelle-rs wasm    → WASM 运行时
```

---

## 文件树（理想）

```
src/
├── main.rs                  # CLI 入口
├── kernel/
│   ├── arena.rs             # GlobalArena, TermId, TypeId, ThmId
│   ├── symbol.rs            # Symbol = u32, SymbolTable
│   ├── types.rs             # Type, Sort, ClassAlgebra (用 Arena)
│   ├── term.rs              # Term (用 Arena)
│   ├── logic.rs             # Pure 元逻辑
│   ├── sign.rs              # Signature
│   ├── theory.rs            # Theory, ProofContext
│   ├── thm.rs               # ThmKernel, Thm, Derivation
│   ├── envir.rs             # Environment
│   ├── unify.rs             # 高阶统一
│   ├── tactic.rs            # 策略 AST (effect system)
│   ├── simplifier.rs        # 重写引擎
│   ├── derived.rs           # 派生规则
│   ├── data.rs              # Facts, Consts, Net
│   ├── proofterm.rs         # 证明项
│   ├── error.rs             # 结构化错误
│   └── gc.rs                # Arena 版本化 GC
├── session/
│   ├── mod.rs               # Session actor
│   ├── file_worker.rs       # FileWorker
│   ├── watchdog.rs          # Watchdog
│   └── document.rs          # 增量文档模型
├── lsp/
│   ├── mod.rs               # LspServer (tower)
│   ├── router.rs            # Router
│   ├── handlers/
│   │   ├── initialize.rs
│   │   ├── hover.rs
│   │   ├── completion.rs
│   │   ├── definition.rs
│   │   ├── did_open.rs
│   │   ├── did_change.rs
│   │   └── proof_goals.rs
│   ├── transport.rs         # stdio I/O
│   └── protocol.rs          # LSP types
├── isar/
│   ├── token.rs             # 词法分析
│   ├── parse.rs             # 解析组合子
│   ├── term_parser.rs       # term/type parser
│   ├── proof.rs             # 证明状态机
│   ├── method.rs            # method 系统
│   ├── context.rs           # Isar 证明上下文
│   └── toplevel.rs          # Toplevel 命令循环
├── hol/
│   └── loader.rs            # 从 Isabelle 源文件加载 HOL
├── web/                     # (未来) WASM 前端
├── wasm_sdk/                # (未来) WASM 插件 SDK
└── cli/
    └── build.rs             # 批量编译
```

---

## 实施优先级（按收益/风险排序）

```
Phase 1: Arena + Symbol    ████████ 高收益, 低风险, 2-3 天
Phase 2: 模块合并          ████     中收益, 低风险, 1 天
Phase 3: Session Actor     ██████   高收益, 中风险, 3-5 天
Phase 4: Tactic AST        ██████   高收益, 中风险, 2-3 天
Phase 5: LSP tower         ████     中收益, 低风险, 1-2 天
Phase 6: Rowan CST         ███      中收益, 中风险, 2-3 天
Phase 7: WASM 插件         ██       低收益, 高风险, 5-10 天
Phase 8: 持久化/Web        ██       长远收益, 高风险, 10+ 天
```

## 不变的基石

```
✅ Isabelle .thy 语法       — 零变化
✅ Isar 语言                — 零变化
✅ LCF 推理规则 (9 条)      — 零变化
✅ Pure 元逻辑 (!!/==>/==)  — 零变化
✅ Signature/Theory 体系    — 零变化
✅ LSP 协议                 — 标准协议, 零自创
```

**变化的是：内存布局、并发模型、代码组织、可观测性、可扩展性。所有用户可见的语法、逻辑、内核不变。**


---

## 进一步进化空间

### 安全性

**11. 差分测试框架** — 随机生成 term/type/thm, Isabelle-rs 和 Isabelle 同时执行, 比较输出。Isabelle 是唯一的 ground truth。

**12. 内核模糊测试** — cargo-fuzz: 从随机字节构造 term, 执行推理规则, 检查不变式, 崩溃即 bug。

**13. 显式栈替代递归** — unify/subst/compare 用显式栈, 消除 stack overflow。

**14. cgroups 资源限制** — FileWorker 限制 CPU/内存, 超限 → SIGKILL → Watchdog 重启。

### 性能

**15. Struct-of-Arrays Arena** — kinds/names/children 分开存储, 缓存命中率提升, 内存减少 40%。

**16. rayon 并行替换** — subst(App(f,a)) → rayon::join(|| subst(f), || subst(a))。

**17. io_uring 文件 I/O** — tokio-uring, 批量加载 .thy 快 2-5x。

### 实用性

**18. 零配置安装** — curl | sh / brew install → VSCode 自动检测 → .thy 打开即用。

**19. Nix Flake** — nix develop (开发环境) / nix build (发布)。

**20. CI 全矩阵** — os × rust × feature × test/fuzz/bench/miri/diff-test。

**21. 基准测试套件** — criterion: unification p50/p99, 增量吞吐量, Arena 轨迹。

### 与竞品对比

| 特性 | Isabelle | V3 | Lean 4 | Coq |
|------|:---:|:---:|:---:|:---:|
| LCF 内核 | ✅ | ✅ | — | — |
| 结构化证明 (Isar) | ✅ | ✅ | ✅ | — |
| LSP | — | ✅ | ✅ | ✅ |
| Arena 内存 | — | ✅ | ✅ | — |
| Per-file 隔离 | — | ✅ | ✅ | — |
| WASM 插件 | — | ✅ | — | — |
| 差分测试 | — | ✅ | — | — |
| SQLite 缓存 | — | ✅ | — | — |

**空白格 = Isabelle-rs 独有。** 没有其他证明助手同时拥有 LCF 内核 + Arena 内存 + Per-file 隔离 + WASM 插件。


---

## 详细设计：Arena GC

```
/// 版本化 Arena。每个 FileWorker 获得一个版本号。
/// 文件关闭时，该版本的所有分配批量回收。

struct VersionedArena<T> {
    /// 所有分配： (version, data)
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

// 使用:
//   FileWorker 打开 → arena.set_version(worker_version)
//   FileWorker 关闭 → arena.gc(worker_version)
//   GC 是 O(n) 但只在文件关闭时执行, 不影响热路径
```

## 详细设计：Session 协议

```
/// Session 接收的命令
enum SessionCommand {
    /// 打开文件
    OpenFile {
        url: Url,
        content: String,
        /// 回复: 初始诊断
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

/// Session 推送的事件 (broadcast)
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

## 详细设计：理论导入解析

```
/// FileWorker 需要导入理论时的流程:
///
/// 1. FileWorker 解析到 "imports Foo"
/// 2. 检查本地缓存: theory_cache.get("Foo")
/// 3. 如果未缓存:
///    a. 向 Session 发送 ImportTheory 命令
///    b. Session 查找 Foo.thy 文件
///    c. Session spawn 新的 FileWorker 加载 Foo.thy
///    d. 等待 Foo 编译完成
///    e. 缓存 Foo 的 Theory + ThmStore
/// 4. FileWorker 获取 Foo 的 Arc<Theory> 作为自己的父理论

struct FileWorker {
    /// 已解析的理论 (包含自己)
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

## 详细设计：Tactic 解释器

```
/// Tactic 执行引擎
struct TacticEngine {
    arena: Arena,
}

impl TacticEngine {
    /// 执行一个 Tactic AST, 产生 Goal 序列
    fn execute(&self, tac: &Tactic<()>, goal: &Goal) -> Vec<Vec<Goal>> {
        match tac {
            Tactic::Pure(()) => vec![vec![goal.clone()]],

            Tactic::Bind { tac: first, f } => {
                let intermediates = self.execute(first, goal);
                let mut results = Vec::new();
                for subgoals in intermediates {
                    let next = f(()); // 简化: A = ()
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
                    vec![] // timeout: 返回空
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

    /// 编译 Tactic AST 为闭包 (JIT)
    fn compile(&self, tac: &Tactic<()>) -> Box<dyn Fn(&Goal) -> Vec<Vec<Goal>>> {
        // 展开递归, 内联 Trace/Timeout, 生成优化的执行路径
        // ...
        todo!("Tactic JIT compiler")
    }
}
```

## 详细设计：生命周期

### 启动序列

```
1. main() 解析 CLI 参数
2. 初始化 tracing subscriber
3. 创建 GlobalArena (空)
4. 预加载 Pure theory (编译到 arena)
5. 创建 Session actor:
   a. spawn session task
   b. 初始化 theory_cache (包含 Pure)
6. 创建 LspServer:
   a. 创建 mpsc channel → Session
   b. 创建 broadcast receiver ← Session
   c. 构建 tower ServiceStack
7. spawn reader task (stdin → parse JSON-RPC)
8. spawn writer task (outgoing_tx → write JSON-RPC)
9. 进入 main loop (处理 incoming messages)
```

### 优雅关闭

```
1. Editor 发送 shutdown 请求
2. LspServer:
   a. 停止接受新请求
   b. 等待所有 in-flight 请求完成 (timeout: 5s)
   c. 发送 SessionCommand::Shutdown
3. Session:
   a. 向所有 FileWorker 发送取消信号
   b. 等待所有 worker 退出 (timeout: 10s)
   c. 强制 kill 未退出的 worker
   d. 执行 Arena GC (回收所有版本)
   e. 发送 Shutdown 回复
4. LspServer 收到回复 → 发送 exit 通知 → 退出
```

### 崩溃恢复

```
FileWorker panic:
  1. tokio task 返回 JoinError
  2. Watchdog 检测到:
     a. 记录崩溃信息 (tracing::error!)
     b. broadcast SessionEvent::WorkerCrashed
     c. 如果文件仍打开: 以相同状态重新 spawn worker
     d. 否则: 清理资源, GC Arena 版本
  3. LSP 层收到 WorkerCrashed → publishDiagnostics (错误信息)
  4. 用户看到: "File worker crashed, restarting..."
```

## 详细设计：Rowan CST 集成

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

// Rowan 自动处理:
// - 增量 re-lex: 只重新词法分析受编辑影响的区域
// - 增量 re-parse: 只重建受影响的 CST 子树
// - 位置映射: GreenNode 偏移 ↔ 行号/列号
```

## 错误传播路径

```
┌─────────────────────────────────────────────────────────┐
│ 每一层定义自己的错误类型:                                 │
│                                                         │
│ KernelError   — 内核 bug (不可恢复)                       │
│   ├─ NotEquality, NotImplication, OccursCheck, ...       │
│                                                         │
│ ProofError    — 证明失败 (正常, 可恢复)                    │
│   ├─ NoUnifier, SearchBound, TacticFailed, ...           │
│                                                         │
│ SessionError  — Session 层错误                            │
│   ├─ FileNotFound, ImportCycle, WorkerCrashed, ...        │
│                                                         │
│ LspError      — LSP 协议错误                              │
│   ├─ MethodNotFound, InvalidParams, InternalError         │
│                                                         │
│ 传播规则:                                                │
│   KernelError → 不可恢复, 向上传播为 InternalError         │
│   ProofError  → 转为 Diagnostic 发送给 Editor              │
│   SessionError → 转为 LspError 返回给 Editor              │
│   LspError    → JSON-RPC error response                  │
└─────────────────────────────────────────────────────────┘
```

## 配置系统

```
/// 全局配置, 支持多层覆盖:
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

    /// FileWorker 超时 (秒)
    #[serde(default = "default_timeout")]
    worker_timeout: u64,
}

fn default_search_bound() -> usize { 60 }
fn default_max_workers() -> usize { 8 }
fn default_timeout() -> u64 { 300 }

// 加载顺序:
// 1. Config::default()
// 2. ~/.isabelle-rs/config.toml
// 3. ./.isabelle-rs.toml (项目根目录)
// 4. LSP initialize params (workspace/configuration)
```

---

## 增强并发模型（合并所有讨论）

### 完整并发栈

```
Layer         | Pattern              | Concrete Crate       | Why
LSP I/O       | async/await          | tokio + io_uring     | non-blocking, batch syscall
LSP routing   | Service middleware   | tower                | timeout/retry/rate-limit
LSP -> Session| Actor model          | tokio::mpsc (bounded)| backpressure
Session -> LSP| Pub/Sub              | tokio::broadcast     | one-to-many push
TheoryCache   | RCU (lock-free read) | arc-swap             | read-heavy, zero-block
Arena alloc   | Lock-free queue      | crossbeam::SegQueue  | multi-producer, zero-lock
Term ops      | Work-stealing        | rayon                | CPU-intensive, auto-balance
Kernel        | Dedicated pool       | rayon (isolated)     | large stack, uninterruptible
Cancel        | Token propagation    | CancellationToken    | cross-layer
```

### 为什么不用这些

| Not chosen | Reason |
|------------|--------|
| RwLock | Writer starvation. TheoryCache reads >> writes |
| Mutex | Contention bottleneck. Arena alloc on hot path |
| STM | No mature Rust STM crate |
| Channels everywhere | Cost: allocation + copy. Internal ops use function calls |
| Actor for kernel | Kernel is pure functions. Actor suits stateful services |

---

## 详细设计：LCF 内核 API (Arena 化)

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

    // transitive, combination, abstraction, beta_conversion,
    // implies_intr, implies_elim follow same pattern
}
```

## 详细设计：类型检查流 (Arena)

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

## 详细设计：跨 Arena 序列化/IPC

```rust
// 问题: 不同 FileWorker 有不同 Arena, TermId 不通用
// 解决: 序列化时转为名称路径 (interning 保证同名同义)

enum SerialTerm {  // 可跨 Arena 传输
    Const { name: String, typ: SerialType },
    Free { name: String, typ: SerialType },
    Var { name: String, index: u32, typ: SerialType },
    Bound(u32),
    Abs { name: String, typ: SerialType, body: Box<SerialTerm> },
    App { func: Box<SerialTerm>, arg: Box<SerialTerm> },
}

impl Arena {
    fn export_term(&self, id: TermId) -> SerialTerm { /* Symbol lookup */ }
    fn import_term(&mut self, st: &SerialTerm) -> TermId { /* Symbol intern */ }
}
```

## 详细设计：测试策略

| Layer | Test Type | Tool | Target |
|-------|-----------|------|--------|
| Kernel | Unit | #[test] | 3+ cases per inference rule |
| Kernel | Property | proptest | Random term -> invariant holds |
| Kernel | Fuzz | cargo-fuzz | Random bytes -> no crash |
| Kernel | Differential | custom harness | vs Isabelle output |
| Session | Integration | #[tokio::test] | Multi-file concurrency |
| LSP | End-to-end | lsp-test-harness | Simulated editor |
| Isar | Syntax | known .thy files | Parse -> correct AST |
| Perf | Benchmark | criterion | Regression detection |
| Memory | Leak | dhat/valgrind | Arena GC correct |
| Unsafe | UB | cargo miri | Unsafe code audit |

## 详细设计：V1 -> V3 迁移路径

```
Phase 1: Arena + Symbol (no external API change)
  Delete: none
  Rewrite: types.rs, term.rs (internal Arena)
  Add: kernel/arena.rs, kernel/symbol.rs
  Touch: ~25 files that use Term/Typ
  Test: all 117 V1 tests should pass

Phase 2: Module merge
  Delete: drule, more_thm, conjunction, bires, consts, facts, net
  Add: kernel/derived.rs, kernel/data.rs

Phase 3: Session Actor
  Delete: fleche/engine.rs, document/document.rs
  Add: session/ (4 files)
  Touch: server/handler.rs -> channel-based

Phase 4: Tactic AST
  Rewrite: kernel/tactic.rs (Box<dyn Fn> -> enum Tactic)

Phase 5: LSP tower
  Delete: server/handler.rs, server/transport.rs
  Add: lsp/ (router + handlers)

Phase 6: Rowan CST
  Touch: isar/token.rs (Lexer -> rowan::Lexer)

Phase 7-8: WASM, persistence, Web (future)
