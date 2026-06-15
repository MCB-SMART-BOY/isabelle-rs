---
description: Concurrency and synchronization patterns. Arc, OnceLock, thread_local!, Send/Sync, tokio runtime, actor model.
globs: src/core/net.rs, src/hol/hol_loader.rs, src/session/**, src/server/**
alwaysApply: false
version: 1.0
updated: 2026-05-29
---

# Concurrency Rules

> "Share memory by communicating; don't communicate by sharing memory." — Go proverb, applicable to Rust.

## 触发条件

使用 `Arc`, `Mutex`, `RwLock`, `OnceLock`, `thread_local!`, `tokio::spawn` 或设计 actor 时应用。

## 铁律

1. **内核操作是单线程的** — `Thm`/`ThmKernel` 不跨线程共享可变状态
2. **`Arc<Thm>` 是共享安全边界** — 定理通过 `Arc` 在线程间传递
3. **`OnceLock` 用于惰性全局** — 优于 `lazy_static!` (标准库支持)
4. **`thread_local!` 用于线程局部可变状态** — 如 DB override
5. **Actor 模型用于会话管理** — tokio mpsc channel 通信

## 模式 1: Arc<Thm> 共享

```rust
// ✅ 推荐: Arc<Thm> 用于跨线程定理共享
pub struct HolTheoremDb {
    pub by_name: HashMap<String, Arc<Thm>>,    // Arc 包装
    pub intros: Vec<Arc<Thm>>,
    pub elims: Vec<Arc<Thm>>,
    // ...
}

// ❌ 避免: 裸 Thm 在线程间传递
pub struct BadDb {
    pub by_name: HashMap<String, Thm>,  // Thm 不是 Send (包含 Rc)
}
```

## 模式 2: OnceLock 惰性初始化

```rust
// ✅ 推荐: OnceLock 惰性构建 Net
use std::sync::OnceLock;

pub struct HolTheoremDb {
    intro_net: OnceLock<Net<Arc<Thm>>>,
    elim_net: OnceLock<Net<Arc<Thm>>>,
    safe_intro_net: OnceLock<Net<Arc<Thm>>>,
    safe_elim_net: OnceLock<Net<Arc<Thm>>>,
}

impl HolTheoremDb {
    pub fn intro_net(&self) -> &Net<Arc<Thm>> {
        self.intro_net.get_or_init(|| {
            let mut net = Net::new();
            for thm in &self.intros {
                let (_, concl) = Pure::strip_imp_prems(thm.prop().term());
                net.insert(&concl, Arc::clone(thm));
            }
            net
        })
    }
}

// ❌ 避免: 加载时构建所有 nets (浪费启动时间)
```

## 模式 3: thread_local! DB Override

```rust
// ✅ 推荐: 线程局部可变状态
thread_local! {
    static DB_OVERRIDE: RefCell<Option<*const HolTheoremDb>> = const { RefCell::new(None) };
}

impl HolTheoremDb {
    pub fn with_override<F, R>(db: &HolTheoremDb, f: F) -> R
    where F: FnOnce() -> R
    {
        DB_OVERRIDE.with(|cell| {
            let old = cell.replace(Some(db as *const _));
            let result = f();
            cell.replace(old);
            result
        })
    }

    pub fn get() -> &'static HolTheoremDb {
        DB_OVERRIDE.with(|cell| {
            if let Some(ptr) = *cell.borrow() {
                unsafe { &*ptr }
            } else {
                GLOBAL_DB.get().expect("no DB initialized")
            }
        })
    }
}
```

## 模式 4: Actor 模型 (Session)

```rust
// ✅ 推荐: mpsc channel 通信
use tokio::sync::mpsc;

pub enum SessionMessage {
    ProcessFile { path: PathBuf, reply: oneshot::Sender<Result<()>> },
    Shutdown,
}

pub struct Session {
    rx: mpsc::Receiver<SessionMessage>,
    state: SessionState,
    file_worker: FileWorker,
}

impl Session {
    pub async fn run(&mut self) {
        while let Some(msg) = self.rx.recv().await {
            match msg {
                SessionMessage::ProcessFile { path, reply } => {
                    let result = self.process_file(&path);
                    let _ = reply.send(result);
                }
                SessionMessage::Shutdown => break,
            }
        }
    }
}
```

## 模式 5: Send + Sync 边界

```rust
// ✅ 确保跨线程类型正确标记
pub struct SessionBuilder {
    graph: TheoryGraph,        // Send + Sync ✅
    db: Arc<HolTheoremDb>,     // Send + Sync ✅ (Arc)
    config: BuildConfig,       // Send + Sync ✅
}

// 检查: 所有字段必须是 Send + Sync
// 如果包含 Rc → !Send, 需要换 Arc
// 如果包含 RefCell → !Sync, 需要换 RwLock/Mutex
```

## 并发模型总结

| 组件 | 并发模型 | 同步原语 |
|------|---------|---------|
| LCF 内核 | 单线程 | 无 |
| HolTheoremDb | 只读共享 | `Arc` + `OnceLock` |
| Net 索引 | 惰性构建 | `OnceLock` |
| DB Override | 线程局部 | `thread_local!` + `RefCell` |
| Session 管理 | Actor | `tokio::mpsc` |
| LSP Server | 异步 I/O | `tokio` + `tower` |
| WASM Runtime | Host 隔离 | `wasmtime::Store` |
| TheoryProcessor | 顺序处理 | 无 (方法内状态) |

## 检查清单

- [ ] 跨线程共享数据用 `Arc`，非 `Rc`
- [ ] 可变全局状态用 `OnceLock`/`thread_local!`/`Mutex`/`RwLock`
- [ ] Actor 通信用 `mpsc` channel，非共享内存
- [ ] `unsafe` 代码有安全文档 (如 DB_OVERRIDE 的裸指针)
- [ ] 无死锁风险 (锁获取顺序一致)
- [ ] Tokio 任务有超时或取消机制

## 反模式

| ❌ | ✅ |
|----|----|
| `Rc<T>` 跨线程 | `Arc<T>` |
| `RefCell<T>` 跨线程 | `RwLock<T>` 或 `Mutex<T>` |
| `lazy_static!` | `OnceLock` (std) |
| 共享可变 HashMap 无锁 | `RwLock<HashMap<...>>` |
| 忙碌等待 (spin loop) | channel / Condvar |
| `block_on` 在 async context | 纯 async 或纯 sync |
