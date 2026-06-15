# isabelle-rs v1.9.0-dev 项目状态

> 当前会话：2026-06-16 | 状态：Route A 稳定性优先，Tier2 验证进行中

---

## 一、项目概况

isabelle-rs v1.9.0-dev — Isabelle 证明助手内核的 Rust 移植。
- LCF 可信内核 (15 ops + tpairs/shyps) + 高阶合一 + Isar 证明语言
- ~54K Rust LOC, 124 files, 714 tests (638 lib + 76 integration)
- Core 5/5 files 125/125 (100%), Tier2 6/19 files 100% (running in tmux)

## 二、Route A 完成状态

| Step | 内容 | 状态 |
|------|------|:--:|
| 1 | 5 测试修复 | ✅ |
| 2 | OOM 根因修复 (repeat_conv + stack) | ✅ |
| 3 | Tier2 验证扩展 | 🔄 tmux 'tier2': 6/19 ✅, Fields running |
| 4 | 属性系统补完 | ✅ begin_lemma + lemmas + declare + attrs propagation |
| 5 | 文档同步 | ✅ .claude/ + docs/ 已更新 |

## 三、关键架构

```
.thy → OuterSyntax::parse_spans() → CommandSpan[]
  → TheoryProcessor::process_span()
    ├─ lemma → begin_lemma() → parse_name_attrs() [NEW: 属性解析]
    ├─ lemmas → process_lemmas_cmd() [NEW]
    ├─ declare → process_declare_cmd() [NEW]
    └─ ...
  → HolTheoremDb::extend() → compute_db_categories() [属性分类]
```

## 四、已知问题

| 问题 | 严重度 |
|------|:--:|
| Fields.thy 证明搜索慢 (360 simp calls, arithmetic-heavy) | 🟡 |
| HolTheoremDb LazyLock 首次加载全部 1,473 .thy files | 🟡 |
| ctr_sugar test_verify_systematic (disj_parts unwrap) | 🟢 |

## 五、常用命令

```bash
# 构建
cargo check --lib

# tier2 验证 (tmux)
tmux new-session -d -s tier2 "RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture 2>&1"
tmux attach -t tier2  # 查看进度

# 核心验证
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files --lib -- --nocapture

# 所有测试
RUST_MIN_STACK=268435456 cargo test --lib
```

## 六、提交规则

- 中文提交信息
- 不含 Co-Authored-By
- Git user: MCB-SMART-BOY
