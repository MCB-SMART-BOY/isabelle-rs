---
description: 理论加载规则。.thy解析, DB构造, DAG, nets, override, session_builder。
globs: src/hol/hol_loader.rs, src/hol/theory_graph.rs, src/theory/loader.rs, src/theory/session_builder.rs
alwaysApply: false
version: 2.1
updated: 2026-05-28
---

# 理论加载规则

## 触发条件

修改 `src/hol/hol_loader.rs`, `src/hol/theory_graph.rs`, `src/theory/loader.rs`, `src/theory/session_builder.rs` 时应用。

## 数据流

```
.thy → TheoryProcessor::process_source()
  → OuterSyntax::parse_spans() → CommandSpan[]
  → process_span() 命令分发
    ├─ theory → LocalTheory::begin()
    ├─ lemma → IsarProof::lemma()
    ├─ definition/fun/inductive/datatype → parse + rules
    ├─ have/show → proof sub-goals
    ├─ apply/by → method dispatch
    ├─ qed → goal refinement → close_block
    └─ end → LocalTheory::finalize() → Arc<Theory>
  → HolTheoremDb::extend()
    ├─ by_name, intros, elims, simps
    ├─ safe_intros, safe_elims         (auto-classified)
    ├─ def_index                       (go-to-definition) ✅
    ├─ intro_net, elim_net             (OnceLock, lazy)
    └─ safe_intro_net, safe_elim_net   (OnceLock, lazy)
```

## TheoryProcessor Pipeline

```rust
// 单文件
let mut proc = TheoryProcessor::with_parent(parent, "MyTheory");
let theory = proc.process_source(source);

// 批量编译
let builder = SessionBuilder::new("HOL");
let report = builder.build_from_dir("isabelle-source/src/HOL")?;
// → BuildReport { total, succeeded, failed, panicked, theorems, lemmas }
```

## 属性分类 (Phase 10.4c ✅)

```
[intro!] → safe intro    [intro] → unsafe    [intro?] → extra
[elim!]  → safe elim     [elim]  → regular
[simp] → simplification   [iff] → intro+elim+simp
```

## TheoryGraph DAG

```rust
graph.scan("isabelle-source/src/HOL")?;  // 1,472 nodes
let order = graph.topological_sort()?;
// 增量: for name in &order { db.extend(&load_file(&path)?.0); }
```

## DB Override

```rust
thread_local! { static DB_OVERRIDE: RefCell<Option<*const HolTheoremDb>> = ...; }
HolTheoremDb::with_override(&custom_db, || { verify_lemma(&lem); });
```

## Net 构建

```rust
// intro: index by conclusion
intro_net.get_or_init(|| {
    for thm in &self.intros {
        let (_, concl) = Pure::strip_imp_prems(thm.prop().term());
        net.insert(&concl, Arc::clone(thm));
    }
});
// elim: index by first premise (major premise)
// safe_*: same pattern, using safe_intros/safe_elims
```

## 文件

| 文件 | LOC | 内容 |
|------|:--:|------|
| `hol/hol_loader.rs` | 3999 | 解析 + DB + nets + builtins + TypeEnv |
| `hol/theory_graph.rs` | 502 | DAG + 加载 + 验证测试 |
| `theory/loader.rs` | ~900 | TheoryProcessor: .thy → commands → theorems |
| `theory/local_theory.rs` | ~270 | 增量理论构建 |
| `theory/registry.rs` | ~50 | 父理论注册 |
| `theory/session_builder.rs` | ~350 | 批量编译 + CLI |
