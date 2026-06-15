---
description: Isar 证明语言规则。IsarProof 状态机 (3 modes), 命令分发, 目标精化。Phase 23: induct/cases 完成。
globs: src/isar/proof.rs, src/isar/proof_context.rs, src/isar/toplevel.rs, src/isar/outer_syntax.rs
alwaysApply: false
version: 3.2
updated: 2026-05-28
---

# Isar 规则

## 触发条件

修改 `src/isar/proof.rs`, `proof_context.rs`, `toplevel.rs`, `outer_syntax.rs` 时应用。

## IsarProof 状态机 (三模式)

```rust
pub enum ProofMode {
    Forward,   // 配置模式: fix, assume, note, let, have, show
    Chain,     // 链式模式: 事实已链接, 等待 have/show
    Backward,  // 证明模式: apply, by, proof (sub-block)
}
```

## 状态转换

```
Forward ── lemma/theorem ──► Backward
Backward ── proof ──► Forward (new sub-block)
Forward ── qed ──► Backward (parent goal)
Forward ── fix/assume/note ──► Forward
Chain ── have/show ──► Forward
Forward ── have/show ──► Backward (sub-goal)
Backward ── apply ──► Backward (same goal, refined)
Backward ── done/by ──► Forward (goal solved)
Forward ── next ──► Forward (switch to next subgoal)
```

## 命令分发 (全部完成 ✅)

```
lemma/theorem  → lemma()         ✅  进入证明模式
proof          → proof()         ✅  打开子块
qed            → qed()           ✅  关闭证明块 + 父目标精化
{ / }          → open/close_brace ✅ 嵌套块
next           → next()          ✅  下一个子目标
have           → have()          ✅  中间目标
show           → show()          ✅  目标 (记录 refines)
hence/thus     → then + have/show ✅
fix            → fix()           ✅  固定变量
assume         → assume()        ✅  局部假设
obtain         → obtain()        ✅  存在消去
apply          → apply()         ✅  方法应用 (method dispatch)
by             → by()            ✅  终端证明
done           → done()          ✅  关闭所有块
sorry          → sorry()         ✅  跳过证明
from           → from()          ✅  链接事实
with           → with()          ✅  from + using
using          → using()         ✅  目标事实
let            → let_bind()      ✅  局部绑定
note           → note()          ✅  命名事实
then           → then_chain()    ✅  链式传递
also           → also()          ✅  计算链追加
finally        → finally()       ✅  计算链终结
moreover       → moreover()      ✅  事实累积
ultimately     → ultimately()    ✅  累积后链式
induct         → induct()        ✅  归纳法 (lookup_theorem→DB)
cases          → cases()         ✅  情况分析 (.cases/.exhaust lookup)
case           → case_()         ✅  命名情况
defer/prefer   → defer/prefer()  ✅  子目标重排
```

## 目标精化 (show → qed)

```rust
// qed 实现:
let proved_goal = self.top().goal.clone();
self.close_block();
if let (Some(goal), Some(parent)) = (proved_goal, self.top_mut().goal) {
    if let Some(expected) = &goal.refines {
        if goal.statement == *expected {
            let parent_ct = CTerm::certify(expected.clone());
            parent.goal_thm = ThmKernel::trivial(parent_ct)?;
        }
    }
}
```

## 定理查找 (Phase 23 ✅)

```rust
fn lookup_theorem(&self, name: &str) -> Option<Thm> {
    use crate::hol::hol_loader::HolTheoremDb;
    let db = HolTheoremDb::get();
    db.by_name.get(name).map(|t| (**t).clone())
}
```

## 理论加载 pipeline

```rust
let mut proc = TheoryProcessor::with_parent(parent, "MyTheory");
let thy = proc.process_source(source);
// 内部: parse_spans → process_span → LocalTheory + IsarProof → finalize
```

## 设计规则

1. `have` 结果自动加入 facts
2. `then` → 下一个 have/show 的 chained_fact
3. `hence` = `then have`; `thus` = `then show`
4. `show` 必须记录 `refines` 用于 qed 精化
5. `qed` 必须检查 show 结果匹配父目标
6. 理论加载用 `TheoryProcessor`, 不用直接调 `LocalTheory`
7. 命令分类用 `OuterSyntax::classify()`, 不用 `Keywords` 直接查询
