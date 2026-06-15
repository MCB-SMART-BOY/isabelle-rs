---
name: add-isar-command
description: Add a new Isar command to the three-mode state machine (Forward/Chain/Backward) with goal refinement patterns.
category: development
version: 2.0.0
triggers: [add Isar command, proof language, state machine, have/show, fix/assume, qed]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit]
---

# Add Isar Command

Add a new Isar proof language command to the three-mode state machine.

## State Machine Reference

```
Forward  → fix, assume, note, let, have, show
Chain    → facts linked, waiting for have/show
Backward → apply, by, proof (sub-block)

Transitions:
  Forward  ── lemma ──► Backward
  Backward ── proof ──► Forward (new sub-block)
  Forward  ── qed ────► Backward (parent goal)
  Chain ──── have/show ► Forward
  Forward  ── have/show ► Backward (sub-goal)
  Backward ── apply ──► Backward (same goal)
  Backward ── done/by ─► Forward (goal solved)
```

## 5-Step Pattern

### 1. Add CommandKind

```rust
// src/isar/keyword.rs
pub enum CommandKind { /* ... */ MyCommand }
```

### 2. Add Parser

```rust
// src/isar/outer_syntax.rs
fn parse_command(&mut self) -> Option<CommandSpan> {
    match self.current_kind() {
        CommandKind::MyCommand => self.parse_my_command(), // ...
    }
}
```

### 3. Add State Machine Handler

```rust
// src/isar/proof.rs
fn exec_my_command(&mut self, span: &CommandSpan) -> Result<ProofAction> {
    match self.mode {
        ProofMode::Forward => { /* context manipulation */ }
        ProofMode::Chain => { /* consume chained fact */ }
        ProofMode::Backward => return Err(/* not allowed in proof mode */),
    }
    Ok(ProofAction::Continue)
}
```

### 4. Handle Mode Transition

| Your command does... | Set mode to... |
|---------------------|---------------|
| Extends context (fix, assume, note) | `ProofMode::Forward` |
| Creates a sub-goal (have, show) | `ProofMode::Backward` |
| Consumes chained facts | `ProofMode::Forward` |
| Applies a method (apply, by) | `ProofMode::Backward` |
| Finalizes a proof (qed) | `ProofMode::Forward` |

### 5. Handle Goal Refinement (if applicable)

```rust
// If your command creates a goal that must match a parent:
fn exec_show(&mut self, span: &CommandSpan) -> Result<ProofAction> {
    let stmt = self.parse_statement(span)?;
    let refines = self.top().goal.as_ref().map(|g| g.statement.clone());
    //                                         ↑ MUST set refines for qed
    self.push_goal(Goal { statement: stmt, refines, .. });
    self.mode = ProofMode::Backward;
    Ok(ProofAction::Continue)
}
```

## Design Rules

1. **`show` MUST record `refines`** — for `qed` parent goal refinement
2. **`have` auto-adds to facts**, `show` does not
3. **`then` sets chained_fact** for next `have`/`show`
4. **`hence` = `then have`; `thus` = `then show`**
5. **Validate mode before executing** — use `self.require_mode()`
6. **Consume `chained_fact` in Chain mode** — don't leave stale facts

## Key Files

| File | What to Modify |
|------|---------------|
| `src/isar/keyword.rs` | `CommandKind` variant |
| `src/isar/outer_syntax.rs` | Parser + classification |
| `src/isar/proof.rs` | State machine handler |
| `src/isar/proof_state.rs` | If command affects proof state |

## Related

- `.claude/rules/isar.md` — Isar proof language rules
- `.claude/skills/add-method.md` — Adding proof methods
- `src/isar/proof.rs` — `IsarProof` + `ProofMode` + `Goal`
