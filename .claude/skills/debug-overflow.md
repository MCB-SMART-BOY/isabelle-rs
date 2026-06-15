---
name: debug-overflow
description: Diagnose stack overflow → select iterative pattern → convert → verify. Four patterns: stack, worklist, continuation frames, DFS.
category: debugging
version: 2.0.0
triggers: [stack overflow, "overflowed its stack", SIGABRT, recursion too deep]
permissions: [Bash:cargo test, Bash:RUST_MIN_STACK, Read]
---

# Debug Stack Overflow

Diagnose stack overflow errors and convert recursive functions to iterative implementations using four proven patterns.

## When to Use

- Any test crashes with "overflowed its stack" or SIGABRT
- `RUST_MIN_STACK=1073741824` (1GB) still overflows → infinite recursion
- Deeply nested term processing (inductive, fixpoint, large .thy files)

## Diagnostic Workflow

### 1. Reproduce

```bash
# Find minimum failing stack size
RUST_MIN_STACK=33554432 cargo test <test> -- --nocapture   # 32MB
RUST_MIN_STACK=268435456 cargo test <test> -- --nocapture  # 256MB
RUST_MIN_STACK=1073741824 cargo test <test> -- --nocapture # 1GB — if still fails → infinite recursion
```

### 2. Identify the Recursive Function

```bash
RUST_BACKTRACE=full cargo test <test> -- --nocapture 2>&1 | grep -E "^  [0-9]+:" | head -20
# Look for repeated function names in the backtrace
```

### 3. Choose the Right Pattern

```
Does the function rebuild the tree bottom-up?
  YES → Pattern 3: Continuation Frames
  NO  → Does it modify shared state?
           YES → Pattern 2: Worklist
           NO  → Pattern 1: Simple Stack

Is it a search function with a depth bound?
  YES → Pattern 4: Iterative Deepening DFS
```

### 4. Convert and Verify

After conversion:
```bash
# Same output for shallow inputs
cargo test <unit_tests> -- --nocapture

# Full regression
RUST_MIN_STACK=268435456 cargo test --lib

# Verify the specific test that was overflowing
RUST_MIN_STACK=33554432 cargo test <original_test> -- --nocapture
```

## Pattern Quick Reference

### Pattern 1: Simple Stack
For: Traversing tree to collect info, no rebuild.
```rust
// ❌ Recursive
fn compute_maxidx(t: &Term) -> usize { ... recursive ... }

// ✅ Iterative
fn compute_maxidx(t: &Term) -> usize {
    let mut maxidx = 0;
    let mut stack = vec![t];
    while let Some(term) = stack.pop() {
        match term {
            Term::App { func, arg } => { stack.push(arg); stack.push(func); }
            Term::Abs { body, .. } => stack.push(body),
            Term::Var { index, .. } => maxidx = maxidx.max(*index),
            _ => {}
        }
    }
    maxidx
}
```

### Pattern 2: Worklist
For: Modifying shared state during traversal, no rebuild.
```rust
// ✅ Process items from stack, modify env in-place
let mut stack: Vec<DPair> = pairs;
stack.reverse();
while let Some(item) = stack.pop() { /* process, push children */ }
```

### Pattern 3: Continuation Frames
For: Bottom-up tree reconstruction. Use Process/Build stack frames.
```rust
enum Frame { Process(Term), BuildApp, BuildAbs(Symbol, Typ) }
// Push Process to expand, push Build* for reconstruction
```

### Pattern 4: Iterative Deepening
For: Search with depth bound. Loop with increasing bound.
```rust
fn fast_exec(state, premises) -> Vec<Thm> {
    for bound in 0..8 {
        if let Some(r) = dfs(state, bound, premises) { return vec![r]; }
    }
    fallback(state, premises)
}
```

## Completed Conversions

| Function | File | Pattern | Stack Before | Stack After |
|----------|------|:------:|:------------:|:-----------:|
| `unify_dpairs` | `unify.rs` | Worklist | 512MB | 32MB |
| `match_pattern` | `unify.rs` | Continuation | 512MB | 32MB |
| `norm_term` | `envir.rs` | Continuation | 256MB | 32MB |
| `compute_maxidx` | `thm.rs` | Stack | 128MB | 32MB |
| `subst_bounds` | `term_subst.rs` | Continuation | 128MB | 32MB |
| `incr_bound` | `term.rs` | Continuation | 256MB | 32MB |
| `occurs_check` | `unify.rs` | Stack | 128MB | 32MB |
| `free_in` | `thm.rs` | Stack | 128MB | 32MB |

## Known Overflow Locations

| Test | File | Status |
|------|------|:------:|
| `test_batch_scan_theories` | `theory/loader.rs` | 🔴 Overflows at 1GB |
| `test_verify_all_core_files` | `isar/method.rs` | 🔴 Overflows at 1GB |
| `test_batch_verify_all` | `isar/method.rs` | 🔴 Overflows at 1GB |

## Related

- `.claude/rules/iterative.md` — Full patterns with detailed examples
- `.claude/skills/verify.md` — Verification debugging
