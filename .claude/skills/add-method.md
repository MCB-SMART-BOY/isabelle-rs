---
name: add-method
description: Add a new proof method: 4-step pattern (enum variant → execute dispatch → implementation → name resolution). Metis as reference example.
category: development
version: 2.0.0
triggers: [add proof method, new search strategy, port method from Isabelle]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit]
---

# Add Proof Method

Add a new proof method to the 25-method engine following the established 4-step pattern.

## The 4-Step Pattern

```
1. Enum variant → 2. Execute dispatch → 3. Implementation → 4. Name resolution
```

## Step 1: Enum Variant

In `src/isar/method.rs`, add to the `Method` enum (before `Skip`/`Fail`):

```rust
pub enum Method {
    // ... existing: Assumption, Rule, Simp, Auto, Blast, Fast, Step,
    //               Best, Depth, DupStep, Induct, Cases, Unfold, Fold,
    //               Insert, Erule, Drule, Frule, Coinduct, Try, Metis ...
    MyNewMethod,  // ← ADD HERE
    Skip,
    Fail,
}
```

## Step 2: Execute Dispatch

In `execute_depth()`, add to the match:

```rust
fn execute_depth(&self, state: &Thm, depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm> {
    match self {
        // ... existing arms ...
        Method::MyNewMethod => Self::my_new_method_exec(state, depth, premises),
        _ => vec![state.clone()],
    }
}
```

## Step 3: Implementation

```rust
fn my_new_method_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm> {
    // RULE 1: Safe rules first — ALWAYS
    let current = Method::apply_safe_rules(state, premises);
    if current.nprems() == 0 { return vec![current]; }

    // RULE 2: Depth guard — prevents infinite recursion
    if depth > 15 { return vec![state.clone()]; }

    // RULE 3: Use nets, not linear scan
    let db = HolTheoremDb::get();
    for rule in db.intro_net().lookup(&current.prem(0).unwrap_or(/* fallback */)) {
        if let Some(result) = ThmKernel::bicompose(true, rule, &current, 0) {
            if result.nprems() == 0 { return vec![result]; }
            let sub = Self::my_new_method_exec(&result, depth + 1, premises);
            if sub.iter().any(|r| r.nprems() == 0) { return sub; }
        }
    }

    // RULE 4: Return state on timeout — NOT empty vec
    vec![current]
}
```

## Step 4: Name Resolution

In `exec_single_method()`:

```rust
if inner == "mynewmethod" || inner.starts_with("mynewmethod ") {
    return Method::MyNewMethod.execute(state, premises);
}
```

## Design Rules

| ✅ DO | ❌ DON'T |
|--------|----------|
| `apply_safe_rules` as first step | Skip safe rules |
| `intro_net().lookup()` | `db.intros` linear scan |
| `depth > N → return vec![state]` | Infinite recursion |
| `vec![state]` on timeout | `vec![]` (signals failure) |
| Matching before resolution | Direct resolution (unexpected instantiation) |

## Reference: Metis Integration (Real Example)

The `Method::Metis` variant shows the complete pattern:

```rust
// Step 1: enum variant
Method::Metis,

// Step 2: dispatch
Method::Metis => Self::metis_exec(state, depth, premises),

// Step 3: implementation
fn metis_exec(state: &Thm, _depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm> {
    let current = Self::apply_safe_rules(state, premises);
    if current.nprems() == 0 { return vec![current]; }

    let mut metis = crate::tools::metis::MetisProver::with_limits(10000);
    metis.add_premises(premises);
    match metis.prove(&current) {
        Some(result) if result.nprems() == 0 => vec![result.as_ref().clone()],
        _ => Method::Auto.execute(&current, premises),
    }
}

// Step 4: name resolution
if inner == "metis" || inner.starts_with("metis ") {
    return Method::Metis.execute(state, premises);
}
```

## Testing

```bash
cargo test --lib isar::method                # Method tests
cargo test test_verify_all_core_files -- --nocapture  # Regression
```

## Related

- `.claude/rules/proof-methods.md` — Full method rules and safe rules
- `.claude/skills/verify.md` — Verification debugging
- `src/isar/method.rs:32-77` — Current `Method` enum
- `src/isar/method.rs:95-187` — `execute_depth()` dispatch
