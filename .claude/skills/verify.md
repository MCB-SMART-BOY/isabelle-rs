---
name: verify
description: Verify lemma(s) through the six-layer fallback architecture. Run tests, diagnose failures, debug proof search.
category: verification
version: 2.1.0
triggers: [lemma verification, proof failure, test failure, "this lemma doesn't prove", verify fails]
permissions: [Bash:cargo test, Bash:cargo run, Read, Grep]
---

# Verify

Verify that lemmas prove correctly through the isabelle-rs proof engine.

## When to Use

- Lemma verification returns `None` or wrong result
- A previously-passing proof now fails
- After modifying kernel / method dispatch / unify / simplifier
- After modifying strict kernel (`src/kernel/`)
- Running the regression suite after any `src/core/` or `src/isar/` change

## The Six-Layer Architecture

```
verify_lemma():
  0 → Safe rules (match → elim_match → resolution)    [O(log n) net lookup]
  1 → Built-in Var-override (pre-stored DB theorems)
  2 → Anonymous datatype axiom
  3 → Isar structured proof (3-mode state machine)
  4 → exec_proof → 27 methods (incl. meson, metis, auto, blast, simp, induct, fast, best)
  5 → Axiom acceptance (generalize_thm — last resort)
```

## Workflow

### 1. Run the Right Tests

```bash
# Strict kernel attack tests (fastest, no stack tuning)
cargo test --test kernel_rewrite_soundness

# Fastest — kernel unit tests (32MB stack OK)
cargo test --lib core::thm

# Medium — full lib tests (256MB stack needed)
RUST_MIN_STACK=268435456 cargo test --lib

# Core verification — 5/5 files 125/125 (100%, 256MB)
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture

# Extended verification — 15-30 files
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier3_verify -- --nocapture

# Single file verification
cargo test --test single_verify -- --nocapture
```

### 2. Isolate the Failing Lemma

```bash
# Run with verbose output to see which lemma fails
RUST_BACKTRACE=1 cargo test test_verify_all_core_files -- --nocapture 2>&1 | grep -E "FAILED|error|None"
```

### 3. Diagnose by Layer

| Symptom | Layer | What to Check |
|---------|:-----:|------|
| Method name not recognized | 4 | `exec_single_method()` dispatch — is the method string handled? |
| Safe rules don't fire | 0 | `safe_intro_net` built? Rule in correct net? |
| `bicompose` returns `None` (⚠️ LEGACY core) | 0-4 | Rule pattern doesn't match goal. Check unification. |
| `ThmKernel::*` returns `Err` | Kernel | Type mismatch — likely `Typ::dummy()` leaking |
| Strict kernel invariant fails | Kernel | `check_kernel_invariants(Strict)` — check `src/kernel/invariant.rs` |
| DB has 0 theorems | Loading | `parse_lemmas` silently failed. Check `.thy` path. |
| Stack overflow | Any | Recursive fn not iterativized. See `debug-overflow` skill. |
| Verified but wrong result | 5 | Axiom fallback accepted unproven lemma |

### 4. Debug Specific Methods

```rust
// In src/isar/method.rs, exec_single_method():
// Find your method string and trace which arm it hits
if inner == "metis" || inner.starts_with("metis ") { ... }
```

### 5. Trace the Net Lookup

When a rule should match but doesn't:
```bash
# Add debug prints in method.rs apply_safe_rules():
# eprintln!("  subgoal: {:?}", subgoal);
# eprintln!("  intro_cands: {} rules", intro_cands.len());
```

## Test Matrix

| Test Suite | Files | Stack | Time |
|-----------|:-----:|:-----:|:----:|
| `kernel_rewrite_soundness` | — | 32MB | <1s |
| `core::thm` | — | 32MB | <1s |
| `core::unify` | — | 32MB | <1s |
| `tools::metis` | — | 32MB | <1s |
| `hol::hol_loader::lemma_tests` | — | 32MB | ~2s |
| `test_verify_all_core_files` | 5 | 256MB | ~25s |
| `tier2_verify` | 15 | 256MB | ~30s |
| `tier3_verify` | 16 | 256MB | ~60s |
| `test_batch_scan_theories` | ~100 | **OVERFLOWS** | N/A |

## Common Fixes

| Problem | Fix |
|---------|-----|
| Method unrecognized | Add string → `Method` mapping in `exec_single_method` |
| Rule not in net | Check `compute_db_categories()` in `hol_loader.rs::extend()` |
| Unify fails | `apply_safe_rules` uses *matching* (match_flag=true), not unification. Check pattern structure. |
| Type dummy in kernel | Use `CTerm::certify_annotated()` not `CTerm::certify()` |
| `dest_equals` → missing type | Use `Pure::dest_equals_with_type()` to extract equality type |
| Strict kernel invariant fails | Check `src/kernel/invariant.rs` for the violated condition |

## Related

- `.claude/rules/testing.md` — Test commands and stack requirements
- `.claude/rules/proof-methods.md` — Method dispatch and safe rules
- `.claude/rules/kernel.md` — Kernel invariants and type safety
- `.claude/skills/debug-overflow.md` — Stack overflow diagnosis
- `.claude/skills/audit-kernel.md` — Kernel safety audit
- `docs/KERNEL_PRIMITIVES.md` — Strict kernel rule contracts
