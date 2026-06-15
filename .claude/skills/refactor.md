---
name: refactor
description: Safe refactoring for isabelle-rs: kernel safety, method dispatch, theory pipeline, attribute pipeline patterns.
category: development
version: 2.0.0
triggers: [refactor, extract module, rename, restructure, code smell]
permissions: [Bash:cargo test, Bash:cargo clippy, Bash:cargo fmt, Read, Edit, Grep]
---

# Refactor

Safely refactor isabelle-rs code following project-specific patterns and safety constraints.

## Prerequisites

```bash
# Capture baselines before ANY refactoring
cargo test --lib 2>&1 | tee test-before.log
cargo clippy -- -D warnings 2>&1 | tee clippy-before.log
```

## Refactoring Workflow

```
1. IDENTIFY → 2. BASELINE → 3. EXTRACT → 4. VERIFY → 5. REPEAT
```

After each extraction:
```bash
cargo test --lib 2>&1 | diff - test-before.log
```

## Project-Specific Safety Constraints

### Kernel Code (`src/core/thm.rs`)
- **NEVER** change `Thm` field visibility — must stay `pub(crate)`
- **NEVER** expose `Thm { .. }` constructor outside `thm.rs`
- **ALWAYS** preserve `ThmKernel` as sole public interface
- **ALWAYS** keep 7 Thm fields: hyps, prop, maxidx, tpairs, shyps, derivation, serial

### Method Dispatch (`src/isar/method.rs`)
- **NEVER** reorder the six-layer fallback in `verify_lemma()`
- New methods follow the 4-step pattern (see `add-method` skill)
- Don't extract `apply_safe_rules` out of the module — it's coupled to `HolTheoremDb`

### Theory Pipeline (`src/theory/loader.rs`)
- **NEVER** bypass `TheoryProcessor` — it's the single entry point
- Don't expose `LocalTheory` internals
- Parent theories go through `registry.rs`

### Attribute Pipeline (`src/hol/hol_loader.rs`)
- Attribute parsing must use `parse_attrs()` (not naive `split(',')`)
- DB classification must use `compute_db_categories()` from `attrib.rs`
- Don't duplicate attribute strings in `add_builtins()` — use constant helpers

## Project-Specific Patterns

### Extract Function (long method.rs functions)
```rust
// Before: 100+ line execute_depth match arm
Method::Auto => { /* 50 lines */ }

// After: extract to named method
Method::Auto => Self::auto_exec(state, depth, premises),
```

### Extract Module (from 4000-line hol_loader.rs)
```rust
// Candidates for extraction from hol_loader.rs:
// → lemma parsing functions → src/hol/lemma_parser.rs
// → datatype parsing functions → src/hol/datatype_parser.rs
// → attribute pipeline → already in src/isar/attrib.rs
```

### Enum Over Magic Strings
```rust
// ❌
match method_name { "auto" => ..., "fast" => ..., _ => ... }

// ✅ (already done — preserve this pattern)
pub enum Method { Auto, Fast, ... }
```

## Common Code Smells

| Smell | Location | Fix |
|-------|---------|-----|
| `Typ::dummy()` outside tests | Anywhere | Use `CTerm::certify_annotated()` |
| `dest_equals()` without type | `core/` | Use `dest_equals_with_type()` |
| Linear scan of rules | `isar/method.rs` | Use `net.lookup()` |
| Recursive term traversal | `core/`, `isar/` | Iterativize (see `debug-overflow`) |
| `unwrap()` in kernel path | `core/thm.rs` | Return `Result` |

## Anti-Patterns

| ❌ | ✅ |
|----|----|
| Refactor + add features together | Pure refactoring, separate PR |
| Change 20 files at once | 1-5 files per commit |
| Manual rename | rust-analyzer "Rename Symbol" |
| Keep dead code "for later" | Delete — git history recovers it |
| Abstract prematurely (YAGNI) | Abstract only when ≥3 use sites exist |

## Related

- `.claude/rules/refactoring.md` — Full refactoring rules
- `.claude/rules/api-design.md` — API design constraints
- `.claude/skills/audit-kernel.md` — Kernel safety audit
