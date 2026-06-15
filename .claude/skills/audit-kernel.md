---
name: audit-kernel
description: Audit kernel for Typ::dummy() presence, Thm field initialization, tpairs/shyps propagation, CTerm invariants.
category: safety
version: 2.0.0
triggers: [kernel change, thm.rs, logic.rs, drule.rs, more_thm.rs, new inference rule]
permissions: [Bash:rg, Bash:cargo test, Read]
---

# Audit Kernel

Audit LCF kernel code for safety violations. Every kernel change must pass this audit.

## Quick Scan

```bash
# 1. Typ::dummy() in kernel — ZERO TOLERANCE
rg "Typ::dummy\(\)" src/core/thm.rs src/core/logic.rs src/core/drule.rs src/core/more_thm.rs

# 2. Direct Thm construction outside thm.rs — FORBIDDEN
rg "Thm\s*\{" src/core/ --glob '!thm.rs'

# 3. CTerm::certify without annotation — suspicious
rg "CTerm::certify\(" src/core/thm.rs | grep -v certify_typed | grep -v certify_annotated

# 4. Missing require_non_dummy at kernel boundaries
rg "require_non_dummy" src/core/
```

## Checklist

### Thm Struct (all 7 fields must be set)

```rust
pub struct Thm {
    hyps: Hyps,                    // □ α-equivalence class
    prop: CTerm,                   // □ certified, no dummy type
    maxidx: usize,                 // □ ≥ max index in prop + hyps
    tpairs: Vec<(Term, Term)>,     // □ propagated from premises
    shyps: Vec<Sort>,              // □ merged from premises
    derivation: Derivation,        // □ records the rule used
    serial: u64,                   // □ unique (auto-incremented)
}
```

### Kernel Operations

| Operation | Critical Invariant |
|-----------|-------------------|
| `reflexive` | Uses `ct.term_type()`, NOT `Typ::dummy()` |
| `symmetric` / `transitive` | Uses `dest_equals_with_type()` |
| `combination` | Returns `Err(NotFunctionType)` — no dummy fallback |
| `abstraction` | `x` not free in hypotheses |
| `forall_intr` | `x` not free in hypotheses |
| `forall_elim` | Term type matches bound variable |
| `instantiate` | Types and terms consistently instantiated |

### Type-Aware Equality — The Only Correct Pattern

```rust
// ✅ CORRECT
let typ = ct.term_type().clone();
let eq = Pure::mk_equals(typ, t.clone(), t);

// ✅ CORRECT
let (t, u, eq_typ) = Pure::dest_equals_with_type(thm.prop.term())?;
let new_prop = Pure::mk_equals(eq_typ, u.clone(), t.clone());

// ❌ FORBIDDEN
let eq = Pure::mk_equals(Typ::dummy(), t, u);
```

## Post-Audit Verification

```bash
# 1. Kernel unit tests
cargo test --lib core::thm core::logic core::drule core::unify

# 2. Full regression
RUST_MIN_STACK=268435456 cargo test --lib

# 3. Core verification
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
```

## Common Violations

| Pattern | Detection | Severity |
|---------|----------|:--------:|
| `Typ::dummy()` in thm.rs | `rg "Typ::dummy\(\)" src/core/thm.rs` | 🔴 |
| `dest_equals()` instead of `_with_type()` | `rg "dest_equals\(" src/core/thm.rs` | 🟠 |
| Missing tpairs/shyps in Thm constructor | Code review | 🔴 |
| `unwrap()` in kernel path | `rg "\.unwrap\(\)" src/core/thm.rs` | 🟠 |
| Missing `free_in` before `forall_intr` | Code review | 🟡 |
| Missing `occurs_check` in unification | Code review | 🟡 |

## Related

- `.claude/rules/kernel.md` — Full kernel rules
- `.claude/skills/verify.md` — Verification after kernel changes
