---
name: audit-kernel
description: Audit kernel for Typ::dummy() presence, Thm field initialization, tpairs/shyps propagation, CTerm invariants. Covers both strict src/kernel/ and legacy src/core/.
category: safety
version: 2.1.0
triggers: [kernel change, thm.rs, logic.rs, drule.rs, more_thm.rs, new inference rule, strict kernel, src/kernel]
permissions: [Bash:rg, Bash:cargo test, Read]
---

# Audit Kernel

Audit LCF kernel code for safety violations. Every kernel change must pass this audit.

## Two-Kernel Reality

The project is mid-strangler-pattern kernel reset (ADR-0001 accepted):

```text
src/kernel/  → new strict TCB nucleus — active development
src/core/    → legacy quarantine — frozen, migration target
```

## Quick Scan — Strict Kernel (`src/kernel/`)

```bash
# 1. Typ::dummy() in strict kernel — ZERO TOLERANCE (should not even exist)
rg "dummy" src/kernel/

# 2. Direct KernelThm construction outside rules.rs — FORBIDDEN
rg "KernelThm\s*\{" src/kernel/ --glob '!rules.rs'

# 3. ProofObligation used as theorem — FORBIDDEN
rg "ProofObligation" src/kernel/thm.rs src/kernel/theory.rs

# 4. SearchFact promoted to TrustedTheorem — FORBIDDEN
rg "SearchFact.*TrustedTheorem\|TrustedTheorem.*SearchFact" src/kernel/

# 5. Undeclared constants/frees in CTerm construction — suspicious
rg "CTerm::new\|CProp::new" src/kernel/

# 6. Crate-wide strict-kernel escape hatches — FORBIDDEN
rg "pub\\(crate\\)" src/kernel/
```

## Quick Scan — Legacy Core (`src/core/`)

```bash
# 1. Typ::dummy() in kernel — ZERO TOLERANCE
rg "Typ::dummy\(\)" src/core/thm.rs src/core/logic.rs src/core/drule.rs src/core/more_thm.rs

# 2. Direct Thm construction outside thm.rs — FORBIDDEN
rg "Thm\s*\{" src/core/ --glob '!thm.rs'

# 3. CTerm::certify without annotation — suspicious
rg "CTerm::certify\(" src/core/thm.rs | grep -v certify_typed | grep -v certify_annotated

# 4. Missing require_non_dummy at kernel boundaries
rg "require_non_dummy" src/core/

# 5. compat_alpha_eq in trusted kernel rules — FORBIDDEN
rg "compat_alpha_eq" src/core/thm.rs
```

## Checklist — Strict Kernel

### Global Invariants (from ADR-0001)

- □ No dummy type in `Ty`.
- □ Constants declared in `Signature`.
- □ Local frees declared in `ProofContext`.
- □ `CTerm`/`CProp` produced only by strict certification.
- □ `KernelThm` produced only by `KernelRules`.
- □ Internal constructors are `pub(in crate::kernel)` or narrower, never
  crate-wide `pub(crate)`.
- □ `ProofObligation` is not a theorem.
- □ `ClosedThm` wraps theorems with no hypotheses.
- □ `TrustedTheorem` is a checked `ClosedThm`.
- □ `TrustedTheory` accepts only `TrustedTheorem`.
- □ `SearchFactDb` facts cannot become trusted theorem-table entries.

### Primitive Rules (15 implemented)

| Operation | Critical Invariant |
|-----------|-------------------|
| `assume` | Input is `CProp`; output is `OpenThm`, `A \|- A` |
| `reflexive` | Uses certified type, NOT dummy; output is `ClosedThm` |
| `symmetric` | Premise must be equality; hypotheses preserved |
| `transitive` | Middle terms strict alpha-equivalent; types identical |
| `implies_intr` | Exactly one matching hypothesis discharged |
| `implies_elim` | Antecedent strict alpha-equivalent; hypotheses unioned |
| `beta_conversion` | Input must be `App` with `Abs` func; strict de Bruijn substitution |
| `forall_intr` | Free variable must have been declared; x not free in hypotheses |
| `forall_elim` | Theorem must be `Forall`; argument type must match binder type |
| `combination` | Both premises must be equality; domain must match argument type |
| `abstraction` | Premise must be equality; x not free in hypotheses |
| `equal_intr` | Both premises must be implications; antecedents/consequents cross-match |
| `equal_elim` | Major must be propositional equality (object_ty = prop); minor must match LHS |
| `generalize` | Free → Var; uses fresh indices (start = max_var_index + 1); unmatched frees no-op |
| `instantiate` | Var → CTerm via InstEntry; exact (name,index,type) match; duplicates (name,idx)-keyed; Bound rejected; simultaneous |
| `resolve1_match` | Conservative one-way backward resolution; deterministic substitution order; no lifting/flex-flex/full unification |

## Checklist — Legacy Core

### Thm Struct (all fields must be set)

```rust
pub struct Thm {
    hyps: Hyps,                    // □ α-equivalence class
    prop: CTerm,                   // □ certified, no dummy type
    maxidx: usize,                 // □ ≥ max index in prop + hyps
    tpairs: Vec<(Term, Term)>,     // □ propagated from premises
    shyps: Vec<Sort>,              // □ merged from premises
    oracles: Vec<Arc<str>>,        // □ propagated from premises
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
# 1. Strict kernel attack tests
cargo test --test kernel_rewrite_soundness

# 2. Legacy kernel unit tests
cargo test --test kernel_soundness
cargo test --lib core::thm core::logic core::drule core::unify

# 3. Full regression
RUST_MIN_STACK=268435456 cargo test --lib

# 4. Core verification
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
```

## Common Violations

| Pattern | Detection | Severity |
|---------|----------|:--------:|
| Dummy type in strict kernel | `rg "dummy" src/kernel/` | 🔴 |
| `Typ::dummy()` in legacy thm.rs | `rg "Typ::dummy\(\)" src/core/thm.rs` | 🔴 |
| `KernelThm` outside `rules.rs` | `rg "KernelThm\s*\{" src/kernel/ --glob '!rules.rs'` | 🔴 |
| `dest_equals()` instead of `_with_type()` | `rg "dest_equals\(" src/core/thm.rs` | 🟠 |
| Missing tpairs/shyps/oracles in Thm constructor | Code review | 🔴 |
| `unwrap()` in kernel path | `rg "\.unwrap\(\)" src/core/thm.rs src/kernel/` | 🟠 |
| Missing `free_in` before `forall_intr` | Code review | 🟡 |
| Missing `occurs_check` in unification | Code review | 🟡 |
| `compat_alpha_eq` in trusted rules | `rg "compat_alpha_eq" src/core/thm.rs` | 🔴 |
| SearchFact → TrustedTheorem conversion | Code review | 🔴 |

## Related

- `.claude/rules/kernel.md` — Full kernel rules
- `.claude/skills/verify.md` — Verification after kernel changes
- `docs/ADR-0001-kernel-core-rewrite.md` — Strangler pattern decision
- `docs/KERNEL_PRIMITIVES.md` — Strict kernel rule contracts
