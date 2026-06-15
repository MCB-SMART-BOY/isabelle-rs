---
name: port-isabelle
description: Port a function/module from Isabelle/ML to Rust: type mapping, pattern translation, kernel integration, testing.
category: development
version: 2.0.0
triggers: [port from Isabelle, Isabelle ML, ML to Rust, new module from Isabelle]
permissions: [Bash:cargo test, Bash:cargo check, Read, Edit, Grep]
---

# Port from Isabelle

Port a function or module from Isabelle/ML to isabelle-rs Rust.

## When to Use

- Porting a missing Isabelle module (e.g., `meson.ML`, `argo.ML`)
- Porting a specific function or proof tactic
- Adding a new HOL tool (code generator, SMT, quickcheck)

## Workflow

### 1. Locate the ML Source

```bash
# Isabelle source (typically in ~/.isabelle or isabelle-source/)
find isabelle-source -name "*.ML" | grep -i "<module>" 2>/dev/null
```

Key Isabelle/ML directories:
- `src/Pure/` — kernel, Isar, tactics
- `src/HOL/Tools/` — HOL tools (BNF, Sledgehammer, Metis, etc.)
- `src/Provers/` — classical reasoner, simplifier

### 2. Map ML → Rust Types

| Isabelle/ML | isabelle-rs Rust |
|-------------|-----------------|
| `term` | `crate::core::term::Term` |
| `typ` | `crate::core::types::Typ` |
| `thm` | `crate::core::thm::Thm` |
| `cterm` | `crate::core::thm::CTerm` |
| `theory` | `crate::core::theory::Theory` |
| `Proof.context` | `crate::core::context::ProofContext` |
| `tactic` | `crate::core::tactic::Tactic` |
| `conv` | `crate::core::conv::Conv` |
| `morphism` | `crate::core::morphism::Morphism` |
| `sort` | `crate::core::sorts::Sort` |
| `envir` / `Envir.envir` | `crate::core::envir::Envir` |
| `string` | `String` |
| `int` | `usize` / `i64` |
| `'a list` | `Vec<T>` |
| `'a option` | `Option<T>` |
| `'a -> 'b` | `fn(&T) -> U` or trait |

### 3. Translate Key Patterns

```ocaml
(* Isabelle/ML: pattern matching *)
case term of
  Const (name, typ) => ...
  | Free (name, typ) => ...
  | Var (name, index, typ) => ...
  | Bound i => ...
  | Abs (name, typ, body) => ...
  | App (func, arg) => ...  (* $ *)
```

```rust
// isabelle-rs Rust: same structure
match term {
    Term::Const { name, typ } => { ... }
    Term::Free { name, typ } => { ... }
    Term::Var { name, index, typ } => { ... }
    Term::Bound { index } => { ... }
    Term::Abs { name, typ, body } => { ... }
    Term::App { func, arg } => { ... }
}
```

```ocaml
(* Isabelle/ML: theorem construction via kernel *)
Thm.assume ct
Thm.implies_intr ct thm
Thm.implies_elim thm1 thm2
Thm.forall_intr x thm
Thm.forall_elim ct thm
```

```rust
// isabelle-rs Rust: identical API
ThmKernel::assume(ct)
ThmKernel::implies_intr(&ct, &thm)
ThmKernel::implies_elim(&thm_imp, &thm_a)
ThmKernel::forall_intr(name, typ, &thm)
ThmKernel::forall_elim(ct, &thm)
```

### 4. Place the Code Correctly

| ML Location | Rust Destination |
|------------|-----------------|
| `src/Pure/thm.ML` | `src/core/thm.rs` |
| `src/Pure/unify.ML` | `src/core/unify.rs` |
| `src/Pure/Isar/method.ML` | `src/isar/method.rs` |
| `src/Pure/Isar/proof.ML` | `src/isar/proof.rs` |
| `src/HOL/Tools/inductive.ML` | `src/hol/inductive.rs` |
| `src/HOL/Tools/simp.ML` | `src/tools/simp.rs` |
| `src/Provers/classical.ML` | inline in `src/isar/method.rs` |

### 5. Add Tests

```bash
# Unit tests inline in the new module
cargo test --lib <module>::

# Integration tests if needed
# Add to tests/ directory

# Verify no regression
RUST_MIN_STACK=268435456 cargo test --lib
```

## Common Porting Pitfalls

| ML Pattern | Rust Gotcha |
|-----------|------------|
| `case x of ...` with multiple matches | Rust `match` is exhaustive — add `_ =>` arms |
| `fun f x =` recursive | Check for deep recursion → iterativize |
| `ref` mutable cells | Use `&mut` or `Cell`/`RefCell` |
| `SOME x` / `NONE` | `Some(x)` / `None` |
| `x |> f` | `f(x)` or method chaining |
| `op ::` (list cons) | `Vec::push` or `vec![head, rest..]` |
| `map f xs` | `xs.iter().map(f).collect()` |
| `foldl f a xs` | `xs.iter().fold(a, f)` |
| `f o g` (composition) | `\|x\| f(g(x))` |
| Lazy evaluation | Rust is eager — use closures or lazy init |

## Related

- `.claude/rules/kernel.md` — Kernel rules (type safety critical)
- `.claude/rules/api-design.md` — API design for new modules
- `.claude/skills/add-method.md` — Porting a proof method specifically
- `docs/GAP_ANALYSIS.md` — What's still missing from Isabelle
