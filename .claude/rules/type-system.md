---
description: Checked type schemes, sorts, CTerm/CProp certification, and dummy-type debt.
globs: crates/kernel/src/typ.rs, crates/kernel/src/cterm.rs, crates/kernel/src/signature.rs, crates/kernel/src/context.rs, crates/kernel/src/logic.rs, src/core/types.rs, src/core/thm.rs
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Type System Rules

The strict kernel accepts only declared type constructors with exact arities,
declared constants/frees, and fully checked terms. Type declarations enter
`SignatureId`; unknown types are never inferred as arity zero. Theorem
propositions are `CProp : prop`; HOL `bool` terms require source-aware
`HOL.Trueprop` elaboration before proposition certification.

Do not infer types from name similarity or compatibility Free/Const/Var matching.
Polymorphic instantiation and axiom schemas must validate schemes, sorts, and
all nested annotations against the same immutable signature/context before
installing a basis. `Typ::dummy()` remains legacy parser debt and is never
tolerated at the final trusted boundary.
