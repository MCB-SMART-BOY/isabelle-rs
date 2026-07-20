---
description: Checked type schemes, sorts, CTerm/CProp certification, and dummy-type debt.
globs: src/kernel/typ.rs, src/kernel/cterm.rs, src/kernel/signature.rs, src/core/types.rs, src/core/thm.rs
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Type System Rules

The strict kernel accepts only declared constants/frees and fully checked terms.
Theorem propositions are `CProp : prop`; HOL `bool` terms require source-aware
`HOL.Trueprop` elaboration before proposition certification.

Do not infer types from name similarity or compatibility Free/Const/Var matching.
Polymorphic instantiation must validate type schemes and sort constraints in an
immutable signature/context. `Typ::dummy()` remains legacy parser debt and is
never tolerated at the final trusted boundary.
