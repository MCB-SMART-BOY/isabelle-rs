---
description: Candidate isabelle-kernel TCB and legacy src/core trust rules.
globs: crates/kernel/**, src/kernel/**, src/core/thm.rs, src/core/proofterm.rs, tests/kernel_*.rs
alwaysApply: false
version: 5.1
updated: 2026-07-19
---
# Kernel Rules

`crates/kernel` (re-exported by `src/kernel`) is the isolated Pure/LCF TCB
nucleus for accepted tokens, not yet the sole project theorem path. Its only
declared dependencies are `sha2` and `thiserror`. It admits no dummy type,
compat certification, fallback theorem construction, or upper-layer dependency.
`ProofObligation` and `SearchFact` cannot become `TrustedTheorem`;
unchecked constructors remain kernel-private.

`src/core` is legacy quarantine. Changes are limited to soundness fixes,
diagnostics, and migration adapters; do not add theorem-specific HOL proof
power. Preserve hypotheses, `tpairs`, `shyps`, oracles, types, theory provenance,
and replay data through every inference.

Legacy strict shape counts only as `TransitionalStrictClosed`.
`KernelTrustedClosed` requires the token returned by exact-owner
`accept_closed_theorem`; a logical `TheoremId` dependency alone grants no
authority. The standalone HOL slice has a checked `refl` basis and conservative
`True_def`; the bundled sampler accepts only the audited `HOL::TrueI` source
projection (`KernelTrustedClosed: 1/125`, `TransitionalStrictClosed: 0/125`).
General HOL declaration loading and whole-theory acceptance remain absent.
Legacy `typedecl` registration does not install HOL axioms into the
strict owner. Run `cargo +stable xtask strict` and update the trust/attack
ledgers.

类型 constructor/arity 必须显式登记，且进入 SignatureId；basis 安装前校验
全部 schema。定义入口与 replay 共享验证，后代不能补授权祖先声明。
ForallIntr/Abstraction 只扩展 premise-local Free 作用域；owner 不接收泄漏的
Free。祖先 theorem reference 必须核对规范 token 及证明负载。
