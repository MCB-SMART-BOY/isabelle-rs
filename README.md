# Isabelle-rs

Rust research prototype of an Isabelle/Pure-inspired LCF kernel.

This repository is **not** a full Rust rewrite of Isabelle. The accurate current
position is:

```text
A Rust implementation of an Isabelle/Pure-inspired LCF kernel
with explicit oracle footprints, closed-theorem acceptance,
and minimal proofterm replay.
```

The project has moved beyond a toy parser. Its current value is trusted-kernel
engineering: theorem construction boundaries, admitted/oracle tracking, closed
proved theorem statistics, and proof-object replay. It is still far from full
Isabelle/HOL + Isar + PIDE + AFP feature parity.

Agents and contributors should read [AGENTS.md](AGENTS.md), then
[docs/PROJECT_STATUS.md](docs/PROJECT_STATUS.md), before changing the project.

## Quick Start

Prerequisites: Git and Rust 1.96 or newer. From a local checkout,
[scripts/install.sh](scripts/install.sh) and
[scripts/install.ps1](scripts/install.ps1) provide locked check, debug-build,
and release-build modes; see [scripts/README.md](scripts/README.md) for the
maintained command catalog. The default `isabelle-rs` binary is a research demo,
and `--lsp` starts an experimental protocol server rather than a complete
Isabelle/PIDE implementation.

Run `scripts/dev-check.sh fast` for formatting and compilation, then
`scripts/dev-check.sh strict` for the kernel, replay, and legacy-core gate.
All reusable verification commands are maintained in
[scripts/dev-check.sh](scripts/dev-check.sh), not duplicated in Markdown.

Use `scripts/dev-check.sh core`, `tier2`, or `tier3` for stack-sensitive theory
runs. The wrapper supplies the standard large stack and freezes `Cargo.lock`.

Do not claim full `cargo test --lib` success unless the known
`theory::loader::tests::test_batch_scan_theories` stack-overflow issue is
verified as fixed in the current checkout; the explicit wrapper mode is
`scripts/dev-check.sh lib`.

`cargo +stable check --locked --all-targets` currently fails in the pre-existing
`benches/kernel_benchmarks.rs` target: two calls use the private
`proofterm::check_proof`, and two implication benchmarks pass `Result<Thm>`
instead of `Thm`. The same four errors occur at `origin/dev`; do not report the
all-targets gate as green until that separate benchmark debt is fixed.

## Trust Model

The core rule is simple:

```text
TransitionalStrictClosed =
  legacy strict construction + no oracles + no hypotheses + no unresolved tpairs + no dummy types

KernelTrustedClosed =
  exact-owner accept_closed_theorem + replayed closed CProp : prop + authorized dependencies
```

Important API distinction:

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hyps + no unresolved tpairs
is_strict_closed_proved() == strict construction + is_closed_proved() + no dummy types
```

`ThmKernel::assume(A)` constructs `A |- A`. It is a valid open theorem, not
`|- A`, and must not be counted as a closed proved lemma.

`ThmKernel::admit(ct, reason)` is the explicit accepted-without-proof entry
point. Its oracle footprint is propagated through later kernel inferences.

See [docs/TRUST.md](docs/TRUST.md).

## Current Status

| Area | Status |
|---|---|
| LCF-style `Thm` kernel | Research prototype with private theorem fields and hardened construction routes. |
| Strict kernel nucleus | `src/kernel` is the candidate target TCB nucleus: no dummy type or compat certification; immutable signature, theory, and accepted-fact ancestry; exact context stamps; proof obligations and search facts separated from theorem authority; primitive Pure rules plus conservative wrappers. It has not yet replaced legacy `src/core`. |
| Kernel primitive rules | Current strict derivations recursively recertify and replay under the acceptance owner; theorem-reference reuse records exact ancestor dependencies. |
| Checked instantiation | Production proof-search paths use `instantiate_checked`; legacy infallible instantiation is not a production API. |
| Oracle/admit tracking | Explicit `admitted:*` footprint tracking and propagation. |
| Closed theorem acceptance | `accept_closed_theorem` is the sole sealed-token constructor. It validates exact owner identity, recursive replay, closedness, dependencies, immutable owner/store consistency, and duplicate names before returning a child `TrustedTheory` plus `TrustedTheorem`. |
| Searchable facts vs trusted table | `HolTheoremDb` and `SearchFactDb` are proof-search/migration indexes with no conversion into the sealed token. |
| Source proposition AST | `src/isar/source_ast.rs` is a data-only, parser-independent syntax model with raw name/syntax spellings, grouping, binders, type annotations, and half-open byte spans. It carries no trusted context and has no conversion into kernel propositions or theorems. |
| Sampled HOL trust metrics | `TransitionalStrictClosed: 1/125`; `KernelTrustedClosed: 0/125`. Synthetic Pure acceptance is excluded; current `HOL::TrueI` remains bool-valued legacy output. |
| Proofterm replay | Every current strict `Derivation` variant replays with exact `TheoryId` / `SignatureId` propagation. Ancestor theorem dependencies are supported; object-logic axiom/basis and conservative-definition replay remain absent. |
| Isar/HOL/tools | Partial implementation; useful for experiments, not feature-compatible with Isabelle. |
| LSP/WASM/PIDE | Skeletons only; not current priority. |

Relative completion estimates:

| Scope | Estimate |
|---|---:|
| Full Isabelle/HOL + Isar + PIDE + AFP ecosystem | 15%-25% |
| Isabelle/Pure-inspired Rust kernel research slice | 45%-60% |
| Minimal end-to-end Isabelle/Pure trusted kernel | 30%-40% |
| Oracle footprints + closed theorem acceptance specialty | 65%-75% |
| T4 proofterm replay/checker | 10%-20% |
| HOL tools and automation | 10%-20% |

## Known Trust Debts

- Trusted kernel equality now uses strict `kernel_alpha_eq`. The old broad
  Free/Const and Var/Free behavior is isolated as explicit `compat_alpha_eq`
  parser/loader compatibility and remains a T2 boundary debt.
- `Typ::dummy()` still appears at trusted boundaries. The direction is stricter
  parsing, type inference, and `CTerm` certification, not more kernel tolerance.
- Some proof-search APIs still collapse `KernelError` into `Option<Thm>`. This
  is sound when rejected branches fail closed, but weak for auditability.
- Proofterm replay is currently a minimal derivation replay checker, not full
  Isabelle `proofterm.ML`.

## Roadmap

Current priority order (aligned with ADR-0002 layered platform vision):

1. Keep the completed immutable context identity and exact-owner acceptance
   boundary stable.
2. Keep the implemented data-only source proposition AST unresolved and
   disconnected from theorem authority.
3. Next, integrate source parsing and elaborate checked judgments, constants,
   and polymorphic type schemes, including explicit `HOL.Trueprop`, into the
   existing `CProp : prop` boundary.
4. Install the HOL logical basis as an immutable data-only manifest replayed by
   generic kernel code.
5. Add a generic conservative definition extension; do not promote
   `true_def_transport`.
6. Re-derive `HOL::TrueI` through the new kernel before implementing
   `HOL::trans` or another theorem adapter.
7. Continue strict-kernel stabilization and replay coverage without adding HOL
   primitives to legacy `src/core`.
8. Defer workspace, session, APP, LSP, and broad HOL coverage until these trust
   boundaries close.

Parallel non-blocking design track: HPC symbolic compute may define packed IR,
a deterministic CPU baseline, and future optional Burn/CubeCL backends, but it
must never become a trusted theorem constructor or block the strict-kernel /
resolution / admitted-inventory main line.

Detailed plan: [docs/ROADMAP.md](docs/ROADMAP.md).

## Documentation

| Document | Purpose |
|---|---|
| [AGENTS.md](AGENTS.md) | Versioned, harness-neutral engineering and trusted-boundary rules. |
| [docs/PROJECT_STATUS.md](docs/PROJECT_STATUS.md) | Canonical current positioning and status. |
| [docs/BASELINE.md](docs/BASELINE.md) | Trusted-kernel checkpoint, gate, and next entry point. |
| [docs/TRUST.md](docs/TRUST.md) | Trust model, theorem acceptance, oracle/admit semantics. |
| [docs/KERNEL_RULES.md](docs/KERNEL_RULES.md) | Kernel rule audit ledger. |
| [docs/KERNEL_PRIMITIVES.md](docs/KERNEL_PRIMITIVES.md) | Strict-kernel base primitive rule contracts. |
| [docs/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](docs/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md) | Current strict-kernel acceptance inventory, missing context bindings, and minimal acceptance API. |
| [docs/RESOLUTION_DESIGN.md](docs/RESOLUTION_DESIGN.md) | Resolution family design and `resolve1_match` / `subst_premise` / conservative `bicompose` status. |
| [docs/HPC_SYMBOLIC_COMPUTE_DESIGN.md](docs/HPC_SYMBOLIC_COMPUTE_DESIGN.md) | Design-only untrusted CPU/GPU symbolic compute layer for candidate generation and prefiltering. |
| [docs/KERNEL_ATTACK_TESTS.md](docs/KERNEL_ATTACK_TESTS.md) | Soundness regression matrix. |
| [docs/CHECKED_HOL_PROPOSITION_NORMALIZATION.md](docs/CHECKED_HOL_PROPOSITION_NORMALIZATION.md) | Source-aware checked HOL proposition elaboration contract and `HOL::trans` diagnostic. |
| [docs/ADR-0003-hol-logic-trusted-extension.md](docs/ADR-0003-hol-logic-trusted-extension.md) | Proposed Pure/HOL/Isar trust-layer boundary; design only. |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Current architecture and trusted-boundary data flow. |
| [docs/ROADMAP.md](docs/ROADMAP.md) | Concrete next phases and acceptance gates. |
| [docs/GAP_ANALYSIS.md](docs/GAP_ANALYSIS.md) | Honest comparison against Isabelle. |
| [docs/DEVELOPMENT.md](docs/DEVELOPMENT.md) | Development and verification commands. |

## Recommended Description

Use this description externally:

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel. It focuses on explicit oracle footprints,
closed-theorem acceptance, and proof-object replay rather than broad
Isabelle/HOL feature parity.
```

Avoid describing the project as a feature-complete Rust Isabelle.

Short explanatory Bash, Rust, PowerShell, TOML, and JSON blocks may remain in
Markdown. Large runnable or duplicated snippets belong in [scripts/](scripts/)
or [scripts/templates/](scripts/templates/), whose classifications and
validation limits are documented in
[scripts/templates/README.md](scripts/templates/README.md).

## License

The Rust implementation is licensed under the
[Apache License 2.0](LICENSE). Bundled Isabelle theory sources retain their
upstream terms in [theories/LICENSE](theories/LICENSE).
