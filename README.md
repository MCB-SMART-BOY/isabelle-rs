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
[project status](docs/status/PROJECT_STATUS.md), before changing the project.

The approved long-term target is native Rust compatibility with a fixed
Isabelle2025 baseline, including user ML extensions, official logics and tools.
This is not a current capability claim. Maintained project automation now
uses native Rust `cargo +stable xtask`; scoped checks, full-project results and
remaining boundaries are recorded in [current delivery evidence](docs/status/PROJECT_STATUS.md#current-delivery-state).
The nine-root official reference observations remain historical and distinct
from native Rust closure acceptance. Native P2/P3/P4 kernel/ML work has resumed
under reviewed contracts, but complete ROOT/HOL compatibility is not accepted.
The JVM-free policy disables local official reference preparation/build/inventory;
only offline comparison remains available. The official runtime is never a
production backend, and the unresolved solver cleanup blocker still prohibits
new solver launches.
See the [A–H program](docs/status/ROADMAP.md#approved-native-compatibility-program).

## Quick Start

Prerequisites: an existing local checkout (obtain it with Git separately) and
Rust/Cargo 1.96 or newer. Run `cargo +stable xtask install` to build
from this checkout; `--check`, `--release`, and `--dir PATH` are available.
Build outputs stay in Cargo's target directory; no binary is copied onto PATH.
It does not download or upgrade Rust or pull/clone a repository. There is no
remote curl-to-shell or PowerShell installer. See the
[command catalog](scripts/README.md#verification). Running `isabelle-rs` without
a mode flag prints the research demo; `--lsp` starts an experimental protocol
server, not a complete Isabelle/PIDE implementation.

Run `cargo +stable xtask fast` for formatting and compilation, then
`cargo +stable xtask strict` for the kernel, replay, and legacy-core gate.
The independent [xtask](xtask/) package owns orchestration; see
[the command catalog](scripts/README.md#verification).

Use `cargo +stable xtask verify` for the complete repository code/test matrix,
`selftest` for product-independent automation tests, and `test` for workspace
tests with failure aggregation. The default Cargo workspace member remains the
root product; bare `cargo test` is not a full workspace run. `xtask all` adds
Tier diagnostics, not every quality gate. Follow the
[engineering workflow](docs/guides/DEVELOPMENT.md#engineering-workflow) for
behavior evidence, project gates and the separate global validator.

Use `cargo +stable xtask core` for the stack-sensitive 125-theorem regression.
`tier2` and `tier3` are opt-in, supervised statistics, not default tests:
the wrapper builds the locked worker, then applies a 600-second wall deadline
and 4096 MiB per-process address-space limit by default. Override with
`HOL_DIAGNOSTIC_TIMEOUT_SECS` / `HOL_DIAGNOSTIC_MEMORY_MIB`; it prints a fresh
output directory containing `stderr.log` and `supervisor.json`.
See [diagnostic modes](scripts/README.md#report-only-scale-workloads).

The `core` sampler reads five bundled `theories/HOL/` files, not the
`isabelle-source` Gitlink. The last source-backed sampled run (before this
automation migration) reported `TransitionalStrictClosed: 0/125` and
`KernelTrustedClosed: 1/125` for `HOL::TrueI`. This is historical evidence,
not a fresh run of the migrated xtask or a completed theory build.
The earlier pinned Isabelle2025 run reported `1/125` transitional and
`0/125` kernel-trusted; those historical counts used a different sampled
path and must not be treated as current. A historical `tier2` test returned
green while reporting 0/3872 verified, 3872 axiom-accepted (not proved), and
four file timeouts; Tier 2/3 now run only as explicit diagnostics. A historical
`quick_verify` test generated 53 theorems but reported 1233 errors and 0/5 files
passed; that generated-count
test and equivalent legacy loader tests have been removed. The Gitlink
remains a separate official source for diagnostic runs, not an implicit
fallback for the bundled sampler.

Default regressions retain the sampled 125 assertions, global HOL database,
functional/trust contracts and the nine official HOL files' no-`SyntaxError`
compatibility checks. Diagnostic completion is not theory compilation or proof.

For the currently supported source-to-kernel slices, run
`cargo +stable run --locked --bin isabelle-build -- tests/fixtures/TrustedTrueI.thy`
or `cargo +stable run --locked --bin isabelle-build -- tests/fixtures/TrustedPureIdentity.thy`.
The first returns `KernelTrustedClosed: TrueI` after the exact checked
`unfolding True_def by (rule refl)` proof. The second returns
`KernelTrustedClosed: identity` after replaying the Pure introduction rules
for `!!P::prop. PROP P ==> PROP P` with `by assumption`. Unsupported commands fail
closed. Neither fixture is part of the sampled HOL verifier or general
theory compilation.

For the audited sampled projection only, run
`cargo +stable run --locked --bin isabelle-build -- --sampled-hol-true-i theories/HOL/HOL.thy`.
It prints `KernelTrustedClosed: TrueI` after owner replay; unrelated HOL
commands and ML are not executed or authorized, and the complete theory is
not compiled.

Current verification results and remaining blockers are recorded in
[delivery evidence](docs/status/PROJECT_STATUS.md#current-delivery-state).
Recent Rust THM consumers and ML/evidence repairs have scoped behavior evidence,
not complete Isabelle/ML or ROOT/HOL acceptance. Automation tests, historical
official reference runs and a passing focused gate cannot replace complete
repository validation.

The earlier [A-package workspace run](docs/status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
completed but failed the official-source compatibility target (`section`
before `theory` in `HOL.thy`). Its scoped passes and earlier OOM/timeout
records remain historical; they are not results from this migration.


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

In legacy `src/core`, `ThmKernel::assume(A)` constructs `A |- A`, not `|- A`;
it must not be counted as a closed proved lemma. `ThmKernel::admit(ct, reason)`
records an explicitly unproved oracle footprint propagated by legacy rules.
Neither operation bypasses strict acceptance. `isabelle-kernel` has no `admit`
or fallback certification path.

See the [trust model](docs/status/TRUST.md).

## Current Status

| Area | Status |
|---|---|
| LCF-style `Thm` kernel | Research prototype with private theorem fields and hardened construction routes. |
| Strict kernel nucleus | `crates/kernel/` implements the isolated `isabelle-kernel` TCB; `src/kernel/` re-exports its API. It has explicit type declarations/arity, immutable context identity, installed-basis schema validation, conservative definitions, and exact-owner replay. It has not replaced legacy `src/core`. |
| Kernel primitive rules | Current strict derivations recursively recertify and replay under the acceptance owner; theorem-reference reuse records exact ancestor dependencies. |
| Checked instantiation | Production proof-search paths use `instantiate_checked`; legacy infallible instantiation is not a production API. |
| Oracle/admit tracking | Explicit `admitted:*` footprint tracking and propagation. |
| Closed theorem acceptance | `accept_closed_theorem` is the sole sealed-token constructor. It validates exact owner identity, recursive replay, closedness, dependencies, immutable owner/store consistency, and duplicate names before returning a child `TrustedTheory` plus `TrustedTheorem`. |
| Searchable facts vs trusted table | `HolTheoremDb` and `SearchFactDb` are proof-search/migration indexes with no conversion into the sealed token. |
| Source proposition pipeline | `source_parser` preserves file byte spans and `elaborator` resolves the supported Pure/HOL subset against a strict `ProofContext`, producing checked `CProp : prop`; `SourceId` and spans grant no authority. The separate legacy parser/adapter remains transitional. |
| Sampled HOL trust metrics | Last pre-migration source-backed sample: `TransitionalStrictClosed: 0/125`; `KernelTrustedClosed: 1/125` on five bundled files. Only `HOL::TrueI` returned an accepted token; separate HOL/Pure fixtures were not counted. Not a migrated-xtask run or full HOL theory execution. |
| Proofterm replay | Strict derivations replay with exact owner identity and the complete theorem payload. Manifest validation alone does not establish full upstream HOL compatibility; source-backed basis and definition contracts remain separately checked. |
| Isar/HOL/tools | Partial implementation; useful for experiments, not feature-compatible with Isabelle. |
| Complete legacy theory loading | One-file transactions, one available import, actual type declarations, and supported proof/document commands only. Failed or unsupported input publishes no partial Theory; failed parents block descendants. |
| Proof and automation success | Full Strict/checked result matching, scoped assumption discharge, complete rewrite certificates, and step-checked ATP evidence. Search hits, Compat facts, malformed source, and unfinished goals are not proof completion. |
| Native Rust THM consumers | `native_thm` and `native_thm_variables` exercise checked transformations, scope/owner replay, closure, acceptance and reference reuse. They are not an ML `Thm: THM` implementation and do not change the sampled count. |
| ML runtime and native plugins | Native SML execution, Context/host services and compiler-linked Rust plugin work have partial contracts and tests; complete ROOT/HOL execution, drain and compatibility gates remain unresolved. |
| Offline reference evidence | `isabelle-evidence` validates comparison data, not theorems. It is a separate workspace package outside the kernel TCB. |
| LSP/WASM/PIDE | LSP DB hover/completion labels legacy search facts; WASM exposes legacy metadata handles but does not execute/reconstruct plugin tactics. These prototypes do not accept trusted proofs. |

These are implemented boundaries and observed outcomes, not measured percentages
of Isabelle compatibility. Earlier completion estimates are retained only as
historical assessments in the [status document](docs/status/PROJECT_STATUS.md).

## Known Trust Debts

- Trusted kernel equality now uses strict `kernel_alpha_eq`. The old broad
  Free/Const and Var/Free behavior is isolated as explicit `compat_alpha_eq`
  parser/loader compatibility and remains a T2 boundary debt.
- `Typ::dummy()` remains in legacy `src/core` and compatibility consumers.
  The isolated strict kernel has no dummy type or compatibility certification.
- Some proof-search APIs still collapse `KernelError` into `Option<Thm>`. This
  is sound when rejected branches fail closed, but weak for auditability.
- Proofterm replay is currently a minimal derivation replay checker, not full
  Isabelle `proofterm.ML`.

## Roadmap

Follow the [A–H native compatibility program](docs/status/ROADMAP.md#approved-native-compatibility-program)
and its prerequisite trust milestones:

1. Preserve immutable identity, exact-owner acceptance, strict replay and the
   source-backed sampled `HOL::TrueI` path. Keep legacy facts quarantined.
2. Keep A's automation evidence separate from complete project and global quality results.
   B's historical reference baseline remains offline evidence under the
   JVM-free policy, not a native capability or new execution permission.
3. Continue the approved Pure/ML closure work under its reviewed contracts.
   C–H cover Pure, ML, Isar/HOL, official logics/tools and runtime/delivery;
   scoped Rust consumers do not discharge their complete acceptance gates.
4. Do not treat the single sampled token, parser-only checks, finite
   differential tests or ISIP design documents as full compatibility.

Parallel non-blocking design track: HPC symbolic compute may define packed IR,
a deterministic CPU baseline, and future optional Burn/CubeCL backends, but it
must never become a trusted theorem constructor or block the strict-kernel /
resolution / admitted-inventory main line.

Detailed plan: [Roadmap](docs/status/ROADMAP.md).

## Documentation

| Document | Purpose |
|---|---|
| [AGENTS.md](AGENTS.md) | Versioned, harness-neutral engineering and trusted-boundary rules. |
| [Project status](docs/status/PROJECT_STATUS.md) | Canonical current positioning, metrics, and verification limits. |
| [Baseline](docs/kernel/BASELINE.md) | Historical trusted-kernel checkpoint and gate. |
| [Trust model](docs/status/TRUST.md) | Theorem acceptance, oracle/admit semantics, and replay. |
| [Kernel rules](docs/kernel/KERNEL_RULES.md) | Kernel rule audit ledger. |
| [Kernel primitives](docs/kernel/KERNEL_PRIMITIVES.md) | Strict-kernel base primitive contracts. |
| [Acceptance inventory](docs/kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md) | Implemented acceptance boundary and remaining sampled integration. |
| [Resolution design](docs/design/RESOLUTION_DESIGN.md) | Conservative resolution and rewriting contracts. |
| [HPC design](docs/design/HPC_SYMBOLIC_COMPUTE_DESIGN.md) | Design-only untrusted symbolic-compute candidates. |
| [Attack tests](docs/kernel/KERNEL_ATTACK_TESTS.md) | Soundness regression matrix. |
| [Checked HOL propositions](docs/design/CHECKED_HOL_PROPOSITION_NORMALIZATION.md) | Source elaboration contract and deferred broader HOL work. |
| [HOL extension ADR](docs/adr/ADR-0003-hol-logic-trusted-extension.md) | Proposed target boundary; narrow implementation does not change its decision status. |
| [Historical architecture](docs/archive/ARCHITECTURE.md) | Archived architecture, not the current implementation contract. |
| [Roadmap](docs/status/ROADMAP.md) | Dependency-ordered priorities and acceptance gates. |
| [Historical gap analysis](docs/archive/GAP_ANALYSIS.md) | Archived comparison against Isabelle. |
| [Development](docs/guides/DEVELOPMENT.md) | Maintained development and verification workflow. |
| [Documentation index](docs/guides/DOCUMENT_INDEX.md) | All first-party document groups and classifications. |

## Recommended Description

Use this description externally:

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel. It focuses on explicit oracle footprints,
closed-theorem acceptance, and proof-object replay rather than broad
Isabelle/HOL feature parity.
```

Avoid describing the project as a feature-complete Rust Isabelle.

Short explanatory Rust, TOML, JSON and command examples may remain in Markdown.
Reusable automation belongs in [xtask](xtask/); [scripts/](scripts/) holds
only reference probe inputs and [classified design templates](scripts/templates/README.md),
not runnable project scripts.

## License

Isabelle-rs is a separately maintained Rust project inspired by Isabelle/Pure,
not an official Isabelle distribution. It does not claim endorsement by the
Isabelle developers or their institutions. Project-authored code, tests,
automation, documentation and templates are made available under
[Apache-2.0](LICENSE), except where a file or component states otherwise.
See [NOTICE](NOTICE) for attribution.

Third-party material retains its applicable terms: bundled theory sources
keep [theories/LICENSE](theories/LICENSE), and the optional `isabelle-source/`
reference checkout keeps its upstream `COPYRIGHT`. The project's Apache
declaration does not replace the terms for copied or adapted upstream material.
The [third-party notices](THIRD_PARTY_LICENSES) preserve both Isabelle notices
and identify the materials to which they apply. These notices are not a
project-wide determination of originality, derivative-work status or
non-infringement; such questions depend on the specific material and applicable
law.

All workspace packages declare Apache-2.0 through shared Cargo metadata.
The two library crates carry their own `LICENSE` and `NOTICE` copies.
Release archives include `LICENSE`, `NOTICE` and `THIRD_PARTY_LICENSES`;
this is not a complete dependency notice inventory or a compliance
certification. When redistributing source or binaries, satisfy the applicable
terms for the materials actually included, including required license texts,
attribution and modification notices. Binary distributions also need the
applicable notices for their actual dependencies and native components.
