# Development Guide

This guide covers day-to-day development commands for Isabelle-rs.

Start with root [AGENTS.md](../../AGENTS.md). For project positioning, read
[PROJECT_STATUS.md](../status/PROJECT_STATUS.md); for trust semantics, read
[TRUST.md](../status/TRUST.md).

## Engineering Workflow

Use one lifecycle for code, documentation, configuration and investigations:
**SCOPE → DESIGN → IMPLEMENT → REVIEW → VERIFY → DELIVER**.
This is the task workflow, not the A–H delivery packages or the numbered trust
milestones in [ROADMAP.md](../status/ROADMAP.md).

| Stage | Required outcome |
|---|---|
| SCOPE | Inspect fresh repository state; identify the user-visible goal, owned files, authoritative code/tests, non-goals, existing failures and acceptance evidence. Preserve unrelated work. |
| DESIGN | Choose the smallest change; define failure semantics, trust boundaries, independent work slices and verification. Obtain approval for destructive actions, material scope/risk changes or unresolved consequential choices. |
| IMPLEMENT | Read before editing, reuse existing patterns, reproduce bugs narrowly and migrate affected callers atomically. Do not turn failed search or official reference output into Rust proof authority. |
| REVIEW | Check facts, scope and contracts independently for TCB, public API, permission and other trust-boundary changes; add security review for dependency, authentication, secret or data-handling changes. Review substantial documentation changes for consistency. |
| VERIFY | Exercise the changed path, run the applicable project gates, then the complete global validator. Aggregate independent failures; distinguish passed, failed, blocked and unrun checks. |
| DELIVER | Update current docs and routing, retain dated evidence, report impact and remaining risks. A failed applicable gate remains a blocker. Commit, push, tag, publish and deployment require separate explicit authorization. |

Small, reversible changes may use a short plan without an approval pause.
Broad but conventional changes do not need a pause merely because they span
many files. A material change to the agreed result or risk does.

Before delegation, fix shared contracts and assign disjoint owned paths.
Workers do not run builds, tests, linters or formatters while edits are in
flight; the integrating agent verifies the final tree. Worktrees are opt-in.
Keep reproduction output, source identity, exact command/toolchain and resource
limits with the evidence. Do not rerun an already reported failure merely to
confirm it or replace a failed contract with a weaker check.

### Verification Selection

| Change | Behavior evidence and project gates |
|---|---|
| Documentation or agent guidance | Read the actual reader route; check facts, local links/anchors and frontmatter; run `cargo +stable xtask docs`. Parse changed configuration; parsing alone does not prove harness loading. |
| Automation | Run the affected real command, including failure/artifact paths; run `selftest` and affected gates. Command definitions and checks live in `xtask/`; `scripts/` holds reference probe inputs and design templates only. |
| Kernel, replay or trust boundary | Positive and rejection/attack evidence plus `strict`; add `core` if the sampled path or its reported outcomes change. |
| Parser, proof engine or runtime | Exercise the changed CLI/document path and its focused contract tests; run `strict` when trust semantics are affected. |
| Workspace regression | Use `cargo +stable xtask test`, which runs the workspace with `--no-fail-fast`; `lib` is root-library only and bare `cargo test` is not a workspace gate. |
| Integrated delivery | Run `cargo +stable xtask verify` for the complete repository code/test matrix, then the separate security/global gates. A focused pass cannot replace this matrix. |
| Broad HOL statistics | Only the explicitly requested supervised `tier2`, `tier3`, `broad` or `profile` mode; preserve manifests, budgets, logs and completion status separately from proof evidence. |

The [command catalog](../../scripts/README.md#verification) owns exact options.
`verify` checks the fixed official source identity and cleanliness, workspace
formatting, strict all-targets Clippy, locked all-targets compilation, the
kernel zero-warning check, documentation subgates, the kernel firewall and
full workspace tests. It does not execute report-only Tier workloads,
official reference builds or network-backed security audits.
`release-check` first validates the tag, then runs this same repository matrix;
neither command publishes or grants release authority. `all` remains an explicit
diagnostic aggregate, not a synonym for verification.

After behavior evidence and project gates, run the full
`~/.omp/agent/validate.sh` from the repository root. `--quick` is not delivery
evidence. Its gates are Secrets → Format → Lint → Type Check → Build/Eval →
Dependency Audit → Test. Report repository, security and global results
separately; missing tools and failed prerequisites are failures, not skips.
Independent gates continue after failure so their diagnostics are retained.

### Test Ownership and Evidence

| Layer | Location and entry point | Required evidence |
|---|---|---|
| Automation contracts | `xtask/src/`, `xtask/tests/`; `selftest` | Arguments, subprocess lifecycle, failure propagation, archive/file boundaries and reference decoding; independent of product compilation. |
| Trusted-kernel contracts | `crates/kernel/`, `tests/kernel_*.rs`; `strict` | Positive derivations plus wrong-owner, malformed-input, scope and replay rejection cases. |
| Product contracts and regression | `src/`, `tests/`; workspace `test` | Parser, loader, proof, process and protocol behavior, including the bundled sampler and official-source compatibility assertions. |
| End-to-end smoke | Actual CLI or public runtime entry point | Execute the changed user path and observe its result; a passing unit test or build is not a substitute. |
| Report-only diagnostics | Supervised `isabelle-scale-hol`; offline reference comparison | Explicit invocation, fixed source identity, limits, logs and completion status; never counted as accepted Rust theorems. Local official reference execution is disabled. |

Keep one observable behavior per deterministic test. Use real temporary
files/processes for boundary contracts and bounded condition polling rather
than fixed sleeps. Do not assert source text, incidental wording or forwarded
arguments merely to test wiring. Existing contract suites own regression
coverage; add a permanent test only for a plausible uncovered failure.

Before the complete product matrix, `cargo +stable xtask pinned-source` requires
the fixed `isabelle-source` HEAD, a clean checkout, the matching index Gitlink
and required source files. It inspects source without starting Isabelle.
Missing official sources must not turn compatibility tests into green skips.
The bundled `core` sampler and product-independent `selftest` do not
require the external Isabelle runtime. Under the JVM-free policy,
`reference prepare/build/inventory` are rejected before workspace access or
process creation. Independently approved offline comparison and native Rust
build/acceptance are separate contracts. The known solver cleanup blocker
continues to prohibit new solver launches.

### CI, Release and Submission

CI runs the same repository `verify` matrix and independent required security
checks; neither property tests nor dependency findings become advisory to
make CI green. Platform jobs establish only the commands they execute.
Release verification uses the exact selected tag and the same matrix, not
Tier statistics. Artifact names must match their actual target architecture.
Pushing a branch is not permission to create a tag, publish binaries or deploy.

Before a requested commit, review the entire proposed tree, including existing
work, dependency intent and Gitlink identity. Resolve the intended scope before
mixing unrelated work into a delivery. Passing quality checks does not complete
a native compatibility milestone or authorize new proof rules.

For the OMP submission gate, stage the complete authorized non-ignored tree,
verify index/worktree equality and clear unsupported index flags. Run the
complete global validator against the final unchanged tree; do not bypass a
missing/stale validation stamp. One explicit commit instruction authorizes one
direct `git commit`, not a push, tag or release. Push only with separate
explicit authorization, using a normal non-force push to the agreed branch.
If the remote has diverged, stop rather than rewriting user history. Verify an
authorized push and report remote CI separately from local checks.

## Environment

- Rust/Cargo stable matching the repository requirement and an existing local
  checkout; install Rust and clone separately before invoking xtask. `install`
  neither upgrades Rust nor clones/pulls the checkout.
- Repository-local [Cargo configuration](../../.cargo/config.toml) sets
  `RUST_MIN_STACK=268435456` and `RUST_TEST_THREADS=1` by default for
  memory-bounded test runs; environment overrides remain possible.
  `cargo xtask` inherits the invoking toolchain; canonical checks use
  `cargo +stable xtask` with rustup stable available. Leaf Cargo commands
  do not switch toolchains.
- Reference observation ML/theory inputs remain preserved historical or
  offline-evidence material, not another project automation language. Do not
  provision a JVM or restart the disabled local official reference workflow.

## Common Commands

Fast checks:

Run `cargo +stable xtask fast`.

Trusted-kernel gate (not the full-project quality gate):

Run `cargo +stable xtask strict`. This runs formatting, locked compilation,
kernel zero-warning and firewall checks; `kernel_rewrite_soundness`,
`kernel_context_identity`, `kernel_trusted_acceptance`, and
`kernel_declaration_boundary` integration suites; kernel soundness and doctests;
the `isabelle-kernel` crate unit tests; and legacy `core::` compatibility tests.
The actual checks are in
[xtask](../../xtask/src/tasks.rs).

`cargo +stable xtask checkpoint` adds focused feature tests to `strict`.
Run `cargo +stable xtask core` for the bundled 125-theorem sample, **not** the
independent strict source fixtures. `tier2` and `tier3` are opt-in supervised
statistics; `broad` runs `core`, `tier2`, `tier3` and aggregates independent failures.
The Tier 2/3 wrapper builds the locked worker before the default 600-second
wall deadline and 4096 MiB per-process address-space limit; override via
`HOL_DIAGNOSTIC_TIMEOUT_SECS` / `HOL_DIAGNOSTIC_MEMORY_MIB`. It prints a fresh
output directory for `stderr.log` and `supervisor.json`; see
[scale workload modes](../../scripts/README.md#report-only-scale-workloads).
The last source-backed sampled core result, before this migration, was
`TransitionalStrictClosed: 0/125` and `KernelTrustedClosed: 1/125`; only the
audited `HOL::TrueI` projection reached owner replay. This dated evidence is
not a new migrated-xtask run or whole-theory compilation; see
[current status](../status/PROJECT_STATUS.md).

Use `cargo +stable xtask test` for full workspace regression and `lib` for the
root library only. The [A-package verification record](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
contains a completed workspace run: the library passed, but the official-source
compatibility target failed. Earlier OOM/timeout runs remain historical, not
the latest result. No partial or failed run establishes full-suite success.

Eight report-only workloads have moved out of the default test set into the
explicit, supervised `isabelle-scale-hol` entry point (the former six plus
Tier 2/3, not all available scale modes). The Tier 2 active file sequence,
per-file deadlines, adaptive `AUTO_LIMIT`, and Tier 3's complete 30-file
sequence without a new per-file budget are preserved. The core 125-theorem
assertions, global HOL database, existing functional/trust contracts, and
official nine-file no-`SyntaxError` compatibility assertions remain tests.
A regression pass does not imply that separate diagnostics completed; even a
completed statistical diagnostic is not a full theory build or proof result.

`strict`, `core` and `docs` remain focused gates. `verify` and the standalone
`lint` command use strict workspace all-targets Clippy; neither replaces the independent
security/global checks. Current results and dated failures are recorded in
[PROJECT_STATUS.md](../status/PROJECT_STATUS.md).

## Experimental LSP and Document Checks

Run `cargo +stable run --locked --bin isabelle-rs -- --lsp` for the existing
partial JSON-RPC/LSP adapter. It accepts full-document sync only. A valid
`didOpen`/`didChange` installs the new text and revokes the old check before
the bounded worker tokenizes and checks that revision; only the current
open lifetime and generation may publish diagnostics. A rejected update
invalidates the old revision without retaining over-limit text; a later
valid full sync restores checking. Unopened document queries return null
instead of reading arbitrary disk paths on the protocol thread. Pending
proof goals and diagnostics do not represent a completed proof.

The adapter caps a document at 1 MiB, open documents at 64 and 16 MiB
combined, URI length at 4 KiB, each queued check at 4096 commands and
1024 diagnostics / 1 MiB diagnostic message text, and committed snapshots
at 8192 across the workspace. Exceeding a check budget publishes an explicit
`document-check-unavailable` diagnostic with no partial proof state. The
document-symbol endpoint rejects inputs above 8192 lines rather than building
an unbounded symbol response. Incoming messages, outgoing responses, and
CPU checks/definition lookups share bounded queues and one CPU worker. A
definition request for an open document completes with a location or null.
Replacing, invalidating, or closing its revision (or shutting down) cancels it
with `-32800` without waiting for a queued lookup to start. Reusing an
outstanding request ID cancels the original and yields one `-32600` error.
Queue rejection is surfaced as a diagnostic for accepted document updates
or an error for a rejected definition lookup.

The tokenizer retains at most 4096 names and 64 KiB of name text in its
per-thread symbol cache; novel names longer than 1 KiB bypass the cache.
Dropping an old revision releases uncached symbols. Cache quotas do not
limit the memory used by a running command.

Built-in LSP checks and definition lookups use one supervised, reusable
`--compute-worker` child rather than executing legacy search on the protocol
process. The executable must be supplied explicitly when embedding
`IsabelleServer`; the CLI passes its own binary. An embedded Session using
the built-in `RealExecutor` must call `Session::new_with_worker` with a trusted
worker executable; `Session::new` accepts only cooperative custom executors.
Checks transfer diagnostic and proof-state display data, not accepted theorem
authority. IPC rejects source over 1 MiB and responses over 8 MiB; a Session
caller may still allocate source content before this limit is checked. Shared
proof-state snapshots serialize without a pre-cap deep copy. Cancellation,
document close, and shutdown terminate and reap the direct child; reaping
failure is reported, not treated as successful shutdown. Session preserves
cleanup errors across cancelled replies and shutdown join timeouts, and records
worker-side failures even after the owner detaches. A fatal LSP compute-worker
failure terminates accepted pending definition requests with errors before exit.
A timed-out Session check cannot leave an observable successful proof state;
another valid check may recover the document.

An uncooperative custom executor still cannot be preempted mid-operation.
The supervised child inherits credentials, environment, and filesystem access,
and has no OS RSS limit, per-check CPU budget, or process-tree guarantee.
Startup hashing and the first Session check share a 10-second caller timeout;
there is no hard per-check wall-time limit for running LSP checks. Production
HOL load progress and adapter logs use a bounded best-effort, non-blocking
tracing sink when stderr stalls; source text and request IDs are not logged
in full, and the last log may be lost at exit. This adapter does not authorize
accepted theorems or implement the planned ISIP runtime.

## Documentation-Only Changes

Inventory root entrypoints, `docs/`, `.claude/`, workflow configuration and
classified `scripts/` documentation. Check each affected claim against its
source owner; keep accurate files unchanged rather than churning every date.
Synchronize bilingual summaries, current commands, configuration metadata and
reader links. Preserve historical results with their original commands and
scope, but identify obsolete entrypoints as historical.

Classify embedded code before moving it: short command invocations and
explanatory API/configuration examples may stay; reusable orchestration belongs
in the existing Rust `xtask` implementation, not a second script. The
[documentation checks and script ownership](../../scripts/README.md#documentation-checks-and-script-ownership)
section defines the current checks' limits. Review heading anchors and
frontmatter separately; the link gate checks local target existence only.

Run `cargo +stable xtask docs` after edits, then the full global validator.
Parse changed configuration and smoke affected command entrypoints. Report
inherited failures without changing product behavior in a documentation task.
Do not claim that a harness loaded merely because configuration parsed or its
hook command ran directly.

## Documentation And Templates

Markdown may contain short explanatory Rust, TOML, JSON and command examples
when they clarify a local contract. Do not maintain large runnable or
duplicated scripts in documentation.

Put all maintained automation in [xtask/](../../xtask/); `scripts/` retains
only official reference probe inputs and
[classified design/configuration skeletons](../../scripts/templates/README.md).
`cargo +stable xtask templates` proves only standalone compilation of the
classified Rust design files, not production API compatibility, architecture,
theorem semantics, or trust.

## Trusted-Kernel Change Rules

When touching the strict kernel in `crates/kernel/src/**` (re-exported from
`src/kernel/mod.rs`), or legacy `src/core/**` trust-boundary code, follow this
workflow; the strict kernel does not depend on legacy core:

1. Read [KERNEL_RULES.md](../kernel/KERNEL_RULES.md) and the
   [acceptance inventory](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).
2. Preserve explicit declarations, exact-owner replay, authorized dependencies
   and the sole `accept_closed_theorem` token constructor in `isabelle-kernel`.
   It has no `admit`, dummy certification or fallback `assume`.
3. Preserve legacy `src/core` burdens (`hyps`, `tpairs`, `shyps`, `oracles`).
   Strict-kernel replay must also preserve and validate its complete
   H/S/C/F/pending/mode payload; clearing one obligation does not clear others.
   Diagnostic `admitted:*` results remain untrusted and cannot complete a
   checked source proof or authorize a strict token.
4. Never use `assume` for proof failure, unsupported commands, stubs or
   non-derivational transformations.
5. Add or update positive and rejection/attack evidence, obtain independent
   review, then run `cargo +stable xtask strict` and the other affected gates.

## Theorem Status Vocabulary

Use these terms consistently:

| Term | Meaning |
|---|---|
| oracle-free | `thm.is_fully_proved()`; no oracle footprint. |
| closed proved shape | no oracle, no hypotheses, no unresolved `tpairs`; use `thm.is_closed_proved()` for shape only. |
| transitional strict closed | legacy strict construction plus closed proved shape and no dummy types; use `thm.is_strict_closed_proved()` for migration classification only. |
| kernel-trusted closed | `isabelle_kernel::TrustedTheorem` (re-exported at `isabelle_rs::kernel`) over replayed closed `CProp : prop` with an exact immutable owner and authorized dependencies; sampled `HOL::TrueI` alone contributes to `1/125`. |
| open theorem | valid theorem with hypotheses, such as `A |- A`. |
| admitted theorem | legacy theorem-shaped value with explicit unproved oracle footprint; not an accepted strict token. |
| searchable fact | fact available to proof search; may be open or admitted. |
| trusted theorem table | final new-kernel `TrustedTheory`; accepts only context-bound `isabelle_kernel::TrustedTheorem` values, never a legacy classifier result. |

## Proof Replay Development

The legacy `src/core/proofterm.rs` compatibility replay supports six base
Pure rules:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

The former legacy `hol_object_refl` and `true_def_transport` bridges were
removed during the source-backed cutover; do not add them back as shortcuts.

The separate `isabelle_kernel::Derivation` inventory is listed in
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).
Every current variant has an exact-context replay arm; this does not grant
legacy theorems strict-kernel authority.

When changing replay, keep the two paths distinct:

1. Strict replay must recertify under the exact owner, validate rule side
   conditions and authorized dependencies, and compare the reconstructed
   result. Never reconstruct proof authority from frontend metadata.
2. Legacy replay mirrors the corresponding `ThmKernel` side conditions and
   compares reconstructed `prop`, `hyps`, `tpairs` and `oracles`; make
   oracle/admitted premise behavior explicit.
3. Add positive and tampering tests; update
   [KERNEL_RULES.md](../kernel/KERNEL_RULES.md) and
   [KERNEL_ATTACK_TESTS.md](../kernel/KERNEL_ATTACK_TESTS.md).

`ProofBody::check(expected_prop)` is proposition-only compatibility code. Do not
use it as a trusted theorem replay gate. Use `Thm::check_proof()` or
`Thm::validate_proof()`.

## Agent Harness And Review

Repository rules are harness-neutral. `.claude/` provides local routing and
metadata, not another source of theorem authority. Apply the
[engineering workflow](#engineering-workflow) regardless of harness; model
agreement and stored memory are not proof evidence. A parsed configuration is
not evidence that Claude Code or another harness loaded or enforced it.

TCB and other trust-sensitive changes require independent review. Source,
tests, accepted ADRs and observed verification output remain authoritative.
Apply the [cross-harness data boundary](../../AGENTS.md#cross-harness-data-handoffs):
review delegation does not authorize a new external provider or unrestricted
context transfer. Use only the necessary, authorized and redacted material.

Do not create commits, rebase, rewrite history, or push without explicit user
instruction.

## Files Not To Touch Accidentally

Do not modify these unless explicitly in scope:

```text
Cargo.lock
isabelle-source
```

An intentional lockfile update needs a dependency or security rationale and
locked verification. A successful `cargo metadata --locked` proves that the
lockfile is usable, not that an unexplained refresh belongs in the change.
Keep dependency/vendor changes separate from parser, trust, metrics, tests, and
documentation work. Preserve unrelated dirty work.

## Current Engineering Priorities

1. Preserve explicit strict signature type declarations, axiom-schema
   validation before installation, monomorphic definitions, and exact-owner
   acceptance in `crates/kernel`.
2. Keep the independent source-backed `TrueI` and Pure identity
   (`!!P::prop. PROP P ==> PROP P`, `by assumption`) fixture paths distinct
   from the bundled sampler. Only sampled `HOL::TrueI` reaches acceptance via
   audited source projection, basis, definition, Pure transport, and owner
   replay; neither fixture adds to its `1/125` count.
3. Keep full-source legacy loading fail-closed for unsupported commands,
   malformed proofs, and unresolved imports; do not promote legacy Strict
   or search facts to `KernelTrustedClosed`.
4. Keep the all-Rust automation cutover distinct from full-project acceptance.
   Preserve B's historical reference evidence; only offline comparison is
   available under the JVM-free policy. Native P2/P3/P4 work has resumed under
   the approved P1 design. The Rust THM consumers and ML repairs have scoped
   evidence, not complete ML THM/ROOT/HOL acceptance. Consult the
   [current delivery record](../status/PROJECT_STATUS.md#current-delivery-state)
   before selecting follow-on work; do not bypass its solver cleanup blocker.
5. Follow [ROADMAP.md](../status/ROADMAP.md#approved-native-compatibility-program)
   for the A–H native compatibility program. Later proof migrations require
   their own reviewed source/owner/replay contracts; neither one sampled token
   nor this documentation workflow authorizes broader HOL or ISIP runtime work.
