# Automation and reference inputs

All maintained project automation, audits, installation, supervision, and script
tests live in Rust [xtask](../xtask/). This directory retains only official
reference probe inputs and classified [design templates](templates/); nothing
here is a runnable project script. Short explanatory snippets may remain beside
their contract; do not duplicate runnable orchestration in Markdown.

Isabelle-rs remains a Rust research prototype of an Isabelle/Pure-inspired LCF
kernel. See [PROJECT_STATUS.md](../docs/status/PROJECT_STATUS.md) for current trust and
completion status.

## Verification

From an existing checkout with Rust/Cargo installed, use
`cargo +stable xtask` as the canonical command entry point (`+stable` requires
rustup's stable toolchain). `cargo xtask` can inherit a compatible caller
toolchain. Leaf Cargo commands do not install or upgrade Rust; `help` does not
build the product. See [xtask source](../xtask/src/) for implementation.

| Command | Purpose |
|---|---|
| `help` | Command and prerequisite catalog; no product build. |
| `build [--release]` | Locked root product build; no install or release. |
| `check [--all-targets]` | Locked root product compilation. |
| `fmt` / `lint` | Read-only workspace formatting / locked workspace all-targets Clippy with `-D warnings`. |
| `fast` | Workspace formatting and locked root check, aggregating failures. |
| `verify` | Complete repository matrix: pinned-source identity/cleanliness, fmt, strict workspace all-targets Clippy, locked workspace all-targets check, zero-warning kernel check, documentation checks, firewall and workspace tests. Aggregates independent failures; no Tier/reference runs or security scans. |
| `strict` | Kernel zero-warning check, firewall, declaration/context/replay attack suites, crate unit/doctests, and legacy-core checks (also fmt/check). |
| `checkpoint` | `strict` plus focused feature tests, all locked. |
| `core` | Exact 125-theorem sampled run; not the independent strict source fixtures. |
| `lib` | Stack-sensitive root library tests; only report success on completion. |
| `docs` | Markdown snippets, local links, standalone Rust templates, fmt/check. |
| `links` / `snippets` / `templates` | Individually run the three documentation checks aggregated by `docs`. |
| `firewall` / `compat` | Kernel dependency/visibility boundary and legacy compatibility-callsite audit. |
| `pinned-source` | Require the fixed Isabelle2025 HEAD, clean checkout, matching index Gitlink and required source files; source inspection only, no official runtime launch. |
| `fix <check\|apply>` | Inspect fixes without mutation, or explicitly apply Rust fixes to this checkout; review changes before `apply`. |
| `install [--release] [--check] [--dir PATH]` | Locked local check/build from an existing checkout; outputs stay in Cargo's target directory. No clone, pull, toolchain upgrade, or PATH installation. |
| `package --artifacts PATH` | Package existing release binaries plus `LICENSE`, `NOTICE` and `THIRD_PARTY_LICENSES` into tar/zip archives without publishing. |
| `hook <pre-edit\|post-edit>` | Native path/doc-sync reminders for configured editor hooks; reads the existing path environment variable, never edits sources or commits. |
| `profile` | Linux-only single-lemma diagnostic through the same supervisor. |
| `supervise --worker PATH ...` | Direct bounded Linux diagnostic with an explicitly selected worker; `profile`/Tier commands select their worker from Cargo artifacts. |
| `broad` | `core`, `tier2`, `tier3`, aggregating independent failures. |
| `reference prepare` / `reference build` / `reference inventory` | Disabled by the JVM-free policy before workspace access or process creation. Retained source and historical records are not runnable instructions. |
| `reference compare --rust-report PATH --reference-run PATH` | Structural diagnostic comparison against a selected official run; missing required P0 evidence blocks full acceptance, not theorem proof. |
| `all` | `docs`, `strict`, `core`, `tier2`, `tier3`; **not** the full quality gate. |
| `test` | Full workspace tests with `--no-fail-fast`; root-only selectors `--lib [FILTER]`, `--test TARGET`, or `--doc`; optional `-- --ignored`. |
| `selftest` | Independent xtask tests, explicitly run by CI. |
| `rustdoc` | Locked documentation without dependencies, including private items. |
| `audit` / `audit rustsec` | Aggregate required Cargo audit/deny, or run RustSec alone. Tools must already be installed. |
| `version-check --tag TAG` | Cross-platform metadata check: tag must equal `v` plus root package version. |
| `release-check --tag TAG` | Version-check, then `verify`; mismatch blocks gates, never creates a tag or release. |

`package` embeds these legal texts from the checkout used to build xtask, not
from the downloaded artifact directories. Rebuild xtask after changing them.
Notices are non-executable archive entries. They cover project licensing and
the identified Isabelle materials, not a complete dependency notice inventory;
redistributors must also supply notices for their actual build dependencies.

Workspace members are the root product, `isabelle-kernel`, `isabelle-evidence`,
and `xtask`; `default-members` remains root-only. The evidence crate validates
offline comparison data, not theorems. Bare `cargo test` is not a workspace gate.
Use `cargo +stable xtask selftest` and `cargo +stable xtask test` explicitly.
`selftest` does not build or depend on the product/kernel. The real-product
supervision regressions remain in `cargo +stable xtask test --test hol_profile_supervisor`;
they are separate from the product-independent supervisor contract tests.

Every step reports its actual success, exit failure, signal, startup failure,
or dependency block. Independent gates continue; failed builds cannot launch
stale workers. Exit 0 means the requested steps passed, 2 means invalid
arguments, and 1 means operational failure; child exit status is also reported.

For `tier2` / `tier3`, defaults remain 600 seconds and 4096 MiB per process,
overridable with `HOL_DIAGNOSTIC_TIMEOUT_SECS` / `HOL_DIAGNOSTIC_MEMORY_MIB`.
Each uses a fresh output directory; inspect `stderr.log` and
`supervisor.json`. The wall budget covers the worker, not its build.
Worker paths come from the successful Cargo `compiler-artifact.executable`,
including custom `CARGO_TARGET_DIR`; they are never guessed from `target/debug`.

`profile` requires `--source-root PATH --theory NAME --lemma NAME --output-dir PATH`.
It also accepts `--context-root`, `--manifest-in`, `--auto-limit`,
`--timeout-secs`, and `--memory-mib`; it does not accept `--worker`.
Relative input/output paths resolve from the caller's directory. Output must
be fresh. A diagnostic `completed` does not mean an accepted proof.

Build/check/install/version-check need no Bash on macOS/Windows. Documentation,
firewall and compatibility checks run in Rust; template compilation uses
installed Rust tools. Linux diagnostics retain their system prerequisites.
Missing tools are errors, not skips.
Killing only the Cargo/xtask parent PID does **not** guarantee cascading
cancellation; no new process-tree sandbox or cross-platform cancellation is
claimed.

Follow the [engineering workflow](../docs/guides/DEVELOPMENT.md#engineering-workflow):
behavior proof, applicable project gates, then the full workstation
`~/.omp/agent/validate.sh` (secrets, format, lint, type/build, dependency audit,
tests). `--quick` is not delivery evidence. `verify` and CI use strict workspace
all-targets Clippy; the workstation security/global gates remain independent.
The [A-package evidence](../docs/status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
is historical; current results belong in [Project Status](../docs/status/PROJECT_STATUS.md#current-delivery-state).

### Isolated Isabelle2025 reference

Local `reference prepare`, `build`, and `inventory` are disabled before any
workspace access or launcher invocation under the JVM-free policy. The
following workspace/build/inventory details describe **historical** reference
evidence only; they are not instructions for a new local run. Existing
reference source, frozen observations, and code are preserved, but neither a
historical successful run nor a self-reported producer authorizes current
official compatibility.

For an independently supplied, approved offline package, use
`cargo +stable xtask reference compare --rust-report PATH --reference-run PATH --reference-manifest PATH --reference-approval PATH`.
The caller selects an external approval file outside the imported package;
it must bind the fixed source bytes, manifest digest, independent producer,
build/inventory runs, and execution/drain receipt. The native report must have
`purpose=native_build_result`. Missing approval, execution coverage, or one
of six required observations blocks full compatibility; the report cannot
grant a Rust theorem token. No current complete approved package is available.

#### Historical reference workspace (not executable locally)
The historical implementation accepted `--workspace PATH` outside the repository
and fixed source checkout. Its default was
`$XDG_CACHE_HOME/isabelle-rs/reference/Isabelle2025-765fb2460a57`, or the same
suffix under `$HOME/.cache`. `prepare` alone accepted `--source-root PATH`;
its default was the repository's `isabelle-source` checkout. Paths supplied to
the current offline comparison command resolve from the invocation directory.

The earlier reference work ran `prepare`, then `build`, then
`inventory --build-run PATH`, using the exact successful run directory. It
reconstructed Pure and HOL rather than reusing an existing heap. The
inventory validated startup configuration, file bytes/modes, and the build
database's `PIDE/files` source mapping. Those runs are historical evidence,
not a current command sequence or native trust acceptance.

Without a new externally approved package, `reference compare` can still
read the frozen v1 observations as diagnostics; incomplete fields remain
`Incomplete` rather than being filled with inferred values.

The namespace has a clean environment, private HOME and temporary files,
no network, and read-only fixed sources/components. Inventory inputs are
read-only; its output and temporary directory are separate. `XDG_CACHE_HOME`
points into the current temporary directory so generated font caches do not
become reusable heap inputs. These controls are not a guarantee against a
malicious same-UID process replacing host paths concurrently.

Each run prints its artifact directory. Inspect `result.json`, `stdout.log`,
`stderr.log`, `command.json`, and `events.jsonl`; inventory additionally writes
raw YXML and decoded JSON. Only selected executable/resource path observations
and syscall outcomes enter `events.jsonl`, not traced argument vectors or
environment values. A returned file-descriptor path can resolve a relative
`open`/`openat` observation; unresolved paths remain explicit and are not
credited as fixed-source inputs.
The Rust supervisor's execution deadline is 7200 seconds, followed by
TERM/KILL cleanup on timeout or interruption; killing only its Cargo/xtask
parent still does not guarantee cascading cancellation.

Inventory writes six distinct JSON artifacts:

| Artifact | Evidence |
|---|---|
| `inventory.json` | Structured declarations, named static facts, hypotheses/sort burdens, theorem dependencies and oracle registrations/footprints |
| `execution.json` | Completed source command spans and official-parser file-input bindings for the nine roots' closure, excluding the observer |
| `axiom-provenance.json` | Official axiom-table records classified by source and declaration associations, never Rust authorization |
| `profile.json` | Imports graph, occurrence-backed command requirements, ML file bindings and selected build/inventory file/process observations |
| `interfaces.json` | Checked command registry and selected public ML declarations per context, with a separate bootstrap namespace |
| `bootstrap.json` | Source-declared ROOT0/ROOT load order bound to build-time file reads, plus audited startup-prelude sources |

The frozen [reference snapshot](../tests/fixtures/isabelle2025/closure.json)
indexes those hash-bound artifacts and records exact source identities, roots,
command requirements, public symbol names and static fact-group indexes.
Full propositions, API type displays and command occurrences remain in the
run directory, not in the summary fixture. Preserve that directory when
retaining the baseline; reruns produce new directories and may have different
runtime serials/hashes. The snapshot is not yet a native loader input format.

The observed import closure has 67 theories; 66 non-Pure target theories
execute in a `Reference_Execution = Pure +` session. `sessions HOL` provides
resource metadata, not an inherited HOL heap. Public namespace declarations
can use current global fallback and do not prove historical per-theory
namespace state or actual calls. Bootstrap load statements/file reads are not
a complete nested ML execution trace. Anonymous intermediate facts and
dynamic fact evaluations remain outside the static export.
The fact `owner` is the certificate context after `Thm.transfer`, not its
derivation origin. Internal sort constraints and the complete axiom/extension
dependency closure are not exported; named-theorem dependencies are a narrower
observation. A later differential must retain these gaps explicitly.

Oracle registration is not oracle use. The official axiom table includes
definitions and conditional type extensions, not just initial logic axioms.
Actual `veriT` executions are reference observations, not production process
permissions; any native solver result still needs Rust-checked reconstruction.
Reference success does not complete native Rust closure acceptance, resolve
the full-project quality blockers or change the separate sampled `1/125`.

### Documentation checks and script ownership

| Check | Scope | Not established |
|---|---|---|
| `snippets` | Length and exact-body duplication for backtick blocks labelled bash, sh, shell, powershell, rust, toml or json; excludes `.git`, `target` and `isabelle-source`. | General Markdown parsing, tilde/other-language fence coverage, script safety or successful execution. |
| `links` | Existence of local inline Markdown link targets. | Heading anchors, external URLs or factual accuracy. |
| `templates` | Classification header, read-only formatting and standalone compilation of the classified Rust files. | Production API compatibility or theorem authority. |
| `docs` | These three checks plus workspace format and root compilation. | Complete repository, security or global validation. |

Review anchors, frontmatter and the actual reader route separately.
Before extracting a Markdown block, distinguish executable orchestration from
short invocations, explanatory API/configuration examples and dated output.
Reuse an existing `xtask` command where possible; move real reusable logic and
its behavior tests into `xtask/`, update every caller, and remove the obsolete
embedded implementation. Do not port upstream observer ML or turn design
templates into production code merely to make the directory all-Rust.

`strict` includes the kernel `firewall`; `compat` inventories legacy
compatibility constructors and certification calls. `fix check` is read-only;
`fix apply` is explicitly mutating. `selftest` runs the automation contract
tests. These commands neither grant theorem authority nor authorize mutation
or publication beyond the current task.

## Execution

- Research demo: `cargo +stable run --locked --bin isabelle-rs`.
- Experimental LSP server: `cargo +stable run --locked --bin isabelle-rs -- --lsp`.
- Narrow fail-closed source compiler:
  `cargo +stable run --locked --bin isabelle-build -- tests/fixtures/TrustedTrueI.thy`.
  Replace the path with `tests/fixtures/TrustedPureIdentity.thy` for the Pure fixture.

`isabelle-build` accepts only its supported source-backed `HOL.TrueI` or
Pure identity (`!!P::prop. PROP P ==> PROP P`, `by assumption`) forms and prints
`KernelTrustedClosed` on a successful build; unsupported source fails with a
nonzero exit. These independent fixtures are not sampled 125 results. This
launch path does not claim a general Isabelle/HOL compiler or official
Isabelle runtime differential verification.

## Bounded HOL Diagnostics

The preferred single-lemma entry builds and selects the worker from the
successful Cargo artifact before invoking the supervisor:

```bash
cargo +stable xtask profile --source-root isabelle-source/src/HOL \
  --context-root theories --theory HOL --lemma TrueI \
  --timeout-secs 120 --memory-mib 4096 --output-dir /tmp/isabelle-hol-diagnostic
```

The output directory must not exist. The supervisor creates it with restricted
permissions and keeps `events.jsonl`, `stderr.log`, `timeout.log`,
`supervisor.json`, and the first run's `manifest.json`. Replay with the same
roots, theory and lemma, `--manifest-in
/tmp/isabelle-hol-diagnostic/manifest.json`, and a **new** output directory.
`--auto-limit` defaults to 100 on creation; replay rejects a conflicting limit.
For direct supervisor use, build `isabelle-profile-hol` separately and pass
its verified executable to `cargo +stable xtask supervise --worker PATH ...`.
`profile` instead selects the actual Cargo artifact and accepts no `--worker`
override. Both routes preserve the same supervision semantics.

The manifest freezes the actual first-at-most-200 source load order and the
complete bootstrap context, including duplicate-theory selections, paths,
hashes, and work/stack budgets. It does not recreate an unrecorded historical
HashMap order. Bootstrap, loading, builtins, target parsing, search, and
classification emit separate flushed events. Replaying changed or missing
inputs fails rather than using an ambient context fallback.

The Linux supervisor requires user/PID namespaces and the system tools needed
for namespace/process supervision. INT/TERM cancellation is handled during
startup as well as execution; normal exit, timeout, and cancellation reap
remaining descendants. Nonzero exits are never completion.
Supervisor `completed` means the diagnostic finished, **not** that its theorem
was proved. Only the result event's existing outcome class describes proof
status; this entry point adds no theorem authority.

This is not a filesystem/network permission sandbox. CPU/address-space
limits are per process and output limits are per file (8 MiB), not aggregate
tree quotas. The Rust wall-clock budget starts after the namespace launcher
has spawned, covering subsequent startup, loading and computation. Product
compilation, dependency probes and a blocked spawn before it returns are not
covered. SIGKILL, host failure, malicious same-UID processes, and
attacker-replaceable output parent directories are outside the cleanup/integrity guarantee. A timed-out
diagnostic identifies the last stage but proves neither a performance fix
nor a passing full suite.

### Report-only Scale Workloads

Eight report-only workloads formerly registered as default tests now run
through `isabelle-scale-hol` (six earlier migrations plus `tier2` and `tier3`;
these are not all available scale modes). `cargo +stable xtask tier2` and
`cargo +stable xtask tier3` build/select their workers and run those modes.
For a different mode, explicitly build the worker and pass that binary to the
native Rust supervisor (verify the actual output path; do not guess when using
`CARGO_TARGET_DIR`):

```text
cargo +stable build --locked --bin isabelle-scale-hol
cargo +stable xtask supervise --worker PATH --scale-mode structured-proofs --timeout-secs 30 --memory-mib 2048 --output-dir /tmp/isabelle-structured-proofs
```

| Mode | Preserved workload |
|---|---|
| `structured-proofs` | Global HOL database; original three structured proofs from each bundled HOL/Orderings/Nat/Set/List file. |
| `verify-batch-first-five` | Original scanner order, first five `theories/HOL` files, all their proof-bearing lemmas and local databases. |
| `verify-list-sample` | Original first ten proof-bearing List lemmas and automatic search-limit policy. |
| `verify-nat-sample` | Original first 35 proof-bearing Nat lemmas and automatic search-limit policy. |
| `verify-induction-sample` | Original four named List induction attempts and local database. |
| `analyze-failures` | Full `isabelle-source/src/HOL` SessionBuilder classification and top-ten failure report. |
| `tier2` | All originally active Tier 2 `theories/HOL` paths, including Library entries, in their original order; original 60/90/120-second per-file soft deadlines and lemma-count-based `AUTO_LIMIT` (5/10/20/30); proved vs axiom-accepted counts, missing/read-error diagnostics and totals retained. |
| `tier3` | All original 30 Tier 3 `theories/HOL` paths in order, with original local verification and aggregate statistics; no new per-file deadline or `AUTO_LIMIT`. Missing/read-error diagnostics are retained. |

Other scale modes are also selectable. Scale and single-lemma/manifest
arguments are mutually exclusive. Runtime source paths are relative to the
calling directory; normally run from the repository root. List/Nat/induction
samples use embedded sources and do not need a runtime source tree. Tier 2/3
continue past missing/unreadable files; processing none is an input error.
The worker uses the same 256 MiB stack as the legacy test workloads.

Scale output is primarily `stderr.log`; it does not emit the single-lemma
worker's manifest or structured stage-event protocol. `supervisor.json` records
the chosen `scale_mode`, exit classification and resource budgets. These runs
retain the shared timeout, cancellation, namespace-reaping and per-process
resource boundaries above. They are not manifest-pinned reproductions of an
unrecorded historical scan order.

No `#[ignore]` was added. The default regression suite still includes the
assertion-backed 125-theorem sampler, global HOL database and other functional/
trust contracts, plus the nine official HOL file compatibility assertions
(no `SyntaxError`). It no longer runs the Tier 2/3 statistical workloads.
Report regression results separately from these eight diagnostics. A
diagnostic `completed` means statistics finished, not that theory compilation
or any proof succeeded; timeout is incomplete, never a passing test.


## Installation

Install Rust/Cargo and obtain a local checkout first (Git clone is a separate
user action). Run `cargo +stable xtask install` here; use `--release` for an
optimized build, `--check` to check instead of building, or `--dir PATH` to
select an existing checkout to build/check. Outputs remain in Cargo's target
directory; no binary is copied onto PATH. No curl-to-shell or PowerShell remote
installer is supported; xtask neither installs/upgrades Rust nor
clones/pulls/fetches the repository.

`xtask` removes inherited `ZSTD_SYS_USE_PKG_CONFIG` and
`ZSTD_SYS_NO_HIDE_SYMBOLS` from its child Cargo commands so the locked Zstd
dependency uses the approved bundled codec rather than a caller-selected
system library. Direct Cargo invocations are not covered by this isolation.

## Releases

CI checks the release tag with `cargo +stable xtask release-check --tag TAG`,
builds locked release binaries, then packages staged artifacts using
`cargo +stable xtask package --artifacts PATH` for the configured hosts.
Packaging is not publishing, tagging, or a full-project validation gate.
It does not publish to crates.io; publication remains a separate explicit action.

`release-check` runs version matching followed by the full repository `verify`
matrix. CI and release workflows separately require gitleaks, Trivy, Cargo
audit and Cargo deny; security failures cannot be waived by a successful build.
Linux verification requires the fixed, clean Isabelle Gitlink; use
`cargo +stable xtask pinned-source` to check its identity and required files
without starting the official runtime.
`all` and `broad` are explicit diagnostics, not implicit publishing
prerequisites. Local official reference execution is disabled.
Historically ignored Rust diagnostics are manual opt-in CI work, never a
substitute for the default regression suite.

CI definitions remain in [ci.yml](../.github/workflows/ci.yml) and
[release.yml](../.github/workflows/release.yml). Triggering publication,
creating a tag or pushing requires explicit authorization. Local success
does not prove macOS/Windows artifacts ran or hosted CI jobs passed; the
complete workstation validator remains a separate delivery requirement.

Lockfile changes are never incidental to these workflows. A lock-only refresh
needs an explicit dependency/security rationale; successful locked checks prove
validity, not intent.

## Templates

Reusable examples and design skeletons live in [templates/](templates/).
Their authoritative classifications and validation limits are in
[templates/README.md](templates/README.md).

Current groups:

- checked HOL proposition, resolution, symbolic-compute, and proof-session Rust
  files: **design-only**;
- future kernel/project TOML manifests: **design-only**;
- APP JSON payloads and Claude/phase Markdown forms: **example**;
- production files in this directory: **none**.

The Rust files deliberately compile as standalone crates. That check catches
local syntax and type errors only. It does not prove that a template matches
the current project API, composes with production modules, preserves kernel
invariants, or defines an accepted architecture.
