# Isabelle-rs Agent Guide

This file is the versioned, harness-neutral entry point for coding agents working
in this repository. Oh My Pi, Codex, Claude Code, and other tools must apply the
same trust boundary. A stronger harness or model does not make a theorem more
trusted.

## Authority Order

Resolve conflicts in this order:

1. source code and tests in the current checkout;
2. `docs/PROJECT_STATUS.md` and `docs/TRUST.md`;
3. accepted ADRs and trusted-boundary design documents;
4. `docs/ROADMAP.md` and other current repository documentation;
5. `.claude/`, `~/.codex/`, agent memory, and archived session notes.

Always obtain repository state from a fresh status/log inspection. Documentation
must not freeze a clean-worktree claim or assume that an unpublished commit is
still present.

## Project Position

Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired LCF
kernel. It is not a full Rust rewrite of Isabelle and does not have
Isabelle/HOL, Isar, PIDE, or AFP feature parity.

Current sampled trust metrics:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

`HOL::TrueI` is a legacy `core::Thm + ThmTrust::Strict` migration experiment.
Its stored proposition is bool-valued `HOL.True`, not
`HOL.Trueprop HOL.True : prop`; it is not a new-kernel trusted HOL theorem.

`KernelTrustedClosed` is now a mutually exclusive `ProofOutcome` backed by a
real accepted token, and `ProofOutcomeStats::total()` includes it. The
production HOL verifier cannot produce that token yet, so the sampled count
remains zero.

## Two-Kernel Boundary

```text
src/kernel/  candidate target TCB nucleus
src/core/    legacy quarantine and migration source
```

For `src/kernel/`:

- no dummy type or compatibility certification;
- no `admit`, fallback `assume`, or theorem construction from failed search;
- no dependency on `core`, Isar, HOL, tools, theory/session, LSP, server, WASM,
  or compute backends;
- undeclared constants and local frees are rejected;
- `ProofObligation` and `SearchFact` are not theorems;
- unchecked certified-term and theorem constructors remain
  `pub(in crate::kernel)` or narrower;
- every trusted rule requires explicit side conditions, replay, and attack tests.
- `accept_closed_theorem` is the only trusted-token constructor; it owns exact
  owner replay, recursive recertification, dependency reconstruction, duplicate
  rejection, and immutable accepted-fact insertion;
- ancestor theorem reuse requires `KernelRules::theorem_ref`; replay checks the
  exact sealed token (`id`, `name`, and `accepted_in`) in owner ancestry before
  recording its logical `TheoremId` dependency;
- a canonical `DependencySet` is theorem identity data, never proof authority.

For `src/core/`:

- do not add new trusted HOL proof power;
- changes are limited to bug fixes, boundary hardening, diagnostics, and explicit
  migration adapters;
- compatibility constructors and `Typ::dummy()` remain debt, not precedents;
- `is_strict_closed_proved()` authorizes only
  `TransitionalStrictClosed` reporting.

`HolTheoremDb` and other search indexes may contain open, admitted, generated,
compatibility, and transitional facts. They are not trusted theorem tables.

## Current Trusted Main Line

The implementation order is strict:

1. keep the implemented immutable `SignatureId` / `TheoryId` propagation and
   exact mixed-context rejection stable;
2. keep the implemented context/dependency-aware acceptance API and mutually
   exclusive `KernelTrustedClosed` outcome stable;
3. keep the implemented data-only source proposition AST semantically
   unresolved: `SourceName` and `SourceSyntax` retain exact spellings,
   `SourceSpan` is half-open diagnostic metadata, and no trusted context or
   conversion into kernel values exists;
4. next, integrate source parsing and elaborate checked judgments, constants,
   and polymorphic type schemes, including `HOL.Trueprop`, into `CProp : prop`;
5. install a data-only HOL logic-basis manifest, validated and replayed by
   generic kernel code;
6. add a generic conservative definition extension;
7. re-derive `HOL::TrueI` as `HOL.Trueprop HOL.True` through the new kernel;
8. only then consider `HOL::trans` as a reuse consumer.

The immediate next implementation change is item 4. The source AST does not
classify dotted names, Pure/HOL binders, constants, frees, variables, or
judgment positions at construction time; a declaration-aware parser/elaborator
must resolve those meanings without adding a direct source-to-theorem path.

Read `docs/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md` before changing this chain.

## Explicit Near-Term Exclusions

Do not implement any of these before the main line reaches a real
`KernelTrustedClosed: 1/125`:

- `HOL::trans`, `hol_subst`, or a second theorem adapter;
- theorem-specific `ThmKernel::hol_*` or `KernelRules::hol_*` constructors;
- general simp/unfolding as a shortcut for `TrueI`;
- promotion of `hol_object_refl` or `true_def_transport` into the final TCB;
- broad HOL/Isar command coverage, workspace split, APP, LSP, WASM, or PIDE work;
- Burn, CubeCL, GPU, or multi-backend dependencies in the kernel.

Source-shape metadata is a transitional fail-closed guard only. It is not name
resolution, checked elaboration, or trusted provenance.

## Agent and Review Workflow

Use a hybrid workflow where useful:

- Oh My Pi may be the primary harness for long-lived context, LSP, structured
  edits, independent worktrees, and read-only audit fan-out.
- Codex-compatible models or CLI sessions remain useful for bounded
  implementation slices, adversarial review, and independent reproduction.
- High-risk TCB changes should not rely on the implementer as the only reviewer.
- Parallel agents may inspect independent areas, but shared TCB contracts are
  decided before parallel edits. Use isolated worktrees for independent edits.
- The parent agent fixes shared interfaces and invariants before delegation,
  then fans out genuinely independent slices in one batch; do not serialize a
  lone subagent while the parent waits idle.
- Parallel workers must not edit the same trust-sensitive files. Give each
  worker explicit paths and acceptance criteria, and use isolated worktrees for
  independent write tasks.
- Workers run only focused checks for their slice. The parent integrates the
  results and runs each repository-wide verification gate once.
- Repository code, tests, and ADRs remain authoritative over harness memory.

Never commit, amend, rebase, push, or rewrite history automatically unless the
user explicitly requests it. Preserve unrelated work and report dirty state.

## Dependency and Commit Hygiene

`Cargo.lock` and `isabelle-source` are never incidental changes.

- Modify them only when explicitly in scope.
- A lock-only dependency refresh needs an explicit dependency/security rationale
  and must pass locked metadata/build checks.
- If no manifest or intentional dependency update explains lockfile drift, drop
  it rather than mixing it into trust-boundary work.
- Keep dependency/vendor changes separate from kernel, parser, metrics, tests,
  and documentation commits.

For trusted-boundary work, prefer reviewable responsibility splits:

1. parser/dispatcher boundary hardening;
2. outcome model and reporting;
3. attack/regression tests;
4. architecture, status, and agent documentation.

## Documentation and Templates

Short explanatory Bash, Rust, PowerShell, TOML, and JSON fenced blocks are
allowed when they clarify a local contract. Do not duplicate or maintain large
runnable scripts in Markdown.

- reusable commands and full scripts live in `scripts/`;
- reusable design/configuration examples live in `scripts/templates/`;
- every template is classified in `scripts/templates/README.md`;
- standalone template compilation proves only local syntactic/type
  self-consistency, not compatibility with the production project API;
- `scripts/check-markdown-snippets.sh` enforces size and duplication limits, not
  semantic correctness.

Update code, tests, trust/status docs, ADRs, and agent guidance together when a
trusted boundary changes. Historical snapshots and changelog entries should be
marked historical rather than rewritten as current status.

## Verification

Use repository-owned entry points:

- docs or agent guidance: `scripts/dev-check.sh docs`;
- kernel, theorem acceptance, replay, or trust semantics:
  `scripts/dev-check.sh strict`;
- sampled HOL snapshot: `scripts/dev-check.sh core`;
- broader theory claims: the appropriate `tier2`, `tier3`, or `broad` mode.

For the current main line, also run the focused wrong-context and deterministic
identity tests introduced by the slice. Report exact observed outputs. Do not
claim full `cargo test --lib` success unless the stack-sensitive theory-loader
batch is proven fixed in the current checkout.

`cargo +stable check --locked --all-targets` has four known pre-existing
benchmark compile errors on `origin/dev`; see `docs/BASELINE.md`. Report that
gate separately rather than claiming it passed.
