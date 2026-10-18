# CLAUDE.md — Isabelle-rs

Claude Code must follow the repository-wide rules in [AGENTS.md](AGENTS.md).
That file is authoritative for every agent harness; this file is only the
Claude-specific compatibility entry point.

## Canonical Reading Order

1. [AGENTS.md](AGENTS.md)
2. [Project status](docs/status/PROJECT_STATUS.md)
3. [Trust model](docs/status/TRUST.md)
4. [Acceptance inventory](docs/kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md)
5. [Roadmap](docs/status/ROADMAP.md)
6. [Kernel rules](docs/kernel/KERNEL_RULES.md)
7. [Attack tests](docs/kernel/KERNEL_ATTACK_TESTS.md)

Source code and tests in the current checkout override stale agent memory,
`.claude/` notes, or user-level `~/.codex` caches.

## Current Guardrails

```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

The bundled five-file sampler accepts only the source-backed `HOL::TrueI`
projection through checked declarations, its real `True` definition/proof and
exact-owner replay. It does not execute the whole HOL theory or unrelated ML.
The standalone `tests/fixtures/TrustedTrueI.thy` and
`tests/fixtures/TrustedPureIdentity.thy` return separate accepted tokens and
do not add to the sampled count. Pure identity uses
`!!P::prop. PROP P ==> PROP P` with `by assumption` and premise-local replay.
The TCB is `crates/kernel/`; `src/kernel/` re-exports it. Legacy `src/core`,
search indexes and complete theory loading do not mint trusted tokens.

The all-Rust automation cutover and integrated quality repairs have distinct
[delivery evidence](docs/status/PROJECT_STATUS.md#current-delivery-state).
The four workspace members are the root product (`isabelle-rs`, sole default
member), isolated TCB (`isabelle-kernel`), offline evidence data
(`isabelle-evidence`, no theorem authority), and independent automation (`xtask`).
Package B's nine-root official reference observation is historical, not native
Rust acceptance. P2/P3/P4 implementation has resumed under reviewed P1
contracts; the two external Rust THM consumers have narrow local evidence, not
complete ML `Thm: THM`, ROOT/HOL or nine-root compatibility. See the
[THM inventory](docs/status/NATIVE_THM_INTERFACE_INVENTORY.md) and
[current status](docs/status/PROJECT_STATUS.md#current-delivery-state).
The JVM-free policy disables local `reference prepare/build/inventory` before
workspace access; only offline `reference compare` remains available. Do not
launch the official runtime or solver to update frozen reference results.

Complete legacy loading is transactional and fail-closed. Proof completion and
automation require an actual Strict/checked result matching the complete goal;
Compat/search data, unfinished goals, and malformed ATP evidence cannot
authorize success. These hardened legacy contracts do not mint accepted tokens.
Read the canonical status for current verification failures before committing;
passing the strict gate does not imply a green full-project quality gate.

## Claude-Specific Routing

- `.claude/rules/` contains domain-specific compatibility rules.
- `.claude/skills/` and `.claude/commands/` are thin workflow adapters.
- `.claude/agents/` may perform bounded review; high-risk TCB changes still need
  independent evidence and the repository gates.
- Follow [SCOPE → DESIGN → IMPLEMENT → REVIEW → VERIFY → DELIVER](docs/guides/DEVELOPMENT.md#engineering-workflow).
  `.claude/` routes this workflow; parsing its metadata does not prove harness
  loading, hook execution or permission enforcement.
- Do not create commits, rewrite history, or push without explicit user
  instruction.

Use the [xtask command catalog](scripts/README.md#verification), including
`verify`, `docs`, `strict`, `core`, `selftest` and workspace `test`. `all`
includes Tier diagnostics, not the full repository matrix. Run the applicable behavior
proof and project gates before the complete `~/.omp/agent/validate.sh`;
report failures separately. Short explanatory examples are allowed; all
maintained automation lives in `xtask/`. `scripts/` holds official reference
probe inputs and classified design templates, not runnable project scripts.
