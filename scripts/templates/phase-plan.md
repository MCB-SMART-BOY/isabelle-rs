# Phase <N>: <Title>

**Objective:** <one concrete outcome>

**Trusted boundary:** <what may and may not gain proof authority>

Follow [the authoritative engineering workflow](../../docs/guides/DEVELOPMENT.md#engineering-workflow)
for stages and verification. This plan records one bounded task; identify any
A–H delivery package separately from the engineering lifecycle.

**Non-goals:** <behavior, dependencies and user work that must remain unchanged>

## Baseline

- Commit/branch: <fresh git observation>
- Verification metric: <exact current output>
- Known failures: <classified list>
- Sources and owners: <current code/tests, canonical status and relevant design>
- Delivery package (if applicable): <roadmap package, not a capability claim>

## Changes

| Area | Change | Acceptance test |
|---|---|---|
| `<path>` | <behavioral change> | <test or audit> |

## Design And Review

- Failure semantics and recovery: <reject/retry/report; preserve original causes>
- Risk and authorization: <material tradeoffs or destructive actions needing approval>
- Independent slices: <disjoint owned paths and shared contracts before delegation>
- Review: <correctness reviewer; security reviewer when the boundary requires it>

## Verification

- Behavior proof: <exercise the actual changed path; docs/config need facts,
  links/anchors, metadata parsing and an applicable runtime smoke>
- Project gate: select actual commands from [scripts/README.md](../README.md#verification);
  record inputs, toolchain, results and scope. `verify` covers deterministic
  repository checks; `selftest` is separate. `strict`/`core`/`test` apply by change.
  `all`/Tier only run when explicitly selected as expensive diagnostics.
- Independent security audit and full global `~/.omp/agent/validate.sh` after
  project verification: report failures or unavailable prerequisites separately;
  `--quick` is not delivery evidence.
- Observed trust metrics: <transitional versus kernel-trusted, separate from
  source-backed fixtures; do not replace failed full tests with gate successes>

## Delivery

- Documentation and routing: <current facts and dependent bilingual/adapter entries>
- Remaining risks and unverified paths: <explicit blockers, not passing claims>
- Authorization: no commit, push, tag, publish or deployment without an explicit request.

## Exclusions

- <explicitly deferred work>
