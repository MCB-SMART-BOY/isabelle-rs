---
name: Run Benchmarks
description: Run the selected repository verification mode and report failures, skips, and stack-sensitive scope exactly.
category: meta
version: 3.0.0
triggers: [benchmark, performance, test all, regression test, run all tests]
permissions: [Bash:cargo test, Bash:RUST_MIN_STACK]
---
# Bench

Use [the command catalog](../../scripts/README.md#verification) for exact
`cargo +stable xtask` entry points:

- `verify` for deterministic repository checks, including full workspace tests;
  `selftest` separately for product-independent automation.
- `strict` for the scoped trusted-kernel gate; `core` for sampled 125-theorem
  outcomes. Historical `KernelTrustedClosed: 1/125` and
  `TransitionalStrictClosed: 0/125` are not fresh results; CLI fixtures are separate.
- `tier2`, `tier3`, `broad` or `all` only as explicit report-only diagnostics.
- `lib` for root-library tests; `test` for full workspace tests. Bare `cargo test`
  covers only the root default member.

`all`/`broad` do not replace `verify`, `selftest`, independent security audits
or the global validator. Benchmark performance only with actual separately
measured runs; report observed output, duration, failures, and unrun modes.
