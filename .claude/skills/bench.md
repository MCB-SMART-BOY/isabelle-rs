---
name: Run Benchmarks
description: Run the selected repository verification mode and report failures, skips, and stack-sensitive scope exactly.
category: meta
version: 3.0.0
triggers: [benchmark, performance, test all, regression test, run all tests]
permissions: [Bash:cargo test, Bash:RUST_MIN_STACK]
---
# Bench

Use `scripts/dev-check.sh` as the only command source:

- `strict` for the firewall, attack, boundary, inline, and legacy-core suites.
- `core` for the exact sampled 125-theorem run.
- `tier2`, `tier3`, or `broad` for theory-wide claims.
- `lib` only when explicitly testing the stack-sensitive full library.
- `all` for docs, strict, and all theory tiers.

Report actual output, elapsed time, failures, and skipped modes. Do not reuse
historical `125/125`, proof-rate, or test-count claims.
