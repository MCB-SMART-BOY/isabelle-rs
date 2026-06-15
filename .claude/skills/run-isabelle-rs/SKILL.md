---
name: run-isabelle-rs
description: Build, run, test, or verify isabelle-rs. Use when asked to run the Isabelle proof assistant kernel, build the project, run the demo, compile .thy files, run the LSP server, test a change, or verify the kernel is operational.
---

# run-isabelle-rs

Isabelle proof assistant kernel and Isar proof engine, rewritten in Rust.
This skill covers: build, demo, CLI batch compilation, LSP server, test suite, and direct library invocation.

**All paths in this file are relative to the repo root.**

## Prerequisites

Rust nightly (edition 2024). On Ubuntu:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain nightly
```

The full test suite needs 256MB+ stack. Stack size is set via env var (`RUST_MIN_STACK=268435456`), not an OS limit.

## Build

```bash
cargo build
```

## Run (agent path)

The driver smoke-tests build, demo, and kernel tests in one shot:

```bash
bash .claude/skills/run-isabelle-rs/driver.sh
```

Or run individual pieces:

```bash
# Demo mode — exercises types, terms, kernel, Isar proof engine, theory loading
cargo run --bin isabelle-rs

# LSP server — JSON-RPC over stdio (kill with Ctrl-C)
cargo run --bin isabelle-rs -- --lsp

# Batch compile HOL theories (fast accept-all mode — skip proof replay)
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL --stats --accept-all

# Compile a single theory file
cargo run --bin isabelle-build -- isabelle-source/src/HOL/HOL.thy --stats --accept-all
```

The CLI `isabelle-build` binary expects `.thy` files. If `isabelle-source/` is missing (it is gitignored), the demo and tests still work — only batch compilation is affected.

## Direct invocation (library)

Most PRs touch library code, not the binary. Test a specific module:

```bash
# Kernel inference rules (fast, 32MB stack OK)
cargo test --lib core::thm

# Type system
cargo test --lib core::types

# Term operations
cargo test --lib core::term

# Proof methods
cargo test --lib isar::method

# Simplifier
cargo test --lib tools::simp
```

## Test suite

```bash
# Full unit test suite (256MB stack required)
RUST_MIN_STACK=268435456 cargo test --lib

# Core verification (5 files, 125 theorems, needs 256MB stack)
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files --lib -- --nocapture

# Tier 2 verification
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture

# Tier 3 verification
RUST_MIN_STACK=268435456 cargo test --test tier3_verify -- --nocapture

# Fast smoke test — one-of-each
cargo test --lib core::thm types term isar::method tools::simp

# BNF/datatype tests
cargo test --test bnf_tests

# Integration tests
cargo test --test integration_tests

# Benchmarks (release mode)
cargo bench
```

## Run (human path)

```bash
cargo run --bin isabelle-rs       # demo
cargo run --bin isabelle-rs -- --lsp  # LSP server
```

That spawns foreground processes. Kill with Ctrl-C. Useless headless.

## Gotchas

- **Stack overflow at default 8MB**: Any test involving deep term rewriting (verification, simp, linarith) will stack-overflow. Always set `RUST_MIN_STACK=268435456` for full test runs. Kernel-unit tests (`core::thm`) are safe at default stack.
- **`isabelle-source/` is gitignored**: The directory with .thy files for batch compilation is present in the dev environment but excluded from the repo. A fresh clone won't have it. The demo and tests don't need it.
- **Batch compile panics in accept-all mode**: The `--accept-all` flag skips proof replay, but some theories produce proof-state panics (expected — they're caught per-file). The final report still shows `N ok, 0 failed`.
- **`cargo run` needs `--bin`**: There are two binaries. `cargo run` without `--bin` fails with an ambiguity error. Use `cargo run --bin isabelle-rs` or `cargo run --bin isabelle-build`.
- **Rust nightly required**: Edition 2024 means nightly toolchain. `rustup default nightly` or use `cargo +nightly`.
- **Release mode is dramatically faster**: Kernel ops go from microseconds to nanoseconds. Use `cargo build --release` before `cargo bench`.

## Troubleshooting

| Symptom | Fix |
|---------|-----|
| `SIGSEGV` or `stack overflow` in tests | Set `RUST_MIN_STACK=268435456` |
| `could not determine which binary to run` | Add `--bin isabelle-rs` or `--bin isabelle-build` |
| `no such file or directory: isabelle-source/...` | Source is gitignored; skip batch compile or obtain Isabelle distribution separately |
| `error[E0554]: #![feature]` — not on nightly | `rustup default nightly` |
| Build hangs or times out | First build is large (~1 min). Subsequent builds are fast. |
