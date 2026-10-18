---
name: Run Isabelle-rs
description: Build, launch, test, or verify Isabelle-rs through maintained commands.
category: development
version: 2.0.0
triggers: [run, start, build, screenshot, demo, compile, launch, test change, verify kernel]
permissions: [Bash:cargo build, Bash:cargo run, Bash:cargo test, Bash:RUST_MIN_STACK]
---
# Run Isabelle-rs

Use `cargo +stable xtask`; see [the command catalog](../../scripts/README.md#verification).
`verify` aggregates deterministic repository checks including full workspace
tests; `selftest` checks the automation independently. `fast` is only
format/check; `strict` is a scoped trusted-boundary gate; `core` samples bundled
theories, while `tier2`, `tier3`, `broad` and `all` are explicit report-only
diagnostics, not full quality gates. `lib` is root-only; `test` runs the full
workspace. Bare `cargo test` selects only the root default member. Independent
security audits and the global validator remain separate. Report actual failures
and unrun paths.

Launch the research demo with `cargo +stable run --locked --bin isabelle-rs`;
add `-- --lsp` for the experimental protocol server. Compile a narrowly
supported checked theory with
`cargo +stable run --locked --bin isabelle-build -- PATH.thy`; unsupported
declarations, method scripts, or unfinished proofs fail rather than being
reported as complete.

For screenshot or demo requests, launch the requested binary first and capture
only an observed UI or terminal state. Report the exact command, observed result,
and any stack-sensitive or skipped suite. The LSP and theory compiler remain
partial prototypes, not Isabelle/PIDE compatibility claims.
