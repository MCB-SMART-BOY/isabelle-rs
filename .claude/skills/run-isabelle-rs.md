---
name: Run Isabelle-rs
description: Build, launch, test, or verify Isabelle-rs through maintained commands.
category: development
version: 2.0.0
triggers: [run, start, build, screenshot, demo, compile, launch, test change, verify kernel]
permissions: [Bash:cargo build, Bash:cargo run, Bash:cargo test, Bash:RUST_MIN_STACK]
---
# Run Isabelle-rs

Use `scripts/dev-check.sh`; see `scripts/README.md` for verification modes.
`fast` performs format/check, `strict` runs the trusted-boundary gate, and
`core`/`tier2`/`tier3` provide stack-sensitive theory verification. Use `lib`
only for an explicit full-library claim.

Launch the research demo with `cargo run --locked --bin isabelle-rs`; add
`-- --lsp` for the experimental protocol server. Compile a theory with
`cargo run --locked --bin isabelle-build -- PATH.thy`.

For screenshot or demo requests, launch the requested binary first and capture
only an observed UI or terminal state. Report the exact command, observed result,
and any stack-sensitive or skipped suite. The LSP and theory compiler remain
partial prototypes, not Isabelle/PIDE compatibility claims.
