---
name: Build Theory
description: Build and classify .thy files while reporting transitional and kernel-trusted results separately.
category: theory
version: 3.0.0
triggers: [theory loading, .thy file, parse failure, batch compile, session build, load theory]
permissions: [Bash:cargo test, Bash:cargo run, Read]
---
# Build Theory

Trace source through `src/hol/hol_loader.rs`, `src/isar/term_parser.rs`,
`src/theory/loader.rs`, and `src/theory/session_builder.rs`. Distinguish
standalone checked source compilation from legacy complete-source loading
and independent sampled/search collection.

`TheoryProcessor` succeeds only on its supported single-import, fully
consumed command subset with a final `end`; any lemma must have an actual
proved result. Failures publish no partial theory or index. A session may
publish independent good files, not descendants of failed imports. Successful
legacy results are transitional, never `KernelTrustedClosed`; searchable stats
alone are not compilation. Run `cargo +stable xtask strict` for the kernel gate.
For standalone source compiler changes, additionally run
`cargo +stable xtask test --lib theory::trusted_loader::` and both real fixture
CLI commands plus relevant rejection cases described in
[`scripts/README.md`](../../scripts/README.md) and [Verify Lemma](verify.md).
Run `core` for sampled claims and appropriate `tier2`/`tier3` modes for broader
claims; report the exact results rather than assuming broad completion.
