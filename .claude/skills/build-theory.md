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
`src/theory/loader.rs`, and `src/theory/session_builder.rs`. Preserve source
proposition consumption, context, constant/free identity, explicit types, and
meta/object connective distinctions.

Current theory reports are transitional legacy statistics. Never describe
`is_strict_closed_proved()` as new-kernel trust. Run `scripts/dev-check.sh core`
for sampled claims and the appropriate `tier2`/`tier3` mode for broader claims.
Put reusable diagnostics in Bash or Rust files under `scripts/` and remove them
after use if they are not stable.
