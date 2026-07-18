---
description: Verification modes, attack tests, and honest result reporting.
globs: "**/*.rs"
alwaysApply: false
version: 3.0
updated: 2026-07-18
---
# Testing Rules

Use `scripts/dev-check.sh`; `scripts/README.md` is the command index. Trusted
boundary work requires the `strict` gate. Sampled theorem claims require `core`;
broader theory claims require the corresponding tier mode.

Every kernel side condition needs a positive test and a rejection/tampering
attack. Every adapter needs `NotApplicable`, `Proved`, and typed `Rejected`
coverage. Report exact counts from current output, including skipped,
stack-sensitive, or pre-existing failures.
