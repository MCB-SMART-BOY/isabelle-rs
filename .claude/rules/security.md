---
description: Trusted-kernel, dependency, unsafe, parser-input, and artifact security.
globs: "**/*.rs"
alwaysApply: false
version: 2.0
updated: 2026-10-03
---
# Security Rules

Treat theorem construction, source elaboration, theory identity, deserialization,
plugins, and dependencies as security boundaries. Avoid `unsafe`; when required,
document invariants and add focused tests. Reject malformed/unconsumed input and
resource exhaustion without upgrading it into trusted data.

External compute and WASM plugins remain untrusted candidate producers.
Approved compile-time Rust native plugins instead expose explicit host services
with scoped effects; neither path grants theorem authority. The explicitly
JVM-only names are disabled at load time, not callable fallbacks; see
[`JVM-free direction`](../../docs/status/PROJECT_STATUS.md#jvm-free-architecture-direction-2026-10-16).
Dependency or lockfile changes require explicit scope and normal verification.
Never log or commit secrets.

The WASM plugin host depends on supported Wasmtime 36 LTS and enables only
`runtime`, `cranelift`, and `std`; WASM plugins supply search metadata, never trusted
theorems. Keep `Cargo.lock` current with upstream security patches. The
`deny.toml` rejects vulnerable, unsound, and unmaintained dependencies without
advisory exceptions and explicitly allows the reviewed dependency licenses;
run `cargo +stable xtask audit` after dependency updates; this aggregates
`cargo audit` and full `cargo deny check` without weakening either policy.
`verify` does not invoke this network-dependent audit, nor independent
gitleaks/trivy checks or the complete global validator; run and report
applicable security gates separately.
