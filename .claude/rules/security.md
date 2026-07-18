---
description: Trusted-kernel, dependency, unsafe, parser-input, and artifact security.
globs: "**/*.rs"
alwaysApply: false
version: 2.0
updated: 2026-07-18
---
# Security Rules

Treat theorem construction, source elaboration, theory identity, deserialization,
plugins, and dependencies as security boundaries. Avoid `unsafe`; when required,
document invariants and add focused tests. Reject malformed/unconsumed input and
resource exhaustion without upgrading it into trusted data.

External compute and plugins remain untrusted candidate producers. Dependency or
lockfile changes require explicit scope and normal verification. Never log or
commit secrets.
