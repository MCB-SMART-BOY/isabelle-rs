---
description: Typed error handling at parser, adapter, kernel, and replay boundaries.
globs: "**/*.rs"
alwaysApply: false
version: 2.0
updated: 2026-10-19
---
# Error Handling Rules

Use typed enums for control flow. Error display strings are diagnostics only and
must never decide acceptance, rejection class, fallback, or theorem trust.
Preserve `KernelError` detail at trusted boundaries; collapse to `Option` only
for a documented fail-closed search non-match.

Only explicitly classified sampled/search outcomes may become a specific
`admitted:*` legacy reason, never `assume`. Complete-source loading returns
typed `TheoryLoadError` or `GoalExportError` and cannot publish partial
results on failure. Strict kernel paths have no admit constructor. Add tests
showing that message changes do not alter typed classification.

Keep common `Result` error values compact without discarding diagnostics.
`MlError.operation` owns a `Box<str>`; `RootPrefixFailure.error` and nested
native source/reference host errors are boxed only on failure. Preserve the
original exception, span, trace, cancellation and `Error::source` chain.
Native reference input is missing only for `HostIoError::Io(NotFound)`;
permission, lifecycle and malformed evidence failures must not be downgraded.
