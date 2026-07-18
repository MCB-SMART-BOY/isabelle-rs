---
name: Debug Stack Overflow
description: Diagnose stack overflow errors and select the right iterative conversion pattern (stack, worklist, continuation frames, iterative deepening).
category: debugging
version: 3.0.0
triggers: [stack overflow, overflowed its stack, SIGABRT, recursion too deep, stack overflow at]
permissions: [Bash:cargo test, Bash:RUST_MIN_STACK, Read]
---
# Debug Stack Overflow

First reproduce with the appropriate `scripts/dev-check.sh` mode, which sets the
standard large stack. If failure persists, distinguish deep finite input from
non-progress recursion using a focused test and backtrace.

Prefer explicit Rust worklists, continuation frames, or iterative DFS while
preserving traversal order, binder depth, error behavior, and theorem burdens.
Add deep-input and equivalence tests. Large reusable iterative skeletons belong
in a classified design-only Rust file under `scripts/templates/`; short local
explanations may remain in Markdown.
