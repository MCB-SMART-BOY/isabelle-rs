#!/usr/bin/env bash
# Driver for isabelle-rs — smoke test: build, demo, kernel tests.
# Run from repo root. Exits 0 on success, non-zero on failure.
set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

fail() { echo -e "${RED}FAIL${NC} $*"; exit 1; }
pass() { echo -e "${GREEN}PASS${NC} $*"; }

echo "=== isabelle-rs driver ==="
echo ""

# 1. Build
echo "--- Build ---"
cargo build 2>&1
pass "cargo build"

# 2. Demo — exercises types, terms, kernel, Isar proof engine, theory loading
echo ""
echo "--- Demo ---"
cargo run --bin isabelle-rs 2>&1
pass "cargo run --bin isabelle-rs"

# 3. Fast kernel tests (safe at default 8MB stack)
echo ""
echo "--- Kernel tests ---"
cargo test --lib core::thm 2>&1
pass "cargo test --lib core::thm"

echo ""
echo "=== All checks passed ==="
