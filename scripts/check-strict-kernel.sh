#!/usr/bin/env bash
# ============================================================================
# Strict kernel verification gate
# ============================================================================
# Run this before pushing any src/kernel/ or kernel test change.
#
#   bash scripts/check-strict-kernel.sh
#
# The gate verifies:
#   1. Formatting (cargo +stable fmt --check)
#   2. Compilation  (cargo +stable check)
#   3. Kernel firewall (no legacy deps, no forbidden patterns)
#   4. Integration attack tests (kernel_rewrite_soundness)
#   5. Kernel soundness tests (kernel_soundness)
#   6. Inline kernel unit tests (thm, unify, rules)
#   7. Legacy core compatibility tests (core::)
# ============================================================================
set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

failures=0

banner() { echo ""; echo -e "${YELLOW}=== $1 ===${NC}"; }
pass()   { echo -e "  ${GREEN}PASS${NC}"; }
fail()   { echo -e "  ${RED}FAIL${NC}"; failures=$((failures + 1)); }

# ── 1. Formatting ──
banner "1. Formatting (cargo +stable fmt --check)"
cargo +stable fmt --check 2>&1 && pass || fail

# ── 2. Compilation ──
banner "2. Compilation (cargo +stable check)"
cargo +stable check 2>&1 | tail -1 && pass || fail

# ── 3. Kernel firewall ──
banner "3. Kernel dependency firewall"
bash scripts/check-kernel-firewall.sh 2>&1 && pass || fail

# ── 4. Integration attack tests ──
banner "4. Kernel rewrite soundness (integration attack tests)"
cargo +stable test --test kernel_rewrite_soundness 2>&1 | tail -2 && pass || fail

# ── 5. Kernel soundness tests ──
banner "5. Kernel soundness (trusted boundary tests)"
cargo +stable test --test kernel_soundness 2>&1 | tail -2 && pass || fail

# ── 6. Inline kernel unit tests ──
banner "6. Kernel inline unit tests (thm)"
cargo +stable test --lib kernel::thm:: 2>&1 | tail -2 && pass || fail
banner "6b. Kernel inline unit tests (unify)"
cargo +stable test --lib kernel::unify::tests:: 2>&1 | tail -2 && pass || fail
banner "6c. Kernel inline unit tests (rules)"
cargo +stable test --lib kernel::rules::tests:: 2>&1 | tail -2 && pass || fail

# ── 7. Legacy core tests ──
banner "7. Legacy core:: tests"
cargo +stable test --lib core:: 2>&1 | tail -2 && pass || fail

# ── Summary ──
echo ""; echo "============================================"
if [ "$failures" -eq 0 ]; then
    echo -e "${GREEN}STRICT KERNEL GATE PASSED${NC}"
    exit 0
else
    echo -e "${RED}STRICT KERNEL GATE FAILED${NC} — $failures check(s)"
    exit 1
fi
