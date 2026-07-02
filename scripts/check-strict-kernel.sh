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
# Design: uses run_step with temp-file log capture so the real exit code
# of each cargo/test invocation is preserved.  No tail/grep-as-exit-code.
# ============================================================================
set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

failures=0

banner() { echo ""; echo -e "${YELLOW}=== $1 ===${NC}"; }

# run_step "title" command [args...]
#
# Runs the command, capturing stdout+stderr to a temp file.  On success
# prints the last 20 lines of output and PASS.  On failure prints the
# last 80 lines and FAIL, then increments the global `failures` counter.
# The return value is the command's raw exit code so callers can still do
#   run_step ... || true
# when they want to keep going after a failure.
run_step() {
    local title="$1"
    shift

    local log
    log="$(mktemp)"

    local rc=0
    "$@" >"$log" 2>&1 || rc=$?

    if [ "$rc" -eq 0 ]; then
        tail -20 "$log"
        echo -e "  ${GREEN}PASS${NC}"
        rm -f "$log"
        return 0
    else
        tail -80 "$log"
        echo -e "  ${RED}FAIL${NC} (exit code $rc)"
        rm -f "$log"
        failures=$((failures + 1))
        return "$rc"
    fi
}

# ── 1. Formatting ──
banner "1. Formatting (cargo +stable fmt --check)"
run_step "Formatting" cargo +stable fmt --check || true

# ── 2. Compilation ──
banner "2. Compilation (cargo +stable check)"
run_step "Compilation" cargo +stable check || true

# ── 3. Kernel firewall ──
banner "3. Kernel dependency firewall"
run_step "Firewall" bash scripts/check-kernel-firewall.sh || true

# ── 4. Integration attack tests ──
banner "4. Kernel rewrite soundness (integration attack tests)"
run_step "kernel_rewrite_soundness" cargo +stable test --test kernel_rewrite_soundness || true

# ── 5. Kernel soundness tests ──
banner "5. Kernel soundness (trusted boundary tests)"
run_step "kernel_soundness" cargo +stable test --test kernel_soundness || true

# ── 6. Inline kernel unit tests ──
banner "6a. Kernel inline unit tests (thm)"
run_step "kernel::thm" cargo +stable test --lib kernel::thm:: || true

banner "6b. Kernel inline unit tests (unify)"
run_step "kernel::unify" cargo +stable test --lib kernel::unify::tests:: || true

banner "6c. Kernel inline unit tests (rules)"
run_step "kernel::rules" cargo +stable test --lib kernel::rules::tests:: || true

# ── 7. Legacy core tests ──
banner "7. Legacy core:: tests"
run_step "core::" cargo +stable test --lib core:: || true

# ── Summary ──
echo ""
echo "============================================"
if [ "$failures" -eq 0 ]; then
    echo -e "${GREEN}STRICT KERNEL GATE PASSED${NC}"
    exit 0
else
    echo -e "${RED}STRICT KERNEL GATE FAILED${NC} — $failures check(s)"
    exit 1
fi
