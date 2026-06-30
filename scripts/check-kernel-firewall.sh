#!/usr/bin/env bash
set -euo pipefail

# check-kernel-firewall.sh
# Verify that src/kernel/ has no dependencies on legacy layers or
# forbidden trust-boundary patterns.
#
# This gate enforces the strangler-pattern boundary in ADR-0001:
#   src/kernel/  -> new strict TCB nucleus
#   src/core/    -> legacy quarantine
#
# Exit codes:
#   0 = firewall clean
#   1 = firewall breach found
#   2 = rg invocation error

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
KERNEL_DIR="$PROJECT_DIR/src/kernel"

if [ ! -d "$KERNEL_DIR" ]; then
    echo "ERROR: kernel directory not found: $KERNEL_DIR"
    exit 2
fi

BREACH=0

# ---------------------------------------------------------------------------
# Check 1: No imports from legacy or upper-layer crates/modules
# ---------------------------------------------------------------------------
echo "=== Check 1: No legacy/upper-layer crate dependencies ==="

LEGACY_PATTERN="crate::(core|isar|hol|theory|tools|session|lsp|server|wasm)"

if rg "$LEGACY_PATTERN" "$KERNEL_DIR/" 2>/dev/null; then
    echo "FIREWALL BREACH: src/kernel/ imports from legacy or upper-layer modules"
    BREACH=1
else
    echo "  Clean"
fi

# ---------------------------------------------------------------------------
# Check 2: No forbidden trust-boundary patterns
# ---------------------------------------------------------------------------
echo "=== Check 2: No forbidden trust-boundary patterns ==="

FORBIDDEN=(
    "Typ::dummy"
    "compat_alpha_eq"
    "assume_compat"
    "reflexive_compat"
    "admit"
)

for pattern in "${FORBIDDEN[@]}"; do
    if rg "$pattern" "$KERNEL_DIR/" 2>/dev/null; then
        echo "FIREWALL BREACH: forbidden pattern '$pattern' found in src/kernel/"
        BREACH=1
    else
        echo "  '$pattern': clean"
    fi
done

# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------
echo ""
if [ "$BREACH" -eq 0 ]; then
    echo "FIREWALL CLEAN: src/kernel/ has no legacy dependencies or forbidden patterns"
    exit 0
else
    echo "FIREWALL BREACH: fix the issues above before proceeding"
    exit 1
fi
