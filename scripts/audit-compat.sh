#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if command -v rg >/dev/null 2>&1; then
    SCANNER=rg
else
    SCANNER=grep
fi

run_scan() {
    local pattern="$1"
    local status=0
    if [[ "$SCANNER" == rg ]]; then
        rg -n "$pattern" src tests --glob '!target' || status=$?
    else
        grep -R -n -E --exclude-dir=target "$pattern" src tests || status=$?
    fi
    if ((status > 1)); then
        echo "compatibility audit scan failed with status $status" >&2
        return "$status"
    fi
    return 0
}

echo "=== Compatibility theorem constructors ==="
run_scan 'assume_compat\(|reflexive_compat\('

echo
echo "=== Compatibility equality ==="
run_scan 'compat_alpha_eq'

echo
echo "=== Unchecked legacy certification ==="
run_scan 'CTerm::certify\('
