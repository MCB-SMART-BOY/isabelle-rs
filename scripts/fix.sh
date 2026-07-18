#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

usage() {
    printf '%s\n' \
        "Usage: scripts/fix.sh <check|apply>" \
        "" \
        "  check  Run formatting and compilation checks without editing source" \
        "  apply  Run cargo fix, rustfmt, and clippy fixes on the dirty worktree"
}

case "${1:-}" in
    check)
        scripts/dev-check.sh fast
        ;;
    apply)
        cargo +stable fix --locked --allow-dirty --allow-staged
        cargo +stable fmt
        cargo +stable clippy --locked --fix --allow-dirty --allow-staged
        cargo +stable check --locked
        ;;
    -h|--help|help)
        usage
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac
