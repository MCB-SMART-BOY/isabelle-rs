#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

rustup run stable rustc \
    --edition=2024 \
    "$ROOT_DIR/scripts/check-doc-links.rs" \
    -o "$TMP_DIR/check-doc-links"
"$TMP_DIR/check-doc-links" "$ROOT_DIR"
