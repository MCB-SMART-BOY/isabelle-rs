#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

rustfmt +stable --check scripts/check-doc-links.rs scripts/templates/*.rs

count=0
for template in scripts/templates/*.rs; do
    [[ -f "$template" ]] || continue

    IFS= read -r classification < "$template"
    if [[ "$classification" != "// Classification: design-only standalone template; not production code." ]]; then
        echo "$template: missing design-only classification header" >&2
        exit 1
    fi

    crate_name="$(basename "$template" .rs)"
    rustup run stable rustc \
        --edition 2024 \
        --crate-name "$crate_name" \
        --crate-type lib \
        --emit metadata \
        --out-dir "$TMP_DIR" \
        "$template"
    count=$((count + 1))
done

echo "Standalone design templates compile ($count files); project API compatibility not checked"
