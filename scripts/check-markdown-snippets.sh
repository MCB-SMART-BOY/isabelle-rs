#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

MAX_EXPLANATORY_LINES="${MAX_EXPLANATORY_LINES:-40}"
DUPLICATE_MIN_LINES="${DUPLICATE_MIN_LINES:-12}"

for value in "$MAX_EXPLANATORY_LINES" "$DUPLICATE_MIN_LINES"; do
    if [[ -z "$value" || "$value" == *[!0-9]* ]]; then
        echo "Markdown snippet limits must be non-negative integers" >&2
        exit 2
    fi
done

markdown_files=()
if (($# > 0)); then
    while IFS= read -r file; do
        markdown_files+=("$file")
    done < <(
        find "$@" -type f -name '*.md' \
            -not -path '*/.git/*' \
            -not -path '*/target/*' \
            -not -path '*/isabelle-source/*' \
            -print 2>/dev/null | sort
    )
else
    while IFS= read -r file; do
        markdown_files+=("$file")
    done < <(
        find . -type f -name '*.md' \
            -not -path './.git/*' \
            -not -path './target/*' \
            -not -path './isabelle-source/*' \
            -print | sort
    )
fi

if ((${#markdown_files[@]} == 0)); then
    echo "No Markdown files found"
    exit 0
fi

if ! awk \
    -v max_lines="$MAX_EXPLANATORY_LINES" \
    -v duplicate_min="$DUPLICATE_MIN_LINES" '
    function reset_block() {
        in_block = 0
        block_lang = ""
        block_file = ""
        block_start = 0
        block_lines = 0
        block_body = ""
    }

    function report_unclosed() {
        printf "%s:%d: unclosed %s fenced block\n",
            block_file, block_start, block_lang > "/dev/stderr"
        failed = 1
        reset_block()
    }

    function finish_block(    key) {
        if (block_lines > max_lines) {
            printf "%s:%d: %s fenced block has %d lines; explanatory limit is %d\n",
                block_file, block_start, block_lang, block_lines, max_lines > "/dev/stderr"
            failed = 1
        }

        if (block_lines >= duplicate_min) {
            key = block_lang "\034" block_body
            if (key in seen_file) {
                printf "%s:%d: duplicates %s fenced block at %s:%d (%d lines)\n",
                    block_file, block_start, block_lang,
                    seen_file[key], seen_line[key], block_lines > "/dev/stderr"
                failed = 1
            } else {
                seen_file[key] = block_file
                seen_line[key] = block_start
            }
        }

        reset_block()
    }

    FNR == 1 && in_block {
        report_unclosed()
    }

    {
        lower = tolower($0)

        if (!in_block &&
            lower ~ /^```(bash|sh|shell|powershell|rust|toml|json)([[:space:],{].*)?$/) {
            block_lang = substr(lower, 4)
            sub(/[[:space:],{].*$/, "", block_lang)
            block_file = FILENAME
            block_start = FNR
            block_lines = 0
            block_body = ""
            in_block = 1
            next
        }

        if (in_block && $0 ~ /^```[[:space:]]*$/) {
            finish_block()
            next
        }

        if (in_block) {
            block_lines++
            block_body = block_body $0 "\n"
        }
    }

    END {
        if (in_block) {
            report_unclosed()
        }
        exit failed
    }
    ' "${markdown_files[@]}"; then
    echo >&2
    echo "Large or duplicated executable snippets belong under scripts/." >&2
    echo "Short explanatory Bash/Rust/PowerShell/TOML/JSON examples are allowed." >&2
    exit 1
fi

echo "Markdown snippet policy clean (${#markdown_files[@]} files; explanatory limit ${MAX_EXPLANATORY_LINES} lines)"
