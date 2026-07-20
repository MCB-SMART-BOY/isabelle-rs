#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export RUST_MIN_STACK="${RUST_MIN_STACK:-268435456}"

usage() {
    printf '%s\n' \
        "Usage: scripts/dev-check.sh <mode>" \
        "" \
        "Modes:" \
        "  fast       cargo fmt/check with Cargo.lock frozen" \
        "  strict     strict-kernel firewall and regression gate" \
        "  checkpoint strict + feature-branch focused tests" \
        "  core       sampled HOL/Orderings/Set/Nat/List 125-theorem run" \
        "  tier2      tier-2 theory verification" \
        "  tier3      tier-3 theory verification" \
        "  broad      core, tier2, and tier3 verification" \
        "  lib        stack-sensitive full library tests (explicit only)" \
        "  docs       Markdown policy, Rust templates, fmt, and check" \
        "  all        docs, strict, and broad gates"
}

run_fast() {
    cargo +stable fmt --check
    cargo +stable check --locked
}

run_strict() {
    bash scripts/check-strict-kernel.sh
}

run_core() {
    cargo +stable test --locked \
        core_batch_snapshot_reports_one_transitional_and_zero_kernel_trusted -- --nocapture
}

run_tier2() {
    cargo +stable test --locked --test tier2_verify -- --nocapture
}

run_tier3() {
    cargo +stable test --locked --test tier3_verify -- --nocapture
}

run_broad() {
    run_core
    run_tier2
    run_tier3
}

run_lib() {
    cargo +stable test --locked --lib
}

run_docs() {
    bash scripts/check-markdown-snippets.sh
    bash scripts/check-doc-links.sh
    bash scripts/check-rust-templates.sh
    run_fast
}


run_checkpoint() {
    run_strict
    cargo +stable test prove_true_i_succeeds --lib -- --nocapture
    cargo +stable test -p isabelle-kernel --lib polytype_tests -- --nocapture
    cargo +stable test -p isabelle-kernel --lib axiom_dep_tests -- --nocapture
    cargo +stable test -p isabelle-kernel --lib definition_tests -- --nocapture
}

case "${1:-}" in
    fast) run_fast ;;
    strict) run_strict ;;
    checkpoint) run_checkpoint ;;
    core) run_core ;;
    tier2) run_tier2 ;;
    tier3) run_tier3 ;;
    broad) run_broad ;;
    lib) run_lib ;;
    docs) run_docs ;;
    all)
        run_docs
        run_strict
        run_broad
        ;;
    -h|--help|help)
        usage
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac
