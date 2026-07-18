# Scripts

Reusable commands and full scripts live here instead of being duplicated across
Markdown. Short explanatory code/configuration blocks may remain next to the
contract they explain. Prefer Rust for typed design templates and Bash for
repository orchestration, audits, and verification entry points.

Isabelle-rs remains a Rust research prototype of an Isabelle/Pure-inspired LCF
kernel. See [PROJECT_STATUS.md](../docs/PROJECT_STATUS.md) for current trust and
completion status.

## Verification

[dev-check.sh](dev-check.sh) is the common entry point. Its modes are:

| Mode | Purpose |
|---|---|
| `fast` | Stable formatting and `cargo check --locked`. |
| `strict` | Full strict-kernel firewall, attack, replay, and legacy-core gate. |
| `core` | Exact 125-theorem sampled run with the standard large stack. |
| `tier2` / `tier3` | Stack-sensitive theory verification tiers. |
| `broad` | `core`, `tier2`, then `tier3`. |
| `lib` | Explicit stack-sensitive full library test. Do not infer success unless it actually completes. |
| `docs` | Markdown size/duplication policy, template classification and standalone compilation, formatting, links, and compilation. |
| `all` | Documentation, strict, and broad gates. |

Run a mode as an ordinary repository command, for example
`scripts/dev-check.sh strict`.

Supporting checks:

- [check-strict-kernel.sh](check-strict-kernel.sh) is the underlying strict gate.
- [check-kernel-firewall.sh](check-kernel-firewall.sh) enforces kernel dependency
  and visibility boundaries.
- [check-markdown-snippets.sh](check-markdown-snippets.sh) allows short
  explanatory fences and rejects oversized or duplicated Bash, Rust,
  PowerShell, TOML, and JSON blocks.
- [check-doc-links.sh](check-doc-links.sh) compiles and runs the standalone Rust
  local-link checker in [check-doc-links.rs](check-doc-links.rs).
- [check-rust-templates.sh](check-rust-templates.sh) checks classification
  headers and standalone compilation for every Rust design template.
- [audit-compat.sh](audit-compat.sh) inventories legacy compatibility constructors
  and certification calls.
- [fix.sh](fix.sh) keeps check-only and explicitly mutating Rust auto-fix
  workflows separate.

## Execution

- Research demo: `cargo run --locked --bin isabelle-rs`.
- Experimental LSP server: `cargo run --locked --bin isabelle-rs -- --lsp`.
- Partial theory compiler:
  `cargo run --locked --bin isabelle-build -- PATH.thy`.

These launch paths exercise prototype tooling; they do not claim full
Isabelle/PIDE or Isabelle/HOL compatibility.

## Installation

- Linux/macOS: [install.sh](install.sh), with `--release`, `--check`, or
  `--dir PATH` as needed.
- Windows: [install.ps1](install.ps1), with `-Release`, `-Check`, or `-Dir PATH`.

When invoked from this checkout without an explicit directory, both installers
use the current branch and do not pull `main`. Remote execution and explicit
install directories clone or fast-forward the public `main` branch.

Remote one-line installers remain supported by those scripts, but local review
before execution is preferred.

## Releases

The GitHub release workflow accepts only a `vX.Y.Z` tag matching
`Cargo.toml`, runs `scripts/dev-check.sh all`, and then builds binaries for the
three supported CI hosts. It does not publish to crates.io; crate publication is
a separate, explicit release action after a version bump and package check.

Lockfile changes are never incidental to these workflows. A lock-only refresh
needs an explicit dependency/security rationale; successful locked checks prove
validity, not intent.

## Templates

Reusable examples and design skeletons live in [templates/](templates/).
Their authoritative classifications and validation limits are in
[templates/README.md](templates/README.md).

Current groups:

- checked HOL proposition, resolution, symbolic-compute, and proof-session Rust
  files: **design-only**;
- future kernel/project TOML manifests: **design-only**;
- APP JSON payloads and Claude/phase Markdown forms: **example**;
- production files in this directory: **none**.

The Rust files deliberately compile as standalone crates. That check catches
local syntax and type errors only. It does not prove that a template matches
the current project API, composes with production modules, preserves kernel
invariants, or defines an accepted architecture.
