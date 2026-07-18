# Template Classifications

This directory contains reusable examples and design aids. It contains no
production theorem constructor, trusted API, or project-integrated module.

Classifications:

- **design-only**: a proposed interface or architecture shape. It may contain
  placeholders and must not be imported into production code as proof authority.
- **example**: sample data or configuration used to explain a format. It is not
  a supported production configuration unless another document explicitly says
  so.
- **production**: maintained runtime/build input exercised through the real
  project. No file in this directory currently has this classification.

| File | Classification | What is checked |
|---|---|---|
| `checked_hol_proposition_normalization.rs` | design-only | Standalone Rust compilation only. |
| `proof_session.rs` | design-only | Standalone Rust compilation only. |
| `resolution_api.rs` | design-only | Standalone Rust compilation only. |
| `symbolic_compute_backend.rs` | design-only | Standalone Rust compilation only. |
| `isabelle-kernel.Cargo.toml` | design-only | Documentation review only. |
| `isabelle-project.toml` | design-only | Documentation review only. |
| `agent-request.json` | example | Documentation review only. |
| `agent-response.json` | example | Documentation review only. |
| `agent-goals-response.json` | example | Documentation review only. |
| `agent-state-diff.json` | example | Documentation review only. |
| `phase-plan.md` | example | Documentation review only. |
| `claude-rule.md` | example | Documentation review only. |
| `claude-skill.md` | example | Documentation review only. |

`scripts/check-rust-templates.sh` verifies that the Rust design files are
standalone and internally compilable. It does **not** prove that their names,
types, semantics, dependencies, or trust boundaries match the current
`isabelle-rs` production API. Source code, tests, and accepted ADRs remain
authoritative.

Short explanatory Bash, Rust, PowerShell, TOML, and JSON blocks may remain in
Markdown. Large runnable or duplicated snippets belong in `scripts/` or this
directory, with a link from the document and an explicit classification here.
