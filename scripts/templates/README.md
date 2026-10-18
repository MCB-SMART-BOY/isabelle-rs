# Template Classifications

This directory contains reusable examples and design aids. It contains no
production theorem constructor, trusted API, or project-integrated module.

For actual gates and CLI contracts, use
[scripts/README.md](../README.md) and the
[development guide](../../docs/guides/DEVELOPMENT.md). The agent adapter is
[`.claude/`](../../.claude/), not a `docs/agent/` mirror.

The rule, skill and phase-plan forms follow the shared
[engineering workflow](../../docs/guides/DEVELOPMENT.md#engineering-workflow).
They are examples, not executable permission grants. Keep skill frontmatter
and the adapter registry consistent; instantiating a template does not
authorize new proof rules, product packages, commits or releases.

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

`cargo +stable xtask templates` checks classification and standalone compilation
of the Rust design files. It does **not** prove that names, types, semantics,
dependencies or trust boundaries match the production `isabelle-rs` API.
Source code, tests and accepted ADRs remain authoritative. The deterministic
repository gate is `cargo +stable xtask verify`; its included docs checks still
do not establish production template compatibility. Independent `selftest`,
security audits and the global workstation validator remain separate.

Keep only short explanatory Rust/TOML/JSON/command examples in Markdown.
Reusable automation lives in [xtask](../../xtask/); this directory holds
classified examples, while `scripts/reference/` holds official reference
probe inputs. Neither directory is a second runnable project-script entry.
