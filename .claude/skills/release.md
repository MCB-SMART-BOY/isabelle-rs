---
name: release
description: Complete a phase release: summarize → verify → version → sync 12 docs → finalize. Full SOP pipeline.
category: release
version: 2.0.0
triggers: [release, version bump, phase complete, changelog]
permissions: [Bash:cargo test, Bash:cargo check, Bash:cargo clippy, Read, Edit, Bash:git]
---

# Release

Execute the standard operating procedure for completing a phase and cutting a release.

## Pipeline

```
1. SUMMARIZE → 2. VERIFY → 3. VERSION → 4. UPDATE → 5. FINALIZE
```

## Step 1: SUMMARIZE

List all deliverables: new files, modified files, test count, performance impact, breaking changes.

## Step 2: VERIFY

```bash
cargo check --lib                              # zero warnings
cargo test --lib                               # all passing (known overflows excepted)
RUST_MIN_STACK=268435456 cargo test --lib      # with stack
cargo clippy -- -D warnings                    # clean
cargo fmt -- --check                           # formatted
```

## Step 3: VERSION

Follow semver:
- **Patch** (x.y.Z): bug fixes, no API change
- **Minor** (x.Y.z): new feature, backward compatible
- **Major** (X.y.z): breaking API change

## Step 4: UPDATE

Sync these 12 files:

| File | What |
|------|------|
| `Cargo.toml` | `version`, `description` |
| `CHANGELOG.md` | Dated version entry |
| `CLAUDE.md` | Status table, known issues, module map |
| `README.md` | Version, stats, features |
| `docs/ARCHITECTURE.md` | Component statuses, file stats |
| `docs/ROADMAP.md` | Phase markers, verification counts |
| `docs/DEVELOPMENT.md` | Benchmarks, stats, known issues |
| `docs/GAP_ANALYSIS.md` | Complete gap analysis (ISABELLE_COMPARISON merged) |
| `.claude/rules/README.md` | Status table, known issues |
| `.claude/rules/post-session.md` | Completion checklist |
| `.claude/skills/*.md` | Commands/workflows if changed |

## Step 5: FINALIZE

```bash
cargo check --lib               # final check
git diff --stat                 # review all changes
git status                      # confirm clean state
```

## Release Commit Template

```
vX.Y.Z: <short summary>

- <module>: <change 1>
- <module>: <change 2>
- docs: synced ARCHITECTURE vN, ROADMAP vN
- Cargo.toml vX.Y.Z
- N new tests
```

## Phase Completion Checklist

```
□ New files created: <list>
□ Modified files: <list>
□ Tests: <N> new, all passing
□ cargo check --lib: zero warnings
□ cargo clippy -- -D warnings: clean
□ cargo fmt -- --check: clean
□ Cargo.toml version: vX.Y.Z
□ CHANGELOG.md: entry added
□ CLAUDE.md: status + known issues updated
□ docs/ARCHITECTURE.md: statuses synced
□ docs/ROADMAP.md: phase complete
□ docs/DEVELOPMENT.md: stats synced
□ docs/GAP_ANALYSIS.md: coverage updated (merged ISABELLE_COMPARISON)
□ .claude/rules/README.md: status synced
□ .claude/rules/post-session.md: checklist verified
```

## Related

- `.claude/rules/post-session.md` — Full SOP details
- `.claude/rules/release.md` — Semver rules
- `.claude/skills/verify.md` — Pre-release verification
- `.claude/skills/bench.md` — Performance baseline
