---
name: sync-docs
description: Sync docs/ and .claude/ after code changes. Use after modifying src/, adding features, or changing APIs. Keeps ARCHITECTURE.md, GAP_ANALYSIS.md, ROADMAP.md, DEVELOPMENT.md, CLAUDE.md, ADRs, and skills in sync with the code.
category: maintenance
version: 1.1.0
triggers: [sync docs, update docs, doc sync, stale docs, after code change, update documentation]
permissions: [Read, Write, Edit, Bash:git, Bash:cargo]
---

# Sync Docs

Sync documentation with current code state after changes. Covers both `docs/` and `.claude/`.

## When to Run

⚠️ **硬性要求 — 不可跳过。** 每次完成任何任务/Phase/功能后必须执行。

- 新功能 / 模块添加
- API 变更（函数签名、类型）
- Bug 修复（特别是 known issues）
- 严格内核规则变更 (`src/kernel/`)
- Phase 完成（另见 `/release`）
- **任何 src/ 变更之后** — git diff 显示 src/ 变更但 docs/ 和 .claude/ 未触及

## What Gets Synced

### docs/ (10 files)

| File | When to Update |
|------|---------------|
| `docs/ARCHITECTURE.md` | Module added/removed, component status change, module map change |
| `docs/GAP_ANALYSIS.md` | Module completed, coverage % change, new gap identified/fixed |
| `docs/ROADMAP.md` | Phase complete, new phase added, verification counts change |
| `docs/DEVELOPMENT.md` | Test commands change, benchmark results, known issues change |
| `docs/PROJECT_STATUS.md` | Trust boundary, completion estimates, kernel state change |
| `docs/TRUST.md` | Trust model, oracle/admit rules, certification boundary change |
| `docs/KERNEL_RULES.md` | Legacy kernel rule change |
| `docs/KERNEL_PRIMITIVES.md` | Strict kernel rule contract change |
| `docs/KERNEL_ATTACK_TESTS.md` | New/fixed attack test, known gap change |
| `docs/HPC_SYMBOLIC_COMPUTE_DESIGN.md` | HPC symbolic compute design, backend candidates, compute/kernel boundary |
| `docs/ADR-0001-kernel-core-rewrite.md` | Strangler migration progress, TCB boundary change |
| `docs/ADR-0002-layered-platform-architecture.md` | Target platform layer or dependency direction change |

### .claude/ (4 areas)

| Path | When to Update |
|------|---------------|
| `CLAUDE.md` | Project state table, known issues, iron laws, module map, common commands |
| `.claude/skills/*.md` | New skill, changed workflow, new/removed commands |
| `.claude/settings.json` | New permissions needed, new commands, env changes |
| `.claude/rules/*.md` | Rule changes, iron law additions, SOP updates |

## Quick Sync (single session)

```bash
# 1. See what's changed
git diff --stat HEAD -- src/

# 2. Check which docs reference changed modules
git log --oneline -1 -- docs/ .claude/ CLAUDE.md
```

Then update each stale file manually based on the diff.

## Full Sync (after phase/major change)

### Step 1: Collect state

```bash
# Line counts per module
wc -l src/core/*.rs src/isar/*.rs src/hol/*.rs src/tools/*.rs src/theory/*.rs src/kernel/*.rs

# Test counts
cargo test --lib -- --list 2>&1 | tail -5

# Verify counts
grep -c "impl.*Method" src/isar/method.rs 2>/dev/null || echo "check manually"

# File count
find src -name '*.rs' | wc -l

# Strict kernel primitive rule count
grep -c "pub fn" src/kernel/rules.rs 2>/dev/null || echo "check manually"
```

### Step 2: Update CLAUDE.md

Update the project state table at the top:
```
| Kernel | 15 ops + tpairs/shyps, strict src/kernel/ nucleus (11 rules), legacy src/core/ |
| Proof Engine | Isar state machine (3 modes) + N proof methods |
| Code | ~XK Rust LOC, N files |
| Tests | N+ (incl. kernel_rewrite_soundness) |
| Verification | Core 5/5 files 100% (125/125), Tier2 N/20 files 100% |
```

And the known issues table, module map table, and common commands.

### Step 3: Update docs/ARCHITECTURE.md

- Update status markers (✅/🟡/❌)
- Add `src/kernel/` to module map
- Sync module sizes with `wc -l` output
- Add new components, remove deleted ones

### Step 4: Update docs/GAP_ANALYSIS.md

- Update coverage percentages based on new implementation
- Mark completed files as ✅
- Add newly identified gaps
- Update the summary at the top

### Step 5: Update docs/ROADMAP.md

- Mark completed phases as Done
- Update verification counts
- Add planned phases

### Step 6: Update docs/DEVELOPMENT.md

- Update test commands if changed
- Update known issues
- Update project statistics

### Step 7: Update .claude/skills/

- New skills added → update skill files
- Commands changed → update the relevant skill

### Step 8: Verify

```bash
cargo check --lib          # still clean
git diff --stat            # review all doc changes
```

## Related

- `/release` — Full phase release pipeline (includes this step)
- `.claude/rules/post-session.md` — Phase completion SOP
- `.claude/rules/documentation.md` — Documentation standards
- `docs/ADR-0001-kernel-core-rewrite.md` — Strangler pattern decision
