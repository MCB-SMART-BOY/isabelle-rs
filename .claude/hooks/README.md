# Claude Code Hooks

Custom hooks for isabelle-rs development automation.

## Available Hook Points

| Hook | When | Use Case |
|------|------|----------|
| `PreToolUse` | Before a tool executes | Validate Edit/Write targets, enforce kernel rules |
| `PostToolUse` | After a tool executes | Auto-run tests, check for regressions |
| `Notification` | On system events | Alert on build failures |
| `SessionStart` | When session begins | Restore environment, check git state |
| `SessionEnd` | When session ends | Cleanup, auto-commit, generate summary |

## Planned Hooks

### Pre-Edit Kernel Guard
Checks if Edit targets `src/core/thm.rs` and warns about kernel safety rules.

### Post-Test Regressions
After `cargo test` completes, compares with baseline for regressions.

### Pre-Commit Checklist
Before `git commit`, runs `cargo check --lib` and `cargo fmt -- --check`.

## Hook Configuration

Hooks are configured in `../settings.json` under the `hooks` section.
Individual hook scripts go in this directory.

## Related

- `.claude/settings.json` — Hook configuration
- `.claude/rules/kernel.md` — Kernel safety rules for pre-edit guards
