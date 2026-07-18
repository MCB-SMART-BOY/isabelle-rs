# Claude Code Hooks

Custom hooks for isabelle-rs development automation.

## Available Hook Points

| Hook | When | Use Case |
|------|------|----------|
| `PreToolUse` | Before a tool executes | Validate Edit/Write targets, enforce kernel rules |
| `PostToolUse` | After a tool executes | Auto-run tests, check for regressions |
| `Notification` | On system events | Alert on build failures |
| `SessionStart` | When session begins | Restore environment, check git state |
| `SessionEnd` | Manual checklist in this checkout | Cleanup and summary; never auto-commit without an explicit request |

## Planned Hooks

### Pre-Edit Kernel Guard
Checks if Edit targets `src/core/thm.rs` and warns about kernel safety rules.

### Post-Test Regressions
After `cargo test` completes, compares with baseline for regressions.

### Pre-Commit Checklist
Before `git commit`, run the appropriate `scripts/dev-check.sh` mode and the
Markdown/template policy. Hooks must not create commits autonomously.

## Hook Configuration

Hooks are configured in `../settings.json` under the `hooks` section.
`post-session.md` is not wired to an event in the current configuration; run it
manually before reporting completion.
Individual hook scripts go in this directory.

## Related

- `.claude/settings.json` — Hook configuration
- `.claude/rules/kernel.md` — Kernel safety rules for pre-edit guards
