# Claude Code Hooks

Documentation for hook declarations in this checkout, not a guarantee that
this runtime consumes custom settings keys; runtime effectiveness was not verified.

## Available Hook Points

| Hook | Current configuration |
|------|-----------------------|
| `PreToolUse` | Calls `cargo +stable xtask hook pre-edit` to report `CLAUDE_TOOL_FILE_PATH` literally; not a kernel-rule guard. |
| `PostToolUse` | Calls `cargo +stable xtask hook post-edit`; only paths beginning `src/` trigger a Git query and a reminder when more than 10 tracked source files differ from HEAD. Does not run tests. |
| `Notification` | Empty hook list: no build alert. |
| `SessionStart` / `SessionEnd` | Not registered; use the manual checklist below. |

## Planned Hooks (not configured)

### Pre-Edit Kernel Guard
Would warn for edits to trusted kernel paths; not a substitute for code review.

### Post-Test Regressions
Would compare an actual test run with its baseline; not installed.

### Pre-Commit Checklist
Not installed. Before a user-authorized commit, run applicable project and
independent quality gates. No hook creates commits autonomously.

## Hook Configuration

Hooks are configured in `../settings.json` under the `hooks` section.
`post-session.md` is not wired to an event in the current configuration; run it
manually before reporting completion.
Implementation lives in `xtask/src/hooks.rs`, not embedded Shell scripts.
The existing `CLAUDE_TOOL_FILE_PATH` contract is retained: a missing variable
prints an empty pre-edit label and does not trigger a post-edit Git query; a
non-Unicode value is an input error. Pre-edit prints the value literally.
Only a value starting with relative `src/` triggers post-edit counting; absolute
paths do not match. Git runs in the invocation directory, with NUL-separated
names so newline-containing filenames count once. Git failures produce a
nonzero exit, not a zero-change result. This counts tracked changes against
HEAD, not untracked files or only edits made by the hook. Direct CLI behavior
does not establish that a host supplies the variable or loads these
declarations. Rust/Cargo and Git are prerequisites.

## Related

- [`../settings.json`](../settings.json) — actual hook configuration
- [`../rules/kernel.md`](../rules/kernel.md) — kernel rules for manual review
