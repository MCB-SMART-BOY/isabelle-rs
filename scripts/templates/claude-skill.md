---
name: <skill-name>
description: <one-line scope>
category: <development|verification|safety|maintenance>
triggers: [<trigger phrase>]
permissions: [Read, Grep]
---
# <Skill Title>

## Scope

<When to use this skill and what it must not do.>

## Workflow

1. Read `<authoritative docs and source>`.
2. Inspect the current worktree and baseline.
3. Implement the bounded change.
4. Run `scripts/dev-check.sh <mode>`.
5. Report trust metrics, tests, and remaining risks.
