---
name: <skill-name>
description: <one-line scope>
category: <verification|debugging|safety|development|theory|release|meta|maintenance>
version: "1.0.0"
triggers: [<trigger phrase>]
permissions: [Read, Grep]
---
# <Skill Title>

## Scope

<When to use this skill and what it must not do.>

Register the file ID and matching frontmatter in
[skills.toml](../../.claude/skills/skills.toml); keep identity, description,
category, version, triggers and permissions consistent.

## Workflow

Follow [the authoritative engineering workflow](../../docs/guides/DEVELOPMENT.md#engineering-workflow)
for stage requirements, evidence, ownership, review and verification. Select
commands from [the command catalog](../README.md#verification): `verify` for
deterministic repository checks, `selftest` independently for automation, and
`strict`/`core`/`test` as applicable. `all`/Tier are explicitly selected
diagnostics, not substitute gates; independent security audits and the global
validator are separate. Record actual failures and unrun paths. Do not grant
proof, commit or release authority by instantiating this template.
