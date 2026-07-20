# .claude — Isabelle-rs 工程配置

Claude Code 项目配置。所有 agent 先遵循根目录 `AGENTS.md`，再使用
**Rules → Skills → Commands** 分层路由。当前信任状态以
`docs/PROJECT_STATUS.md` 为准；本目录不复制历史验证数据。

## 架构

```
AGENTS.md                      ← 跨 agent 权威规则
CLAUDE.md                     ← Claude Code 兼容入口

.claude/
├── settings.json             ← 权限 + 环境 + hooks
├── rules/                    ← 领域约束 (globs 触发)
│   └── README.md             ← Claude 规则路由索引（非项目状态来源）
├── skills/                   ← 可执行工作流 (自然语言触发)
│   └── skills.toml           ← 技能路由元数据注册表（非项目权威）
├── commands/                 ← 斜杠命令 (薄包装 → skills)
├── agents/                   ← 专用审查子代理
├── hooks/                    ← 自动化钩子
├── memory/                   ← 持久化会话记忆
└── README.md                  ← 当前兼容层索引
```
跨 harness 的模板统一位于 `scripts/templates/`，不在 `.claude/` 内复制。

## 分层原则

| 层 | 职责 | 触发方式 |
|----|------|---------|
| **rules** | 领域约束 + 铁律 | `globs` 文件匹配 |
| **skills** | 可执行工作流 | 自然语言触发词 |
| **commands** | 快速入口 | `/command` |
| **agents** | 专用审查 | 手动指定 |
| **hooks** | 自动化 | 事件驱动 |

## 维护指南

1. **规则新增**: 使用 `scripts/templates/claude-rule.md`。
2. **技能新增**: 使用 `scripts/templates/claude-skill.md`，在 `skills.toml` 注册，并保持 frontmatter 的 `name`（对应 `id`）、`description`、`category`、`version`、`triggers` 和 `permissions` 与注册表一致；生命周期及依赖只由注册表描述。
3. **Phase 计划**: 使用 `scripts/templates/phase-plan.md`。
4. **可执行工作流**: 大型、可复用实现统一放在 `scripts/`；短说明片段可留在文档。
5. **会话结束**: 执行 `hooks/post-session.md` 检查清单。
