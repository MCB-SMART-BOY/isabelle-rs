# .claude — Isabelle-rs 工程配置

Claude Code 项目配置。遵循 **Rules → Skills → Commands** 分层架构。

## 架构

```
CLAUDE.md                     ← 项目入口 (状态 + 铁律 + 快速命令)

.claude/
├── settings.json             ← 权限 + 环境 + hooks
├── rules/                    ← 领域约束 (globs 触发)
│   └── README.md             ← SOF: 项目状态 + 铁律 + 规则索引
├── skills/                   ← 可执行工作流 (自然语言触发)
│   └── skills.toml           ← SOF: 技能元数据
├── commands/                 ← 斜杠命令 (薄包装 → skills)
├── agents/                   ← 专用审查子代理
├── hooks/                    ← 自动化钩子
├── memory/                   ← 持久化会话记忆
└── templates/                ← 标准化模板
```

## 分层原则

| 层 | 职责 | 触发方式 |
|----|------|---------|
| **rules** | 领域约束 + 铁律 | `globs` 文件匹配 |
| **skills** | 可执行工作流 | 自然语言触发词 |
| **commands** | 快速入口 | `/command` |
| **agents** | 专用审查 | 手动指定 |
| **hooks** | 自动化 | 事件驱动 |

## 维护指南

1. **规则新增**: 使用 `templates/rule-template.md` 模板
2. **技能新增**: 使用 `templates/skill-template.md` 模板，在 `skills.toml` 注册
3. **Phase 计划**: 使用 `templates/phase-plan-template.md`，写入 `/root/.claude/plans/`
4. **会话结束**: 执行 `hooks/post-session.md` 检查清单
