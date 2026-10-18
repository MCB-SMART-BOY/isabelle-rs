# .claude — Isabelle-rs 工程配置

Claude 项目路由资料；先遵循根目录 [`AGENTS.md`](../AGENTS.md)，再使用
**Rules → Skills → Commands**。当前事实见
[`PROJECT_STATUS.md`](../docs/status/PROJECT_STATUS.md)、
[`TRUST.md`](../docs/status/TRUST.md)；长期原生兼容计划见
[`ROADMAP.md`](../docs/status/ROADMAP.md)。自动化由 Rust xtask 维护；历史官方
参考基线和当前阻断以状态文档为准，本目录不是第二份进度记录。

## 架构

```
AGENTS.md                      ← 跨 agent 权威规则
CLAUDE.md                     ← Claude Code 兼容入口

.claude/
├── settings.json             ← 自定义元数据 + 权限声明 + hook 定义（运行时支持需另验）
├── rules/                    ← 领域约束 (globs 触发)
│   └── README.md             ← Claude 规则路由索引（非项目状态来源）
├── skills/                   ← 可执行工作流 (自然语言触发)
│   └── skills.toml           ← 技能路由元数据注册表（非项目权威）
├── commands/                 ← 斜杠命令 (薄包装 → skills)
├── agents/                   ← 专用审查子代理
├── hooks/                    ← 配置说明与手动结束清单（未安装自动验证）
├── templates/                ← 指向 scripts/templates 的兼容入口，非另一套模板
├── memory/                   ← 忽略生成的会话记忆；不作为事实源
└── README.md                  ← 当前兼容层索引
```
维护版跨 harness 模板位于 `scripts/templates/`；现有 `.claude/templates/`
三个文件只提供旧 Claude 路径的链接指针，不复制模板正文。

## 分层原则

变更生命周期只遵循 [`DEVELOPMENT.md#engineering-workflow`](../docs/guides/DEVELOPMENT.md#engineering-workflow)；
它与 [`ROADMAP.md`](../docs/status/ROADMAP.md) 的 A–H 产品阶段不同。

| 层 | 职责 | 路由提示（非运行时加载保证） |
|----|------|---------|
| **rules** | 领域约束 + 铁律 | 文件范围 frontmatter |
| **skills** | 任务步骤 | 自然语言触发词与注册表 |
| **commands** | 快速入口 | `/command` |
| **agents** | 专用审查 | 手动指定 |
| **hooks** | 配置声明与手动清单 | 仅以实际注册及运行结果为准 |

## 维护指南

1. **规则新增**: 使用 [`scripts/templates/claude-rule.md`](../scripts/templates/claude-rule.md)。
2. **技能新增**: 使用 [`scripts/templates/claude-skill.md`](../scripts/templates/claude-skill.md)，在 `skills.toml` 注册；文件名对应注册表 `id`，frontmatter 的 `name` 对应注册表 `name`，并保持 `description`、`category`、`version`、`triggers` 和 `permissions` 一致；生命周期及依赖只由注册表描述。
3. **Phase 计划**: 使用 [`scripts/templates/phase-plan.md`](../scripts/templates/phase-plan.md)。
4. **可执行工作流**: 全部项目维护自动化统一在 `xtask/`；`scripts/` 仅保留官方参考探针输入与已分类的设计模板，文档不维护第二套执行逻辑。命令选择见 [`scripts/README.md#verification`](../scripts/README.md#verification)：`verify` 汇总确定性仓库级验证、`selftest` 独立验证 xtask；`strict`/`core` 是聚焦门与采样诊断，`test` 跑完整 workspace；`all`/Tier 为显式诊断，不替代独立安全审计及全局质量门。JVM-free 策略已禁用本地 `reference prepare/build/inventory`，仅能离线 `reference compare`；旧九根官方观察为历史，不是新原生验收。
5. **会话结束**: 手动执行 `hooks/post-session.md` 检查清单；`settings.json` 未注册 `SessionEnd`。自定义 `project`、`strategy`、`commands` 等字段只作项目元数据，不能证明 Claude Code 自动解释它们；hook 在宿主中的加载/环境注入未经实际验证。

权限标签与工具列表只是声明，不能替代当前任务授权；不得据此认定 `ask` 必然触发、
`deny` 能阻止所有联网方式或 hook 提醒具有安全门作用。跨 harness/provider 委派须遵守
[数据交付边界](../AGENTS.md#cross-harness-data-handoffs)，不得携带秘密或无关用户资料。
