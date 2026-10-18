# Post-Session Checklist

会话结束前手动执行；当前 `settings.json` 未注册 `SessionEnd` hook。

## 检查项
1. `AGENTS.md`、`docs/status/PROJECT_STATUS.md` 与实际信任边界一致；历史采样和当前指标分别据其有日期证据记录，不用记忆文件或本清单更新指标。
2. `TransitionalStrictClosed` 与 `KernelTrustedClosed` 没有混用；不得把历史失败重新归因 xtask。
3. 按变更范围记录实际执行的 `verify`、独立 `selftest`、适用的 `strict`/`core` 与完整 workspace `test`；外部安全审计和全局质量门单独报告。`all`/Tier 只在显式选择时作为昂贵诊断，失败和未运行均如实说明。
4. 报告工作树相关修改；未获明确授权不 commit、push 或 tag。

## 更新流程
遵循 [`DEVELOPMENT.md#engineering-workflow`](../../docs/guides/DEVELOPMENT.md#engineering-workflow)，
不要把产品 A–H 阶段当作工程生命周期。

## 信任语义变化时更新
| 文件 | 内容 |
|------|------|
| `AGENTS.md` | 跨 agent 铁律、当前主线、禁止范围 |
| `docs/status/PROJECT_STATUS.md` | 完成度、信任指标、当前阻塞 |
| `docs/status/TRUST.md` / `docs/status/ROADMAP.md` | 接收语义和实施顺序 |
| `CLAUDE.md` / `.claude/rules/README.md` | 仅维护路由，不复制完整状态 |

## 有变更时更新
| 文件 | 触发条件 |
|------|---------|
| `docs/status/ROADMAP.md` | Phase 完成/规划变更 |
| `.claude/skills/*.md` | Skill 语义变更；自动化命令实现保持在 `xtask/`，`scripts/` 仅保留参考输入与设计模板 |
