# Post-Session Checklist

会话结束前手动执行；当前 `settings.json` 未注册 `SessionEnd` hook。

## 检查项
1. `AGENTS.md`、`docs/PROJECT_STATUS.md` 与实际信任边界一致。
2. `TransitionalStrictClosed` 与 `KernelTrustedClosed` 没有混用。
3. 已运行与变更范围对应的 `scripts/dev-check.sh` 模式。
4. `git status` 的所有修改均已报告；未获明确授权时不自动 commit 或 push。

## 更新流程
```
CHECK → AUDIT → TEST → UPDATE → REPORT
```

## 信任语义变化时更新
| 文件 | 内容 |
|------|------|
| `AGENTS.md` | 跨 agent 铁律、当前主线、禁止范围 |
| `docs/PROJECT_STATUS.md` | 完成度、信任指标、当前阻塞 |
| `docs/TRUST.md` / `docs/ROADMAP.md` | 接收语义和实施顺序 |
| `CLAUDE.md` / `.claude/rules/README.md` | 仅维护路由，不复制完整状态 |

## 有变更时更新
| 文件 | 触发条件 |
|------|---------|
| `docs/ROADMAP.md` | Phase 完成/规划变更 |
| `docs/ARCHITECTURE.md` | 架构层变更 |
| `.claude/skills/*.md` | Skill 语义变更；可执行命令保持在 `scripts/` |
