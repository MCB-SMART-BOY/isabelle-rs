# Post-Session Checklist

会话结束时自动执行（由 `settings.json` hooks 触发）。

## 检查项
1. `CLAUDE.md` 状态表版本号 = `Cargo.toml` version
2. `.claude/rules/README.md` 状态表反映最新测试结果
3. 已知问题表与实际阻塞项一致
4. `git status` 干净（已提交或明确 WIP）

## 更新流程
```
CHECK → AUDIT → TEST → UPDATE → COMMIT
```

## 每次必更新
| 文件 | 内容 |
|------|------|
| `CLAUDE.md` | Project State 表、Known Issues、版本号 |
| `.claude/rules/README.md` | 状态表、已知问题、铁律 |

## 有变更时更新
| 文件 | 触发条件 |
|------|---------|
| `docs/ROADMAP.md` | Phase 完成/规划变更 |
| `docs/ARCHITECTURE.md` | 架构层变更 |
| `.claude/skills/*.md` | Skill 命令/工作流变更 |
