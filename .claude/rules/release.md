---
description: Release engineering. Semantic versioning, changelog, cargo publish, git tags, release checklist, distribution.
globs: Cargo.toml, CHANGELOG.md, README.md, docs/**
alwaysApply: false
version: 1.0
updated: 2026-05-29
---

# Release Engineering Rules

> "If it hurts, do it more often." — Martin Fowler on continuous delivery.

## 触发条件

发布新版本或准备 release 时应用。

## 铁律

1. **每次发布前完整测试套件必须通过** — `cargo test` 零失败
2. **CHANGELOG 必须准确完整** — 每个用户可见变更都要记录
3. **版本号严格遵循语义化版本** — v0.x.y 的 x 对应 Phase 号
4. **Git tag 与 Cargo.toml 版本一致** — `git tag v0.7.0` 对应 `version = "0.7.0"`
5. **发布前必须代码冻结** — 至少 24 小时无新功能提交

## 版本号规则

```
当前: v0.7.0

MAJOR.MINOR.PATCH (semver)
  0  .  7  .  0
  │     │     └── PATCH: Bug fixes, 小改进
  │     └──────── MINOR: 新 Phase 完成, 新功能 (0.x 阶段)
  └────────────── MAJOR: 1.0 = 内核 API 冻结

计划:
  v0.7.3 → Patch fixes
  v0.8.0 → BNF 完整 + 全库验证
  v1.0.0 → LCF 内核 API 冻结 + Sledgehammer
```

## 发布检查清单

### 代码准备
```bash
# 1. 更新版本号
#    Cargo.toml: version = "0.7.3"
#    所有 docs: 版本标记更新

# 2. 测试
cargo fmt -- --check
cargo clippy -- -D warnings
cargo test
cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=134217728 cargo test test_verify_beyond_core --lib -- --nocapture

# 3. 文档更新
#    CHANGELOG.md: 版本标题 + 变更列表
#    README.md: 版本号, 统计, 特性表
#    docs/ARCHITECTURE.md: 完成标记
#    docs/ROADMAP.md: Phase 标记
#    docs/ISABELLE_COMPARISON.md: 覆盖率
#    .claude/rules/README.md: 版本号, 状态表

# 4. 构建验证
cargo build --release
cargo doc --no-deps

# 5. 检查
cargo package --allow-dirty  # 验证 package 内容
cargo publish --dry-run       # 验证 crates.io 上传
```

### 发布步骤
```bash
# 1. 提交所有变更
git add -A
git commit -m "release: v0.7.3"

# 2. 打标签
git tag -a v0.7.3 -m "v0.7.3: <简要描述>"

# 3. 推送
git push origin main
git push origin v0.7.3

# 4. 发布到 crates.io
cargo publish

# 5. GitHub Release
#    基于 CHANGELOG.md 创建 Release Notes
#    附上预编译二进制 (如适用)
```

## CHANGELOG 格式

```markdown
## v0.7.3 (YYYY-MM-DD)

### Added
- 新功能 (用户可见)

### Changed
- 行为变更 (非 breaking, 但值得注意)

### Fixed
- Bug 修复

### Deprecated
- 计划删除的功能

### Removed
- 已删除的功能

### Security
- 安全修复

### Performance
- 性能改进
```

## 发布频率

| 类型 | 频率 | 示例 |
|------|------|------|
| Patch | 按需 (bug fix) | v0.7.1, v0.7.2 |
| Minor | 每 Phase 完成 | v0.8.0 (Phase 34-36) |
| Major | 里程碑 | v1.0.0 |

## 发布通信

### 发布前 (1-2 days)
- [ ] 在 GitHub 上创建 milestone
- [ ] 标记所有包含的 issues/PRs

### 发布时
- [ ] 创建 GitHub Release + Release Notes
- [ ] 更新 crates.io 页面
- [ ] 更新 docs.rs 文档

### 发布后
- [ ] 验证 `cargo install isabelle-rs` 成功
- [ ] 验证预编译二进制 (如适用)
- [ ] 通知相关社区渠道

## 回滚计划

如果发布后发现严重 bug:

```bash
# 1. yank 版本
cargo yank --vers 0.7.3

# 2. 修复
git checkout -b hotfix/v0.7.4
# ... fix ...

# 3. 发布修复版本
# (按正常发布流程, 版本号 v0.7.4)
```

## 反模式

| ❌ | ✅ |
|----|----|
| 跳过 CHANGELOG | 详细记录每个用户可见变更 |
| 发布包含 known failures | 所有测试通过才发布 |
| 版本号跳跃 | 线性递增 |
| 发布后立即修改 tag | 创建新版本 |
| package 包含不必要文件 | 使用 `exclude` 精确控制 |
