---
description: CI/CD pipeline best practices. GitHub Actions, test automation, build matrix, deployment, cargo-release.
globs: ".github/**, scripts/**"
alwaysApply: false
version: 1.0
updated: 2026-05-29
---

# CI/CD Rules

> "If it's not in CI, it doesn't exist." — Continuous Integration mantra.

## 触发条件

修改 CI 配置、添加自动化、或规划部署 pipeline 时应用。

## 铁律

1. **每次 push 必须运行完整 CI** — 编译 + 测试 + lint + format
2. **CI 失败不允许合并** — 保护 main 分支
3. **CI 配置即代码** — `.github/workflows/` 中的 YAML
4. **快速反馈** — 基本检查 < 5 分钟
5. **确定性** — 相同 commit 多次运行结果一致

## CI Pipeline 阶段

```
Push / PR
  ├── Stage 1: Quick Checks (并行, < 2 min)
  │   ├── cargo fmt --check
  │   ├── cargo clippy -- -D warnings
  │   └── cargo check (no test compilation)
  │
  ├── Stage 2: Unit Tests (并行, < 5 min)
  │   ├── cargo test --lib core::thm
  │   ├── cargo test --lib core::unify
  │   ├── cargo test --lib isar::method
  │   └── cargo test --lib (其他模块)
  │
  ├── Stage 3: Integration Tests (< 10 min)
  │   ├── cargo test test_verify_all_core_files
  │   ├── cargo test test_verify_beyond_core (RUST_MIN_STACK=128M)
  │   ├── cargo test --test bnf_tests
  │   └── cargo test --test integration_tests
  │
  └── Stage 4: Extended Checks
      ├── cargo audit
      ├── cargo doc --no-deps
      └── cargo build --release
```

## GitHub Actions 模板

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

env:
  CARGO_TERM_COLOR: always
  RUST_MIN_STACK: 134217728  # 128MB

jobs:
  # Stage 1: Quick checks
  fmt:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - run: cargo fmt -- --check

  clippy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - uses: Swatinem/rust-cache@v2
      - run: cargo clippy -- -D warnings

  # Stage 2: Unit tests
  test-unit:
    needs: [fmt, clippy]
    runs-on: ubuntu-latest
    strategy:
      matrix:
        test-group:
          - core::thm
          - core::unify
          - core::simplifier
          - isar::method
          - isar::proof
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - uses: Swatinem/rust-cache@v2
      - run: cargo test --lib ${{ matrix.test-group }}

  # Stage 3: Integration tests
  test-integration:
    needs: [test-unit]
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - uses: Swatinem/rust-cache@v2
      - run: cargo test test_verify_all_core_files -- --nocapture
      - run: cargo test test_verify_beyond_core --lib -- --nocapture
      - run: cargo test --test bnf_tests
      - run: cargo test --test integration_tests

  # Stage 4: Extended checks
  extended:
    needs: [test-integration]
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - uses: Swatinem/rust-cache@v2
      - run: cargo audit
      - run: cargo doc --no-deps --document-private-items
      - run: cargo build --release

  # Release build (only on main)
  release-build:
    if: github.ref == 'refs/heads/main'
    needs: [extended]
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - uses: Swatinem/rust-cache@v2
      - run: cargo build --release
      - uses: actions/upload-artifact@v4
        with:
          name: isabelle-rs-linux
          path: target/release/isabelle-rs
```

## 构建矩阵

```yaml
strategy:
  matrix:
    os: [ubuntu-latest, macos-latest, windows-latest]
    rust: [nightly]  # edition 2024 requires nightly
    include:
      - os: ubuntu-latest
        target: x86_64-unknown-linux-gnu
      - os: macos-latest
        target: x86_64-apple-darwin
      - os: windows-latest
        target: x86_64-pc-windows-msvc
```

## 缓存策略

```yaml
- uses: Swatinem/rust-cache@v2
  with:
    cache-on-failure: true
    shared-key: "ci"
    # 缓存:
    #   - ~/.cargo/registry
    #   - ~/.cargo/git
    #   - target/ (增量编译产物)
```

## 分支保护规则 (GitHub 设置)

```
main 分支:
  ✅ Require a pull request before merging
  ✅ Require approvals (1)
  ✅ Require status checks to pass:
     - fmt
     - clippy
     - test-unit
     - test-integration
     - extended
  ✅ Require branches to be up to date
  ❌ Allow force pushes
  ❌ Allow deletions
```

## 自动化发布

```yaml
# .github/workflows/release.yml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  release:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - run: cargo build --release
      - name: Create Release
        uses: softprops/action-gh-release@v1
        with:
          files: target/release/isabelle-rs
          body_path: CHANGELOG.md
          generate_release_notes: true
```

## 检查清单

- [ ] CI 在所有 push/PR 时触发
- [ ] caches 正常工作
- [ ] 所有测试通过 CI (非仅本地)
- [ ] build matrix 覆盖主要平台
- [ ] `cargo audit` 在 CI 中运行
- [ ] 分支保护规则已启用
- [ ] 发布流程自动化
- [ ] CI 运行时间 < 20 分钟

## 反模式

| ❌ | ✅ |
|----|----|
| CI 跳过测试 | CI 运行完整测试套件 |
| 手动触发测试 | push/PR 自动触发 |
| 无缓存 | rust-cache 加速 |
| 单一平台测试 | 多平台构建矩阵 |
| "在我的机器上可以" | CI 是唯一的真相来源 |
| 忽略 CI 失败 | 修复或回滚 |
