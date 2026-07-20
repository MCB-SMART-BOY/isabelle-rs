# Isabelle-rs

> Isabelle/Pure 风格的 Rust LCF 证明内核研究原型

## 这是什么

Isabelle-rs 实现了一个受 Isabelle/Pure 启发的 LCF 风格证明内核，重点研究：

- **定理不可伪造性** — 私有字段 + `ThmKernel` 构造边界
- **Oracle 足迹追踪** — 显式的 admit/oracle 传播
- **闭合定理验收** — 上下文绑定的 replay 和依赖验证
- **证明对象重放** — 最小化 derivation replay 原型

**它不是 Isabelle 的完整 Rust 重写**，不具备 Isabelle/HOL、Isar、PIDE 或 AFP 功能对等。

## 可信指标

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

## 快速开始

```bash
# 编译
cargo +stable check --locked

# 运行严格内核门禁
bash scripts/dev-check.sh strict

# 运行检查点门禁（strict + 聚焦 TCB 测试）
bash scripts/dev-check.sh checkpoint

# 运行 125 定理样本批处理
bash scripts/dev-check.sh core
```

## 架构

```text
isabelle-kernel (TCB, 零警告, 无异步)
    ↑
HOL 逻辑后端 (精化, 已检查判断)
    ↑
Isar 证明引擎 (部分实现)
    ↑
未来: ISIP 运行时 + LSP/MCP/Agent 适配器
```

## 文档

| 文档 | 描述 |
|------|------|
| [AGENTS.md](AGENTS.md) | 代理入口指南 |
| [AGENTS.zh.md](AGENTS.zh.md) | 代理指南（中文） |
| [docs/PROJECT_STATUS.md](docs/status/PROJECT_STATUS.md) | 项目状态和定位 |
| [docs/isip/ISIP.md](docs/isip/ISIP.md) | ISIP 标准概述 |
| [docs/isip/ISIP.zh.md](docs/isip/ISIP.zh.md) | ISIP 标准概述（中文） |
| [docs/ROADMAP.md](docs/status/ROADMAP.md) | 实施路线图 |
| [docs/README.md](docs/guides/DOCUMENT_INDEX.md) | 文档索引和分类 |

## 许可证
