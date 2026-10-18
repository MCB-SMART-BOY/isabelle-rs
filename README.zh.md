# Isabelle-rs

> Isabelle/Pure 风格的 Rust LCF 证明内核研究原型

## 这是什么

Isabelle-rs 实现了一个受 Isabelle/Pure 启发的 LCF 风格证明内核，重点研究：

- **定理不可伪造性** — `isabelle-kernel` 的私有构造边界与唯一 accepted-token 入口
- **Oracle 足迹追踪** — 遗留引擎中显式的 admit/oracle 传播，不升级为新内核权威
- **闭合定理验收** — exact-owner replay、声明认证和依赖验证
- **证明对象重放** — 严格内核当前 derivation 的重放；遗留 proofterm 仍只有局部覆盖

**它不是 Isabelle 的完整 Rust 重写**，不具备 Isabelle/HOL、Isar、PIDE 或 AFP 功能对等。

已批准的长期目标是针对固定 Isabelle2025 基线的完整 Rust 原生能力，包括
用户 ML 扩展、官方逻辑及工具。项目维护的自动化已切换到原生 Rust xtask，
独立检查与当前阻断见[迁移验证记录](docs/status/PROJECT_STATUS.md#current-delivery-state)。
B 包的九根官方参考观察只是历史参考侧证据。P2/P3/P4 的 kernel/ML
工作已按受审设计恢复实施，但完整 ROOT/HOL 兼容性尚未验收；工程质量门独立记录。
零 JVM 策略禁用本地参考 prepare/build/inventory，只保留离线比较；
官方运行时不是生产证明后端，solver cleanup 阻塞仍禁止新 solver 启动。
参见 [A–H 实施路线](docs/status/ROADMAP.md#approved-native-compatibility-program)；
长期目标不改变当前原型定位。

## 可信指标

2026-10-19 的 `core` 源码支撑复检从仓库捆绑的五个 HOL
理论文件各取 25 条带证明的候选，仍得到：

```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

只有 `HOL::TrueI` 的受审计源码投影获得了 owner-bound accepted token；
这不是完整 HOL 理论编译。2026-10-03 Gitlink 样本的 `1/125`
transitional、`0/125` kernel 是切换前历史记录。两个独立 CLI fixture
得到的 token 不计入当前 125 条。

当前严格内核已检查类型声明与 arity、basis 的完整 schema、保守定义和 owner
replay。legacy 完整 loader 按文件事务发布，只从 registry 导入已注册理论，
不负责通用磁盘依赖递归解析；拒绝未实现声明、多 imports 和不完整证明。
解析、证明结案及自动化出口要求完整输入和真实证据。

独立 Rust THM consumer 已有类型/变量变换、作用域导出、owner replay、
关闭、接受和再次引用的局部证据；ML runtime、Context 和原生插件也已有
局部实现。这不等于完整 ML `Thm: THM`、ROOT 或 HOL 兼容，且不增加上述
125 条采样计数。详见[THM 逐项清单](docs/status/NATIVE_THM_INTERFACE_INVENTORY.md)。

## 快速开始

先自行安装 Rust/Cargo（1.96 或更新），并取得本地 checkout。
`cargo +stable xtask install` 在该 checkout 构建，可选 `--check`、
`--release`、`--dir PATH`，不会自动升级 Rust、拉取或克隆仓库；构建产物
留在 Cargo target 目录，不复制到 PATH。不提供 curl-to-shell 或 PowerShell
远程安装。使用[命令目录](scripts/README.md#verification) 中维护的入口：
`cargo +stable xtask fast` 检查格式和编译，`strict` 检查严格内核，
`core` 运行 125 条采样，`docs` 检查文档。`tier2`/`tier3` 是显式受监督
的统计诊断，不属于默认测试；xtask 先锁定构建 worker，再以默认
600 秒墙钟、4096 MiB 每进程地址空间限制运行（可通过
`HOL_DIAGNOSTIC_TIMEOUT_SECS` / `HOL_DIAGNOSTIC_MEMORY_MIB` 覆盖）。
每次分配新日志目录并打印位置；查看其中的 `stderr.log` 和
`supervisor.json`。详见[诊断模式](scripts/README.md#report-only-scale-workloads)。
默认测试仍保留核心 125、全局 HOL 数据库、功能/信任回归与官方九个 HOL
文件不得出现 `SyntaxError` 的兼容性断言；诊断结束不等于完整理论编译或证明成功。

不带模式参数运行 `isabelle-rs` 会输出研究演示；`--lsp` 启动实验协议服务器，
不是完整 Isabelle/PIDE。构建与可信源码编译是不同入口，见下方 fixture 命令。

`cargo +stable xtask verify` 运行完整仓库代码/测试矩阵；`selftest` 独立验证
自动化，`test` 执行完整 workspace 测试并聚合失败。默认 Cargo 成员仍只有根
产品，裸 `cargo test` 不覆盖整个 workspace。`all` 包含昂贵的 Tier 诊断，
不代替完整质量门。行为证明、项目门及独立全局 validator 的顺序见
[统一工程工作流](docs/guides/DEVELOPMENT.md#engineering-workflow)。

运行独立可信 fixture：

```bash
cargo +stable run --locked --bin isabelle-build -- tests/fixtures/TrustedTrueI.thy
cargo +stable run --locked --bin isabelle-build -- tests/fixtures/TrustedPureIdentity.thy
```

第二条要求 `!!P::prop. PROP P ==> PROP P` 配合 `by assumption`；
旧 `(rule impI)` 不被接受。其他源形式不因名字相似而得到 token。

当前验证结果与剩余阻断见[交付记录](docs/status/PROJECT_STATUS.md#current-delivery-state)。
Rust THM consumer、ML 与离线证据修复的局部通过不等于完整原生兼容性验收。
自动化自检、历史官方参考运行及聚焦门通过均不代替完整仓库验证。
[2026-10-11 A 包记录](docs/status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
曾完成 workspace 测试并发现官方源码 `section` 前缀兼容性失败；
该记录及更早的 OOM、超时和扫描重试都只是各自当次的历史证据。

## 架构与边界

| 当前部分 | 职责 |
|---|---|
| `crates/kernel/` | 独立 `isabelle-kernel` TCB；声明认证、定理构造、owner replay 与验收 |
| `src/kernel/` | 根 crate 对严格内核 API 的 re-export |
| `crates/evidence/` | 离线参考证据校验与结构比较；不属于定理 TCB |
| `src/core/`、现有 HOL/Isar | 遗留引擎与部分前端；搜索、诊断或 legacy Strict 不等于 accepted token |
| `src/ml/`、`src/native_plugins/` | 原生 SML 与受约束 Rust 插件/host 边界；完整 ROOT/HOL 构建未验收 |
| `xtask/` | 独立自动化，不依赖产品或内核；不提供证明权限 |
| CLI/LSP/Session/WASM | 局部入口与实验适配器；不是完整 Isabelle/PIDE |

四层平台和 ISIP runtime 仍是目标设计；单个 sampled token 不是启动广泛
平台实现的充分条件。

## 文档

| 文档 | 描述 |
|------|------|
| [AGENTS.md](AGENTS.md) | 代理入口指南 |
| [AGENTS.zh.md](AGENTS.zh.md) | 代理指南（中文） |
| [项目状态](docs/status/PROJECT_STATUS.md) / [中文摘要](docs/status/PROJECT_STATUS.zh.md) | 当前定位、采样与验证边界 |
| [docs/isip/ISIP.md](docs/isip/ISIP.md) | ISIP 标准概述 |
| [实施路线图](docs/status/ROADMAP.md) | A–H 原生兼容目标、可信前置阶段与各自验收边界 |
[开发工作流](docs/guides/DEVELOPMENT.md#engineering-workflow) 与
[文档索引](docs/guides/DOCUMENT_INDEX.md) 提供任务和资料路由。

## 许可证

Isabelle-rs 是单独维护、受 Isabelle/Pure 启发的 Rust 项目，不是官方
Isabelle 发行版，也不声称获得 Isabelle 开发者或其所属机构的背书。
除文件或组件另有声明外，项目自行编写的代码、测试、自动化、文档和模板
按 [Apache-2.0](LICENSE) 提供，署名说明见 [NOTICE](NOTICE)。

第三方材料保留其适用条款：随附理论源码遵循
[theories/LICENSE](theories/LICENSE)，可选的 `isabelle-source/` 参考源码
保留其上游 `COPYRIGHT`。项目的 Apache 声明不替代复制或改编的上游材料
所适用的条款。[第三方声明](THIRD_PARTY_LICENSES) 保留两份 Isabelle
原始声明并标明适用材料；这些说明不对全工程的原创性、衍生作品性质或
不侵权作出法律认定，相关问题须结合具体材料和适用法律判断。

所有 workspace 包通过共享 Cargo 元数据声明 Apache-2.0；两个库包分别
携带 `LICENSE` 和 `NOTICE`。发行压缩包包含 `LICENSE`、`NOTICE` 和
`THIRD_PARTY_LICENSES`，但这不是完整依赖声明清单或合规认证。再分发源码
或二进制时，应满足实际纳入材料的适用条款，包括所要求的许可文本、署名
和修改说明；二进制分发还须包含实际依赖和原生组件所要求的声明。
