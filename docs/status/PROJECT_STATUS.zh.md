# Isabelle-rs 项目状态（中文摘要）

> 完整英文版见 [PROJECT_STATUS.md](PROJECT_STATUS.md)。本文为中文摘要。

## 当前定位

Isabelle-rs 是受 Isabelle/Pure 启发的 Rust LCF 证明内核研究原型，当前价值在于
定理构造边界、oracle 足迹、闭合定理验收和证明重放；目前远未实现完整
Isabelle/HOL 功能对等，不能将长期目标写成现有能力。

已批准的长期目标是固定 Isabelle2025 基线的完整 Rust 原生能力，包括用户
Isabelle/ML 扩展与其他官方逻辑及工具；这不是当前完成度。官方输出不是生产
后端或 Rust accepted token 的来源。零 JVM 策略已禁用本地参考
prepare/build/inventory，仅保留独立批准的离线证据比较。分阶段目标见
[实施路线](ROADMAP.md#approved-native-compatibility-program)。项目维护的自动化、
脚本测试和编辑提醒 hook 已统一到 Rust xtask。
B 的固定官方观察仍是历史参考侧证据。P2/P3/P4 的 kernel/ML 工作已按
P1 合同恢复实施，但完整 ROOT/HOL 及 ML `Thm: THM` 兼容性尚未验收。

## 可信指标

2026-10-19 的 `core` 源码支撑复检使用仓库捆绑的
`theories/HOL/{HOL,Orderings,Set,Nat,List}.thy`，每文件取前 25 条带证明的
候选；仅 `HOL::TrueI` 的受审计源码投影获得 owner-bound accepted token：

```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

这不是通用 HOL/Isar 理论编译。2026-10-03 基于 Isabelle2025 Gitlink
得到的 `1/125` transitional、`0/125` kernel 计数是切换前历史记录，
不等于当前捆绑样本。参见[英文现状](PROJECT_STATUS.md)。

独立 `isabelle-build` 已接受 `TrustedTrueI.thy` 和 `TrustedPureIdentity.thy`。
Pure 形式必须是 `!!P::prop. PROP P ==> PROP P` 配合 `by assumption`；
两个 fixture 都不计入 sampled 125，也不是通用 HOL/Isar 编译能力。

## 当前已实现边界

- `crates/kernel/` 是独立 TCB，`src/kernel/` 仅 re-export，`src/core/` 保留遗留路径。
- 类型声明与 arity、`SignatureId`、安装前完整 basis schema 检查、
  保守定义和 exact-owner replay 已实现；binder 的 Free 只作用于规则前提。
  当前身份版本见[严格内核不变量](../kernel/KERNEL_PRIMITIVES.md#global-invariants)。
- legacy parser 完整消费，loader 按文件事务发布；失败不发布 partial Theory，
  失败父项阻断后代，类型声明进入真实 signature。
- proof 结案必须有完整匹配目标的 Strict/checked 结果，按真实假设与 fix 导出；
  初始目标、Compat fact、未完成子证明均不算成功。
- simp 证书覆盖完整重写；Metis/Meson/ATP 核对目标与负担，坏 ATP 证据不能
  改跑本地搜索冒充 replay。这些局部边界不增加 sampled kernel 计数。
- legacy 搜索显式借用 `HolTheoremDb`，事务有自己的数据库并按更新接口失效缓存；
  不安全的伪静态数据库覆盖已移除，公开集合直接修改仍有缓存陈旧风险。
- 内置 LSP/Session 检查及 definition 查询由可复用直接子进程执行；
  只返回显示诊断，不提供 accepted token，也不是 OS 资源/权限沙箱。
- workspace 包含根产品、`isabelle-kernel`、`isabelle-evidence` 和独立 `xtask`，
  默认成员仅根产品；自动化不依赖产品或内核，evidence 不属于定理 TCB。
- `native_thm` 和 `native_thm_variables` 已通过公开受检 Rust API 演示变换、
  scope/owner replay、关闭、接受及再次引用；独立 consumer 不增加 sampled 125。
  逐项能力和缺口见 [THM 清单](NATIVE_THM_INTERFACE_INVENTORY.md)。
- 原生 SML/Context、编译期链接 Rust 插件、callback 类型证据与跨 VM 撤权已有
  局部实现/回归。离线证据处理保留未封口、缺成员等不完整结果；
  这些都不构成完整原生构建或新的官方运行证明。
- 本次实际 ROOT smoke 在 22 个文件后停于 `src/Pure/ML/ml_heap.ML` 的
  `PolyML.objSize` 未绑定值，尚未到达 Context；不能把代码中已有的
  Context 替换入口说成当前已执行成功。详见
  [本次核对证据](PROJECT_STATUS.md#source-backed-documentation-audit-and-delivery-plan-2026-10-19)。

## 历史检查点（2026-07-22）

- 递归 `is_concrete_type`（嵌套类型变量检测）
- `is_monomorphic_instance_of` 使用 `BTreeMap<TypeVarId, Ty>`
- 原子化 `AxiomDependencyId`（替换双重条目编码）
- `prove_true_i` 通过已验收 `True_def` + `theorem_ref` 链
- TCB 零警告门禁
- 10 个 TCB 攻击测试（5 polytype, 1 axiom dep, 4 definition）
- `ConservativeDefinition` 已通过 `DefinitionId` 原子化，存储在 `TheoryExtension::DefineConst`，重放时沿 owner 祖先链查找证书
- `PolyType::new` 验证参数排序一致性并要求每个声明的参数都出现在 body 中；`monomorphic_instance_matches` 依据参数授权实例

## 未完成

- 内核→遗留转换器使用 Debug 字符串
- 除 sampled `HOL::TrueI` 外，其他 sampled/legacy 前端仍未迁移到
  owner-bound accepted token；独立 fixture 不计入 sampled 125
- 完整 ROOT、typedef、class/sort 证明闭包、ML THM 接线及九根兼容验收仍有缺口，
  不能由局部内核/ML 通过或离线数据一致替代。
- solver cleanup 的宿主前置阻塞未解除；禁止新增 solver 启动或放宽隔离。

## 验证情况

最新验证和剩余阻断见[当前交付记录](PROJECT_STATUS.md#current-delivery-state)，
其中原生 THM、ML/证据修复、许可与文档维护分别记录实际范围。
`cargo +stable xtask verify` 覆盖完整仓库代码/测试矩阵，CI 的安全门独立且必需；
`release-check` 使用版本检查加 `verify`，不再隐式运行 Tier 诊断。
实施授权、局部行为通过、完整质量门与兼容验收是不同结论。

2026-10-19 的工程修复已通过完整 `cargo +stable xtask verify`：
10 个项目步骤全部通过，workspace 测试汇总为 2508 passed、0 failed、
9 个既有 ignored；严格 all-targets Clippy、`strict`、`selftest` 和 `core`
也已通过。两个独立 fixture 与官方 `HOL.thy` 的 `TrueI` 窄投影经实际 CLI 接受。
修复路径与证明边界见[工程修复记录](PROJECT_STATUS.md#engineering-quality-repair-2026-10-19)。
全局门及提交资格按最终不变工作树的实际输出和验证戳单独验收；
不把下方旧失败或本轮局部通过当作当前整树结论。

以下为修复前的[原生自动化历史验证](PROJECT_STATUS.md#native-rust-automation-verification-2026-10-14)：

- `cargo +stable xtask selftest`：156 项通过；xtask 的严格 Clippy 通过。
- 冻结参考的 SQLite 来源映射及六类解码/画像产物结构一致；合成差分输入
  对齐 18,895 条记录，仍因缺失 P0 证据返回 `BlockedPrerequisite`，不是证明成功。
- 真实 syscall smoke 为 34 个事件、零解码错误，不落盘原始 argv/环境；
  原生参考准备通过。原生 hooks 及实际 CLI 提醒已验证，未验证 Claude 事件加载。
- 新 Rust 入口已实际重建官方 Pure/HOL，并用该次构建完成九根清单导出，
  两次都退出 0、没有中断或 trace 解码错误。导出包含 67 个理论上下文、
  54,538 条命令及 18,895 个事实组成员；每次四个未解析相对路径仍不计入输入。
  这是官方参考运行，不是 Rust HOL 证明；原冻结 `closure.json` 未被改写。
- 当时文档链接、片段和模板子门通过，完整 `xtask docs` 被格式和产品编译阻断。
- 当时完整全局 validator 为 4 通过、4 失败：密钥及三项依赖扫描通过，
  格式、严格 Clippy、构建和测试失败，没有成功戳。
- 当时产品和内核测试缺少 `Sort` 导入；内核严格 Clippy 有 125 条诊断。
  暂停的内核/ML 代码及其格式差异未纳入初始自动化修复，产品监督测试未能执行。

旧 [A 包记录](PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11) 的 scoped
passes、官方源码兼容性失败和当时的 6 通过/2 失败不替代当前结果。
初始迁移运行没有新的 `strict`、`core` 或 accepted-token 成功计数。
macOS/Windows、真实无 rustup 主机及远端发布流程未验证；扫描通过沿用既有
范围和例外，不证明扫描范围以外安全，也不等于完整项目通过。

逐项任务遵循 [六阶段工作流](../guides/DEVELOPMENT.md#engineering-workflow)：
先行为证明和项目门，再运行完整 `~/.omp/agent/validate.sh`，分别报告
通过、失败、阻断和未运行项；`xtask all` 不是完整质量门。

## 下一步优先级

具体阶段、依赖、退出证据和回退边界见
[下一交付计划](ROADMAP.md#next-delivery-plan-2026-10-19)。
近期先恢复完整工程质量门，再从真实 ROOT 的首个失败点推进 ML/THM，
而不是增加 theorem-specific adapter 或扩大解析计数。后续 Pure/Isar、
九根 HOL、独立离线兼容与产品能力分别验收；保留现有严格接受边界、
JVM 禁令和 solver blocker。已修复的搜索上下文和直接子进程隔离不是待建项；
ISIP 仍为设计，单个 sampled token 不授权平台扩张。

## ISIP 平台路线

| 阶段 | 前置条件 |
|------|---------|
| 0: 设计 | 已有概述和 ISIP-000；ISIP-100、ISIP-300 等仍待编写 |
| 1: 可观察 | TCB 闭合 |
| 2: 事务式 | 阶段 1 |
| 3: 分支+Agent | 阶段 2 |
| 4: 证据感知 | 阶段 3 |
| 5: 多逻辑 | 阶段 4 |

详见 [ISIP 中文概述](../isip/ISIP.zh.md)。
