# Project Status and Positioning

This document is the canonical high-level status for Isabelle-rs. Agents should
read root [AGENTS.md](../../AGENTS.md) first, then this document before older
roadmap, architecture, gap-analysis, or session notes.

## Current Position

Isabelle-rs is not a full Rust rewrite of Isabelle. The accurate current
position is:

```text
A Rust implementation of an Isabelle/Pure-inspired LCF kernel
with explicit oracle footprints, closed-theorem acceptance,
and minimal proofterm replay.
```

Chinese summary:

```text
一个受 Isabelle/Pure 启发的 Rust 化 LCF 证明内核原型，
重点研究 oracle 足迹追踪、闭合定理接收条件、
以及 proofterm replay 复检机制。
```

The project is now beyond a toy parser: it has a meaningful trusted-kernel
prototype and a growing soundness attack-test suite. Its research value is not
feature parity with Isabelle/HOL. Its value is a smaller Rust-native setting for
studying theorem-construction boundaries, admitted/oracle accounting, closed
theorem statistics, and proof-object replay.

The approved long-term goal is native Rust compatibility with the fixed
Isabelle2025 baseline, including user Isabelle/ML extensions and all official
logics/tools, not just nine HOL files. This does not change the current research
prototype status. The official runtime is a differential reference only, never
a production proof backend. See the [staged program](ROADMAP.md#approved-native-compatibility-program);
automation package A does not authorize new proof rules or increase trust counts.

## Current Delivery State

Maintained project automation and its script tests now use native Rust
`cargo +stable xtask`. The cutover removes 33 replaced script files, including
the old installers, documentation gates, diagnostic supervisor and reference
tooling. Configured editor reminders also call native Rust hooks rather than
embedded Shell. Local install builds/checks an existing checkout; it does not
install Rust, update Git or copy binaries onto PATH. Official Isabelle/ML and
theory observer inputs remain reference-only, not a second automation stack.

The follow-on integrated delivery includes explicitly authorized source-quality
repairs and a complete repository verification entry point. The user subsequently
approved resuming the P1-designed native P2/P3/P4 closure implementation.
That authorization is not compatibility acceptance; earlier sampled counts and
official reference runs retain their original scope.

Package B's prior isolated Isabelle2025 reference run produced a frozen
nine-root observation baseline. This is **reference-side evidence**, not native
Rust execution or acceptance of the closure. The earlier Rust accepted paths
were the two standalone fixtures and sampled `HOL::TrueI` projection.
The [A-package verification record](#xtask-automation-cutover-2026-10-11)
retains its historical scoped passes and full-project blockers. Official
reference success did not resolve those blockers. Follow the
[engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow).

### Stable dependency and CI repair (2026-10-19)

本轮接续 `700dea1` 的工程交付，不把前一轮本地通过视为远端 CI 通过。
已按 crates.io 官方索引核对原有 23 个直接 registry 依赖；9 项升级至
最新非 yanked 稳定版，其余保留已是最新的版本。新增 `base16ct 1.0.0`
后共 24 个直接依赖；Wasmtime 使用稳定 `49.0.3`，不采用 `50.0.0-rc.1`。
锁文件仍含 Wasmtime/Cranelift 要求的传递 `sha2 0.10.9`，不是直接依赖漏升。
固定 Isabelle2025 Gitlink、内核直接依赖集合和 accepted-token 规则不变。

- SHA-1/SHA-256 的文本表示改为明确的 lowercase byte encoding，
  不改输入、摘要字节、前导零或身份算法；`base16ct` 不进入 TCB。
- `rusqlite` 启用 `fallible_uint`，沿用超出 SQLite 有符号范围时失败、
  读取负时间戳时拒绝的行为，不改缓存 schema。
- 升级后原有 LSP 两项和 Session 一项仍在首次请求时超时。
  真实 `--compute-worker` probe 对约 278 MB debug 二进制测得
  Hello 自哈希约 4932 ms，首次 Check 约 2 ms。保留父进程先哈希再启动、
  子进程独立哈希及原超时，只对 dev/test 的 `sha2` 包启用优化；
  无效的 CLI 分流改动已撤回。
- reference 的 Linux 执行代码不再进入其他平台编译；Unix 离线导入
  保留 descriptor-relative no-follow，非支持平台在导入前明确拒绝。
- GitHub Actions 与扫描工具升级到核对过的稳定版，保留八个独立必需任务、
  完整 `unmaintained`/`unsound` 审计范围和原有精确误报例外。
  Linux namespace 预检及 AppArmor 单程序授权边界见
  [开发流程](../guides/DEVELOPMENT.md#ci-release-and-submission)。
- launcher 诊断使用启动前保留的文件描述符，防止 worker 把日志替换成
  FIFO 或符号链接后阻塞父进程或诱导读取其他文件。

本轮保留 `load_offline_identity` 的局部长度例外：只在已有长审批流程前
增加平台拒绝，保持身份、路径、receipt 和预算检查顺序，不借 CI 修复扩大重构。

本轮已执行的定向证据：
- 真实 `--compute-worker` 完成匹配 executable hash 的 Hello 与 Check，
  退出 0；约 279 MB debug 二进制的 Hello 为 359 ms，Check 再用 2 ms。
  这是当前环境的单次 smoke，不是性能基准或资源隔离保证。
- 原有 LSP 两项、Session/compute worker 三项全部通过；升级后的
  codec/bootstrap/source-graph 与监督流程回归保留原功能断言。
- 恢复完整 `unsound = "all"` 后，`cargo +stable deny check` 的
  advisories、bans、licenses、sources 全部通过；传递重复版本仍报告 warning。
- CI/release/composite YAML 解析和 namespace Shell 语法检查通过；
  本地无 `actionlint`，不声称已运行该工具。
- 修复后新增日志替换回归实际完成 FIFO／symlink 替换并通过；独立
  correctness 与 security 审查的 findings 已关闭。
- `cargo +stable xtask strict`、`core`、`verify` 全部退出 0。
  `verify` 的十个步骤全部通过，workspace 汇总 2512 passed、
  0 failed、9 个既有 ignored；包含 all-targets 严格 Clippy 与固定源码检查。
- 真实 `isabelle-build` 接受 Pure identity、独立 HOL TrueI fixture
  和官方 `HOL.thy` 的受审计 TrueI 投影；采样仍为
  `KernelTrustedClosed: 1/125`、`TransitionalStrictClosed: 0/125`，
  不是整个 HOL 理论构建成功。

本地 Windows 交叉编译被缺少 MSVC `lib.exe` 阻断，不计作 Windows 通过。
真实 solver 的清理前置阻塞、JVM-free 策略和原生 ROOT/HOL 兼容缺口均保留；
依赖升级及 CI 通过不构成新的兼容验收。

### Engineering quality repair (2026-10-19)

本轮根据明确授权修复提交前的工程阻塞；下方文案与权属调查的失败记录
仍是各自时点的历史证据，不代表修复后的工作树结果。没有增加证明规则、
放宽 owner replay、扩大 ML 源码覆盖或解除真实 solver 的宿主清理阻塞。

- `xtask` 的 ZIP 依赖从 `6.0.0` 更新至锁定的 `9.0.5`，修复
  RUSTSEC-2026-0367 / 0368 / 0369；保留仅 `deflate` 的功能选择、
  固定归档路径、权限及拒绝覆盖策略，不新增漏洞豁免。
- `bicompose_candidate` 使用 `CompositionOptions` 汇集 flags、
  elimination、premise count 和仍为 **1-based** 的 subgoal index。
  `ObserverHostInputs` 汇集观察证据构造参数，本身没有认证或定理权力。
  全部调用方切换到新接口；内部参数组保留借用、原检查顺序和拒绝条件。
- `MlError.operation` 使用 `Box<str>`；`RootPrefixFailure.error` 与
  native source/reference 的嵌套 host 错误仅在失败路径装箱。
  原异常身份、source span、trace、停止信号与错误链保持不变。
- `SessionBuilder` 将缺失、失败、冲突合并及成环 import 报告为
  `DependencyError`，不再误报 `SyntaxError`；unsupported header 与
  duplicate theory 分别报告 `UnsupportedError`、`ConflictError`。
  它们仍失败且不发布 theory，真正的语法错误仍为 `SyntaxError`。
- 两个 supervision fixture 从硬编码 `/bin` 路径改用测试环境的 PATH；
  生产 solver 权限和清理策略不变。其余修改为等价 lint 修正、
  无调用私有代码清理与 workspace 格式统一，没有新增 ignore 或 lint 豁免。

本轮已实际运行两个 Rust THM consumer、三平台归档 smoke 和依赖审计。
原生 ROOT smoke 再次执行 22 个文件后，在 `ml_heap.ML` 的
`unbound value PolyML.objSize` 停止，原异常及两项取消 lease 的诊断均保留；
退出 1，未到达 Context，不是完整 ROOT/HOL 构建成功。

|本轮验证|实际结果与边界|
|---|---|
|`cargo +stable xtask verify`|10 个项目步骤全部通过：固定源码、格式、严格 all-targets Clippy、all-targets check、内核零警告、文档片段、链接、模板、firewall 与完整 workspace 测试。测试汇总为 2508 passed、0 failed、9 ignored；9 项为既有 ignore，不是本次豁免。|
|`cargo +stable xtask strict`、`selftest`、`core`|均通过；sampled 125 仍为 `TransitionalStrictClosed: 0/125`、`KernelTrustedClosed: 1/125`，没有扩大可信计数。|
|实际 `isabelle-build` CLI|两个独立 fixture 与官方 `HOL.thy` 的 `TrueI` 窄投影均接受；后者不是完整 HOL 理论编译。|
|修复路径回归|输入/加载/插件 82 项、supervision fixture 4 项及归档契约 6 项通过；三平台归档 smoke 仅证明归档内容与权限，不证明跨平台产品二进制执行。|
|`cargo +stable audit`|升级后的依赖审计通过；未添加漏洞豁免。|
|独立正确性与安全审查|本轮修复切片通过；composition 长函数的维护性意见及措辞意见已按具体理由记录并关闭。审查不是质量门运行结果。|

完整全局 `~/.omp/agent/validate.sh` 与提交门仍须针对最终不变工作树独立验收；
其结果以本轮交付输出及有效验证戳为准，不从上表的项目验证推断通过。

### Legal wording clarification (2026-10-19)

本次只调整第一方说明文字，不判断具体内容是否侵权，也不将整个 Rust
工程归类为衍生或非衍生作品。中英文入口、根及两个库包的 `NOTICE`、
`THIRD_PARTY_LICENSES`、agent 指引和相关状态记录统一区分：
项目自行编写内容的 Apache-2.0 声明、实际第三方材料的适用条款，以及
仍需按具体来源、使用方式和发布产物核对的问题。“单独维护”描述项目关系，
不是独立创作、权利归属或不侵权的证明。

核对依据为仓库许可原文及
[Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0.txt)
第 2–4、6–8 条，以及上游 Isabelle 的 BSD 声明（保存在
[第三方声明](../../THIRD_PARTY_LICENSES) 中）。不改许可正文、版权署名或
免责条款，不改变许可选择、依赖、打包逻辑或发布权限。规范性许可要求以
适用原文为准，本节不增设许可条件。

ISIP 名称及设计目标保留；总览与索引明确其为项目提出的草案，不声称
外部标准组织采纳或 Isabelle 官方背书。源码提交/上传与二进制再分发的
检查分开表述；质量门、依赖许可工具和本次文案审阅均不构成法律合规认证。
下方既有任务的测试、打包和审查记录仍为各自时点的历史证据，不是本次运行。

本次文案任务的实际检查：

|检查|结果与边界|
|---|---|
|受保护内容|5 份许可/版权原文、锁文件、4 份 manifest、依赖策略与两份 CI/release 配置共 13 个文件的 SHA-256 未变；`THIRD_PARTY_LICENSES` 内两份 BSD 原文完整保留，3 份项目 `NOTICE` 一致|
|读者路径|9 份改动 Markdown 的 177 个本地链接、其中 70 个标题锚点通过定向检查；未改 frontmatter|
|独立正确性 / 许可边界审阅|APPROVED / SCAN PASSED；未发现本轮需修复的问题，不是权属审计或法律意见|
|`cargo +stable test --locked -p xtask --test maintenance_contract`|6 passed，含法律文件正文、权限及归档拒绝行为|
|实际 `cargo +stable xtask package --artifacts` smoke|三平台归档中 9 个法律文件与根文件逐字一致；只用受控二进制输入验证归档，未运行跨平台产品，临时目录已清理|
|`cargo +stable xtask docs`|89 份文档的 snippets/links、4 个独立模板编译和 root check 通过；既有 workspace format 失败，整体退出 1|
|完整全局 validator（`RUSTUP_TOOLCHAIN=stable`）|4 pass / 4 fail；gitleaks、cargo check、trivy、cargo deny 通过；format、Clippy、cargo audit、cargo test 失败，整体退出 1，未生成成功验证戳|

全局失败仍包括既有格式与严格 Clippy 问题、`zip 6.0.0` 的
RUSTSEC-2026-0367 / 0368 / 0369（三项漏洞，其中 0369 为 critical 9.1），
以及两个 supervisor fixture 的 `ENOENT`（root lib：913 passed、
2 failed、8 ignored）。未为本轮文案任务修复这些无关问题或新增豁免；
文案审阅和打包检查不能抵消失败。全局验证期间未编辑仓库，完成后仅补记
本段结果；没有执行暂存、提交、上传或发布。完整依赖声明清单、具体材料
的权利链和实际发布的法律审查不属于本轮已验证内容。

### Source-backed documentation audit and delivery plan (2026-10-19)

追加核对覆盖第一方文档入口、status/trust、kernel、design/ADR/ISIP、
脚本目录、agent 路由及 CI/release 说明。按内核、ML/evidence 和产品适配器
分域对照关键实现与已有测试，修正下列有直接源码依据的偏差。
这是文档集合的横向核对，不是逐函数形式证明、171 项 THM 全量执行验收，
也不构成全库原创性或“法律无风险”的保证。

|核对点|当前源码事实与文档修正|
|---|---|
|ROOT 推进边界|`evaluate_root_with_context` 即使成功也只返回前缀/Context 进度；后续 ROOT 不执行。固定列表的下一文件是 `config.ML`，但本次实际运行更早失败，见下表|
|THM 接口|逐项表的“已实现”限定为 Rust 内核/consumer 映射，不是 ML opaque type、异常、callback 或完整签名已验收|
|Resolution|当前保守接口是 `resolve1_match` / `subst_premise`；旧 `KernelRules::bicompose` 包装器未导出，残留源码及其测试不算当前能力。另有的有界 `bicompose_candidate` 不等于完整 ML 搜索|
|WASM|源码注释明确已有 fuel，未设置显式 Store 内存限额或墙钟截止；proposal 数据类型未接入 tactic 交换/证明重建|
|产品入口|中英文入口区分默认 demo、实验 `--lsp` 与可信源码编译；修正 demo 中过时的 TCB 描述，不改执行逻辑。legacy 完整 loader 只查 registry 中的 imports，不提供通用磁盘依赖递归解析|
|权限与证据|P1 Host 是批准的目标合同；原生插件为受信进程内代码；离线来源绑定和差分不发放 theorem token|
|再分发|项目内容按所声明的 Apache-2.0 提供，实际 Isabelle 材料保留适用 BSD 条款；这些声明不判定全库原创性。现有归档只带项目及已识别 Isabelle 声明，实际依赖/原生库要求的 notices 仍须在二进制发布前核对并补齐|

|本轮实际行为检查|结果与限制|
|---|---|
|`cargo +stable run --locked --example native_root_smoke`|退出 1；22 个文件记录 `EXECUTED` 后停在 `src/Pure/ML/ml_heap.ML`，报 `elaborate: unbound value PolyML.objSize`；未到达 Context、THM 或 HOL。上下文和源 lease 完成返回取消，例程保留私有诊断；这不是完整 ROOT 成功，也不验证 solver cleanup|
|`cargo +stable run --locked --bin isabelle-build -- tests/fixtures/TrustedPureIdentity.thy`|退出 0，输出 `KernelTrustedClosed: identity`；只证明该独立 fixture，不增加 sampled 125 计数|
|`cargo +stable run --locked --bin isabelle-rs`|修正前后均退出 0；前次实际输出旧 `not the sole TCB`，修正后输出 isolated accepted-theorem TCB，并继续区分 strict fixture、legacy 示例及未实现的完整兼容；没有新增字符串断言测试|

本次补充审查的验证记录（不替代下方前轮工作流与许可任务的历史记录）：

|检查|实际结果与边界|
|---|---|
|第一方文档结构|88 份 Markdown、38 份 frontmatter、206 个本地标题链接通过；只证明结构，不是全文语义或法律保证|
|独立正确性 / 安全审查|APPROVED / SCAN PASSED；旧 `bicompose` 导出状态的 Minor 已关闭；不解除执行门失败|
|`cargo +stable xtask docs`|89 份文档的 snippets/links、4 个独立模板编译及 root check 通过；workspace format 失败，整体退出 1|
|`cargo +stable xtask verify`|7 个步骤通过、3 个步骤失败；固定源码、all-targets check、kernel zero warnings、snippets、links、templates、firewall 通过；format、strict Clippy、workspace tests 失败，整体退出 1|
|最终完整全局 validator（`RUSTUP_TOOLCHAIN=stable`）|4 pass / 4 fail；gitleaks、cargo check、trivy、cargo deny 通过；format、Clippy、cargo audit、cargo test 失败，整体退出 1；未生成成功验证戳|

完整 workspace 测试继续运行后有两个失败 target：root lib 为 913 passed、
2 failed、8 ignored，两个 supervisor fixture 仍因 `/bin/cat`、`/bin/true`
启动 `ENOENT` 失败；`integration_tests` 为 7 passed、1 failed，
`test_batch_verify_core_files` 在官方 `HOL.thy` 的 `Tools.Code_Generator`
import 不可用处报告 `SyntaxError`。其他 target 的通过不能抵消这些失败，
也不能把测试矩阵完成说成 HOL 构建成功。本次未单独运行 `xtask core`
统计门或完整原生九根闭包，不新增 sampled accepted 计数。

全局运行期间未再编辑仓库，末次结果未报告工作树变动；随后仅补记本节结果。
依赖门仍报告 `zip 6.0.0` 的
[RUSTSEC-2026-0367](https://rustsec.org/advisories/RUSTSEC-2026-0367)、
[RUSTSEC-2026-0368](https://rustsec.org/advisories/RUSTSEC-2026-0368) 和
[RUSTSEC-2026-0369](https://rustsec.org/advisories/RUSTSEC-2026-0369)，
其中最后一项为 critical 9.1。`cargo deny` 或 trivy 通过不抵消该失败。
本次没有更新依赖或加入忽略规则，也没有 stage、commit、push、tag 或发布。

后续顺序、依赖、退出证据和停止条件集中在
[下一交付计划](ROADMAP.md#next-delivery-plan-2026-10-19)：先处理工程基线，
再从本次实际 ROOT 失败点推进 ML/THM、Pure/Isar、九根 HOL，最后分别验收
离线兼容和产品能力。solver 宿主阻塞及本地 JVM 禁令继续保留。
本次不修复 ROOT 语义、依赖漏洞或既有广域失败，不新增证明规则、命令、
测试豁免或发布权限；完整质量门未通过前不提交上传。

### Documentation and workflow refresh (2026-10-19)

本轮盘点第一方文档、agent 路由和工作流，按当前源码校正英文/中文入口、
状态、路线、内核契约与设计文档。P2/P3/P4 已恢复实施不等于完整兼容验收；
Rust THM consumer、ML 局部回归、离线 evidence 和历史 sampled 计数分别记账。
当前身份编码路由到内核不变量，不沿用历史 `SignatureId v2` 摘要。

可维护的项目自动化已在前轮迁入 Rust `xtask`。本次未发现仍需提取的通用
Markdown 多步脚本，因此未为短命令、API 示例、设计模板或官方 ML 探针
新造命令或重复实现。补齐 `pinned-source` 的身份、干净 checkout 和 index
Gitlink 前置条件；保留 JVM-free 拒绝路径、离线批准边界和 solver blocker。
`.claude/settings.json` 只更新 strategy 描述，没有改 hooks、权限或模型。
CI/release 的实际执行配置、产品、TCB、测试和依赖均未在本轮变更。

| 本轮验证 | 实际结果与边界 |
|---|---|
| 第一方文档结构检查 | 检查 88 份 Markdown、38 份 frontmatter、188 个本地标题链接，未发现缺失锚点；不是全文语义正确性证明 |
| 配置和注册表解析 | settings JSON、两份 CI/release YAML 可解析；13 个 skill 的 frontmatter 与注册表字段一致；未验证 Claude 宿主事件加载或远端 CI |
| 实际原生 CLI smoke | `help`、`hook pre-edit`、`hook post-edit` 和 `pinned-source` 通过；hook 只是提醒，不是权限强制执行 |
| 禁用参考入口 smoke | `reference prepare/build/inventory` 均退出 2，报告策略拒绝；没有创建指定 workspace 或启动官方 runtime |
| `cargo +stable xtask selftest` | 194 passed |
| `cargo +stable xtask docs` | snippets、links、templates、root check 通过；workspace format 失败，整体未通过 |
| 独立正确性 / 安全审查 | APPROVED / SCAN PASSED；命令目录遗漏的 Minor 和当前身份摘要已修正；结论不代替执行门 |
| 首次完整全局 validator（stable） | 4 pass / 5 fail：gitleaks、cargo check、trivy、cargo deny 通过；format、Clippy、cargo audit、cargo test 失败，另报验证期间工作树变动；未生成成功验证戳 |

失败仍包括 evidence/kernel 严格 Clippy 诊断、`zip 6.0.0` 的三项已知漏洞，
以及两个 supervisor fixture 启动 `/bin/cat`、`/bin/true` 时的 `ENOENT`
（root lib：913 passed、2 failed、8 ignored）。这些是未解除的代码、依赖或
宿主前置条件问题，不因文档、自检或另一扫描器通过而消失。首次全局运行期间
合入了审查文档修正，其结果不能作为最终稳定工作树的验收证明。
本轮未运行官方 Isabelle/JVM、外部 solver、Tier 诊断或新的 sampled 验证，
没有提交、发布、修改锁文件、上游源码或许可原文。

### Project licensing and distribution notices (2026-10-19)

当时为项目自行编写的代码、测试、自动化、文档和模板统一声明 Apache-2.0，
文件或组件另有声明者除外。根 `LICENSE` 保持原文；新增 `NOTICE` 记录
项目署名和许可范围，`THIRD_PARTY_LICENSES` 保留两份实际 Isabelle 材料
的 BSD 声明。这些记录不替代第三方适用条款，也不对全工程的原创性、
权利归属或衍生作品性质作法律认定。

四个 workspace 包继承共享许可元数据；两个 library 包各携带完整
`LICENSE`、`NOTICE`。发行打包入口给三种平台归档加入根目录的
`LICENSE`、`NOTICE`、`THIRD_PARTY_LICENSES`，保留二进制内容及权限、
缺件拒绝、符号链接拒绝和禁止覆盖已有归档的行为。`deny.toml` 只把两个
zstd BSD 例外对齐当前锁定版本，没有更新依赖、扩大许可允许列表或添加
漏洞忽略。`Cargo.lock` 和两份上游许可原文的 SHA-256 与任务起点一致。

| 本轮验证 | 实际结果与边界 |
|---|---|
| Cargo locked/offline metadata | 四个包均为 Apache-2.0 |
| 两个 library 的实际 `cargo package --no-verify` | `.crate` 中的 `LICENSE`、`NOTICE` 与根文件逐字节一致；未执行打包后的独立编译验证 |
| 主包 `cargo package --list` | 包含四份法律文件，排除 `isabelle-source/`；不是主包完整打包证明 |
| 实际 `xtask package` CLI smoke | 三种归档中的九个法律文件与根文件逐字节一致；使用受控二进制输入，没有运行跨平台产品 |
| `maintenance_contract` / `xtask selftest` | 分别 6 / 194 passed；归档测试已保护正文完整性、权限及原有拒绝行为 |
| 本次两个 Rust 文件的定向 rustfmt | 通过 |
| `cargo deny --locked check licenses` | `licenses ok` |
| 独立正确性 / 安全审查 | APPROVED / SCAN PASSED；正文断言的 Minor 已修复并复核关闭 |
| `xtask docs` | snippets、links、templates、root check 通过；全库 format 失败 |
| xtask 定向严格 Clippy | 未通过：既有 `reference/compare.rs` lifetime 与 `decode_bootstrap_events.rs` nested-if 诊断 |
| 完整全局 validator（stable） | 4 pass / 4 fail：gitleaks、cargo check、trivy、cargo deny 通过；format、Clippy、cargo audit、cargo test 失败，未生成成功验证戳 |

全局剩余失败包括既有全库格式问题、evidence/kernel 严格 Clippy 诊断、
`zip 6.0.0` 的三项已知漏洞，以及两个 supervisor 测试启动 `/bin/cat`、
`/bin/true` 的 `ENOENT`（root lib：913 passed、2 failed、8 ignored）。
许可检查通过不消除这些失败，也不构成全库原创性或完整再分发合规保证。
实际发布前仍须按构建产物补齐依赖和原生库的许可文本与声明。本轮未提交、
发布、运行官方 Isabelle 或外部 solver；未扩大许可任务以修复无关问题。

### ML runtime and evidence semantic repairs (2026-10-19)

本包只修复跨 VM 撤权、静态类型证据、异常回调与离线证据协议的一致性，
不修改内核规则、owner 边界、依赖或固定源码基线。对照固定 Isabelle2025
以及本轮读取的官方 revision
[`7c3c7e030c7d`](https://isabelle.in.tum.de/repos/isabelle/rev/7c3c7e030c7d)，
并按 [Poly/ML 异常接口](https://polyml.org/documentation/Reference/PolyMLException.html)
区分真实语义错误与测试前置条件错误。

- FileHostBridge 的跨 VM 绑定失败撤销两侧生命周期；公开 `Vm::apply`
  对外来 Closure、CurriedClosure 和 partial callable 先撤权，再做类型查询。
- 内部 callback 从认证参数位置及 tuple 字段取得调用实例类型，不再用
  闭包指针首次匹配。composition、Context data、printer、compiler 与
  Basis 回调沿用静态证据；公开无类型、多态、weak、opaque 拒绝仍保留。
- `traceException` 的普通异常 reporter 返回值、packet 身份及 ref 副作用
  按真实接口核对；不可恢复停止不交给普通 handler。负数 trim 在第一次
  应用报 `Subscript`，后续 partial 值携带已认证类型。
- 测试前置条件校正包括：先通过 SML 编译得到外来 theory、修改未 finished
  theory 的 data 后再 finish、读取 ref 快照而非将 ref 当整数，以及为
  单文件 `ml_pretty.ML` 提供 ROOT 的 `implode = String.concat`。
  保留跨 VM、重复祖先、packet 和副作用的拒绝/结果断言。
- GC 与插件回归区分两种失败：同 VM 非法 weak 赋值拒绝且状态不变；
  外来 option 使接收 VM 停止。独立构建自身停止不牵连另一构建，而外来
  VM 访问 registry 属于跨域误用，须撤销双方并拒绝后续服务。
- bootstrap 使用六字段 frame、七字段 load payload 和真实 `observer/event`；
  原始身份、phase、源摘要、field、typed payload 均核对。空源码合法但仍验
  hash，未 sealed 仍不完整。命名定理 singleton 保持 index 0，synthetic
  多成员组使用 1..N，缺成员与缺覆盖仍阻断兼容成功。

本包定向执行结果：

|验证|实际结果|
|---|---|
|9 个 ML contract/security targets|167 passed；保留 3 项既有编译 warning|
|GC 与插件撤权 contracts|45 passed；同 VM 不变更、独立构建隔离及跨域双停均保留|
|evidence lib + reference_protocol|53 passed|
|bootstrap v2 decoder|6 passed|
|临时原生 API smoke|composition 打印 `42`；reporter 返回 `7` 且仅调用一次；packet 保留；trim 边界、不可捕获停止及双域撤权通过|
|离线 decoder → verifier → comparison smoke|非空 bootstrap registration 可导入；sealed 合成输入匹配，unsealed 为 `BlockedPrerequisite`，错误源摘要拒绝|
|`cargo +stable xtask selftest`|194 passed|
|`cargo +stable xtask strict`|13 个独立子门通过；workspace format 失败，整体未通过|
|`cargo +stable xtask docs`|snippets、links、templates、root check 通过；workspace format 失败|
|`cargo +stable xtask verify`|固定源码、all-targets check、内核零警告、文档三门及 firewall 通过；format、strict Clippy 和 workspace tests 失败|
|完整 `~/.omp/agent/validate.sh`（stable）|3 pass、5 fail：gitleaks、cargo check、trivy 通过；format、Clippy、cargo audit、cargo deny、cargo test 失败；未发布成功验证戳|

复审发现的外来 callable 顺序、共享多态 callback 实例、bootstrap channel
和空源码四项均有失败前与修复后的定向证据。独立正确性复核为 APPROVED，
安全复核为 SCAN PASSED：均仅限本包静态 delta，未发现新的有证据 finding，
不代替执行门或来源批准。此前 THM 包记录的失败保留为历史，不能把本包修复
追溯为此前已通过。

最终整库矩阵中，本包受影响的 ML、GC、插件、evidence 与 decoder suites
均通过；剩余失败测试 target 为 root `--lib` 与 `integration_tests`：
两项 supervisor fixture 启动固定 `/bin/cat`、`/bin/true` 时发生 `ENOENT`，
HOL 批量加载则报告缺少 `Tools.Code_Generator`。本包没有改动这些路径，
没有删断言或新增 ignore；solver cleanup 运行前置阻塞仍未解除。
strict Clippy 还报告 evidence 的 6 项和 kernel 的 13 项既有 lint；
workspace format 仍失败。不能把定向语义修复视为整库交付验收通过。

本次全局审计结果单独记账，不沿用此前 THM 包的四项漏洞计数：
`cargo audit` 在当前锁定的 `zip 6.0.0` 报告
[RUSTSEC-2026-0367](https://rustsec.org/advisories/RUSTSEC-2026-0367)、
[RUSTSEC-2026-0368](https://rustsec.org/advisories/RUSTSEC-2026-0368) 和
[RUSTSEC-2026-0369](https://rustsec.org/advisories/RUSTSEC-2026-0369)，
最高为 critical 9.1，建议升级到 `>=9.0.0`；这不是本包可利用性复现。
`cargo deny` 的失败来自 `zstd-safe 8.2.0`、`zstd-sys 2.1.2+zstd.1.5.7`
未匹配仍限定旧版本的 BSD-3-Clause 例外；其 advisories/bans/sources 通过。
依赖与许可修复须由项目依赖维护者在下一次发布前单独处理，本包不放宽许可
策略，也不以 trivy 通过覆盖另外两道依赖门的失败。

函数跨度按 rust-analyzer 的完整签名至结束括号核对。`apply_native`
保留 65 行例外：集中完成同一次 native partial 状态的类型代换及参数累积，
完整调用、结果/异常收束已拆为独立 helper；不再为五行差额拆散这些状态。

本机未运行 Isabelle/JVM/solver/bwrap，未改 Gitlink；官方 observer/patch
变更仍需要新的包外来源批准。离线合成输入不认证官方执行，不增加 sampled
trusted count，也不表示完整 ROOT、THM 或 HOL 兼容已经验收。

### Rust THM type and variable transformations (2026-10-19)

本包在现有 Rust 内核中实现统一的固定类型/项泛化、认证对象泛化、
显式 `export_scope` 与来源回放后的 `incr_indexes`，不增加 ML facade
或 theorem-specific 规则。旧 `(Name, Ty)` 列表和自动分配索引的泛化入口
已移除；所有调用者使用名称集合和显式 fresh index。精确语义见
[变量变换合同](../kernel/KERNEL_PRIMITIVES.md#generalize--固定类型与项的统一泛化)。

外部调用示例
[`native_thm_variables`](../../crates/kernel/examples/native_thm_variables.rs)
已实际运行：从局部固定类型、`x`、`y`、`f` 推导并泛化，
将 `(x ≡ y) ⟹ (f x ≡ f y)` 导出到 owner 后接受为一个 generic token；
在两个后代分支中复用该 token，分别使用已声明的不同类型与常量，
完成实例化、组合、转移、关闭接受，再引用并重新接受。
两分支的完整结论分别是 `(p_left ≡ q_left) ⟹ (g_left q_left ≡ g_left p_left)`
及对应 `right` 版本；每个实例依赖精确保留 generic theorem 身份。
所有 owner 均无 `LogicBasis`。具体类型实例化后保留的额外空 sort
须经既有 `strip_shyps` 消解，不能直接删除 payload 字段。

回放仅按精确 typed Free 和词法来源授予临时权限；类型变换、RHS 复制
及相同 key 合流均保留 binder 来源。退出 binder 撤销其全部派生权限，
但不撤销独立外层授权。`ExportScope` 完整回放来源后在空 local 的 owner
重认证输出；proof-only 局部参数仍由完整 proof 的索引上界确定性 freshen。
真实 H、sort/flex/pending 义务及依赖不因泛化、导出或索引变换消失。

本轮曾稳定复现并修复外层 binder 授权丢失、同时类型/项替换的 RHS 授权
错配，以及转换后 binder 权限逃逸。回归分别覆盖合法接受与非法拒绝。
新增中间类型/sort 篡改和隐藏历史高索引边界也已运行通过。
根回归中仅因同名不同类型而拒绝嵌套 abstraction 的旧断言已移除：
固定 `Pure/thm.ML` 按完整 typed term 执行 `abstract_over`，新的真实应用
回归检查两个绑定均保留、完整命题正确且不向 owner 发布 Free，
而不是重新固定旧单名称授权表的偶然限制。

独立正确性复核已关闭发现的问题；独立安全复核重新读取了最终
`FreeGrant { name, ty, scope_depth }` 实现，确认此前 binder 派生授权泄漏
已修复、未发现新的有证据支持的 finding。两项均为静态审查，
不能代替实际测试或全局依赖审计。

本轮项目验证记录：

|检查|实际结果与边界|
|---|---|
|`native_thm_variables` 与原 `native_thm` executable|均通过完整实际调用闭环；输出、owner 与依赖由程序内断言检查|
|内核单元及集成测试|最终 `cargo +stable test --locked -p isabelle-kernel --no-fail-fast`：200 项单元、224 项集成测试及 8 项 compile-fail doctest 通过；另 1 项既有 doctest ignored|
|新增变换、scope、binder 及 consumer 回归|定向通过；中间篡改 2 项、隐藏索引 2 项、binder 6 项；旧根 acceptance 迁移后 18 项通过|
|新增 Rust 模块的只读格式检查|通过；不表示整个既有工作树格式通过|
|`cargo +stable xtask strict`|13 项通过，只有 workspace format 失败；源码边界、acceptance、内核测试与 firewall 均通过|
|`cargo +stable xtask verify`|固定源码、all-targets、内核零警告、文档/链接/模板与 firewall 通过；格式、strict Clippy、workspace tests 失败|
|`cargo +stable xtask docs`|snippets、links、templates 与 root check 通过；workspace format 失败|
|完整 `~/.omp/agent/validate.sh`|3 pass、5 fail：gitleaks、cargo check、trivy fs 通过；format、Clippy、cargo audit、cargo deny、cargo test 失败；未发布成功验证戳|

`verify` 的失败仍包括原有 10 个测试 target：evidence `reference_protocol`、
root lib、`integration_tests`、六个 ML contract/host target，以及 xtask
`reference_decode_bootstrap_v2`。没有把它们改为 ignored 或删除失败断言。
本包新增的 `check_generalize_index` 嵌套条件 lint 已按等价 let-chain 修正；
其他既有 lint 不在本包范围内。

全局门的 `cargo audit` 仍报告 4 项依赖漏洞：`wasmtime 36.0.17` 的
`RUSTSEC-2026-0363`（medium，6.2），以及 `zip 6.0.0` 的
`RUSTSEC-2026-0367`（high，7.3）、`RUSTSEC-2026-0368`（输出未提供评分）、
`RUSTSEC-2026-0369`（critical，9.1）。`cargo deny` 也因 wasmtime advisory
失败；trivy 的通过不能抵消这些失败。公告链接与影响边界保留在下节
[首个闭环记录](#first-native-rust-thm-closure-2026-10-18)。
本包未修改依赖、锁文件或忽略规则，未验证本 consumer 对漏洞的可利用性。
依赖修复需由维护者另行授权并在解除全量交付阻塞前完成。
全局 `cargo test` 在 evidence `reference_protocol` 失败后停止；
完整 workspace 的其余失败以此前聚合执行的 `xtask verify` 为准。

本包不代表完整 Isabelle/ML THM、ROOT、HOL 或九根兼容验收；
不计入 bundled 125-theorem sampler。未启动 Isabelle/JVM、solver 或
bwrap；既有 solver cleanup 阻塞未解除，既有广域失败不因局部通过消失。

### First native Rust THM closure (2026-10-18)

首个外部 Rust consumer 已由现有 `isabelle-kernel` 公开受检 API 完成：
认证 type/term/prop、从真实 `H=[p ≡ q]` 开放推导、将 schematic
`f:prop⇒prop` 实例化为已声明的 `g`、Pure bicomposition、显式后代
owner transfer、解除 H、关闭、接受，再在新 owner 引用并重新接受。
最终命题恰为 `(p ≡ q) ⟹ (g q ≡ g p)`；没有安装 `LogicBasis`，
首次 token 无依赖，引用后的 token 恰有一个 theorem 依赖。

运行入口为
`cargo +stable run --locked -p isabelle-kernel --example native_thm`。
[consumer](../../crates/kernel/examples/native_thm.rs) 与
[跨步骤回归](../../crates/kernel/tests/native_thm_closure.rs) 共用非可信示例支持模块；
没有新增生产 theorem facade、公开内核 API、推理规则或公理。
内部 `theory::tests::theorem_ref_reaccepted_records_exact_source_dependency`
通过真实 reference→accept 检查精确 `DependencyKind::Theorem + source.id()`，
不是只检查数量，也不解析 Debug。

本次实际行为证据：

|检查|观察结果|
|---|---|
|`native_thm` executable|完成全部结构断言；输出首次依赖 0、重新接受后的 theorem 依赖 1。|
|第一轮 `native_thm_closure` 与六个相邻 kernel suites|98 passed；当时新增闭环/跨步骤回归为 10 项。|
|精确 reference dependency 单元回归|1 passed。|
|补入根级 `Bound(0)` 拒绝后的 `native_thm_closure`|11 passed；完整 workspace 运行中亦全部通过。|
|新增 Rust 文件的只读格式检查|通过。|
|独立正确性与安全复审|正确性 APPROVED；一处清单路径 Minor 已修复并复核关闭。安全复审未发现本轮新增问题；不替代依赖审计。|
|`cargo +stable xtask strict`|失败：workspace format 不通过；其余子门全部通过，包括内核零警告、firewall、接受/replay/source-boundary 与 kernel package tests。|
|`cargo +stable xtask docs`|失败：workspace format 不通过；snippets、links、templates 子门通过。|
|`cargo +stable xtask verify`|失败：format、strict Clippy 和 workspace tests 不通过，10 个测试 target 中 26 项失败；pinned source、all-targets check、内核零警告、firewall 和文档子门通过。|
|完整 `~/.omp/agent/validate.sh`|3 pass、5 fail：gitleaks、cargo check、trivy fs 通过；format、Clippy、cargo audit、cargo deny、cargo test 失败。未生成成功验证戳。|

拒绝路径区分错误 owner、仍有 H、RHS context、根级 `Bound(0)` 与未绑定 local Free；
flex 和 extra sort 经过 transfer 与 H 解除后仍分别以
`UnresolvedFlexPairs`、`ExtraSortHypotheses` 拒绝关闭，避免 H 掩盖错误。
相邻回归保留非法 sort 实例化的 `TypeSortMismatch`、局部固定类型的
`LocalTypeScopeEscape`；合法 forall/abstraction transfer 不向 owner 发布 Free。
上述局部通过不表示集成交付通过。完整门运行后仅补记本文证据，
未继续修改生产实现、测试契约、依赖或忽略规则。

本轮广域阻塞（不在本 consumer 工作中修复）：

- `reference_protocol` 的 named-member 负例遭遇
  `invalid official theorem index sequence`；
  `reference_decode_bootstrap_v2` 遭遇 `expected 7 TLV fields`。
- `integration_tests` 的官方 HOL 导入缺少 `Tools.Code_Generator`；
  `isabelle-rs --lib` 的两个普通子进程回归启动返回 `ENOENT`。
  这些回归不是实际 solver/bwrap smoke，不能解除既有 cleanup 阻塞。
- `ml_basis_contract`、`ml_bootstrap_contract`、`ml_bootstrap_host`、
  `ml_context_contract`、`ml_exception_contract`、`ml_text_basis_contract`
  存在 parser/type、callback 证据、外来 VM 撤权与异常语义失败。
  不把这些错误当作 THM consumer 的通过证据，也不扩大本轮范围修复。
- Clippy 在既有 `bound_proof` 与 evidence 实现上失败；定向 consumer
  Clippy 也被 `isabelle-kernel` 的 13 项既有 lint 错误阻塞，
  不能将编译零警告或新增文件格式通过写成 lint 通过。
- `cargo audit` 报告 `wasmtime 36.0.17`
  [RUSTSEC-2026-0363](https://rustsec.org/advisories/RUSTSEC-2026-0363)，
  以及 `zip 6.0.0` 的
  [RUSTSEC-2026-0367](https://rustsec.org/advisories/RUSTSEC-2026-0367)、
  [RUSTSEC-2026-0368](https://rustsec.org/advisories/RUSTSEC-2026-0368)、
  [RUSTSEC-2026-0369](https://rustsec.org/advisories/RUSTSEC-2026-0369)；
  最后一项为 critical（9.1）。`cargo deny` 的 advisory 门因 wasmtime
  失败，bans/licenses/sources 通过。`trivy` 通过不覆盖这些 RustSec 失败；
  锁文件命中也不单独证明本 consumer 可触发漏洞。依赖更新需另行定界。
- 全局 `cargo test --workspace` 在 `reference_protocol` 失败后停止；
  更完整的失败集合以上述 `xtask verify` 的 no-fail-fast 结果为准。

[固定 THM 逐项清单](NATIVE_THM_INTERFACE_INVENTORY.md) 对照 171 个官方声明，
区分受检内核、非可信派生算法与 ML 表示/效果；完整 `Thm: THM`、typedef、
ROOT、HOL 和九根兼容仍未验收。本 consumer 不进入 bundled 125-theorem
sampler，不改变既有 sampled trusted count。solver cleanup 阻塞继续保留；
不得以本例或 launcher 认证拒绝测试宣称真实 solver 已安全运行。

### JVM-free architecture direction (2026-10-16)

用户明确要求零 JVM 和 Rust 原生插件架构。新的 JAR 准备、官方 launcher、
reference overlay 扩展及相关 supervisor 实施已经冻结；CLI 的
`reference prepare/build/inventory` 在工作目录准备或启动外部程序之前拒绝，
`reference compare` 仅保留离线数据比较。既有源码与历史参考记录未删除，
不能把冻结中的 v2 实现或旧运行记录写成新的完整参考证据。

用户已批准编译期链接的 Rust 原生插件架构，并选择“分离原生构建与兼容验收”。
原生发布仍要求真实源执行、Rust 内核接受和全部任务排空，但不再以前置官方
`Matched` 为条件；完整官方兼容仍须通过独立、包外批准来源的离线证据比较。
新原生结果使用独立 `native_build_result` purpose，不能改写旧兼容报告的成功含义。
该方案已通过独立设计审查，插件、ML 消费者和原生构建接线仍在实施；
不表示完整 ROOT、九根或兼容验收已通过，也不扩大内核推理权限或 solver 运行授权。

固定 ROOT 的 `Resources.check_scala_function` 会在 ML 反引展开时校验
服务名，包含尚不能用 Rust 重实现的 JVM 专属服务。用户另批准这些明确
服务的仅加载期禁用延迟链接，不允许将其注册为可调用服务；真实调用失败。
用户同时批准 `lzma-rust2` 与 `zstd`/静态 `libzstd` 的窄依赖边，
用于实际 XZ/Zstd 服务，不授权外部运行进程或新增定理规则。
此前独立审查指出的 class predicate 普通定义、`SortErased` 完整类型身份、
导出前提重排及 proof-only 索引分配问题，已完成定向修复；下节记录该
检查点的行为证据，不把它当作随后在途改动的验证结果。依赖审计发现既有
`wasmtime 36.0.17` 对应 RUSTSEC-2026-0363；本轮未获授权升级该无关
依赖，质量门不得称通过。

### Native closure integration checkpoint (2026-10-16)

在 HOLBasisV1 policy 与 composition/maxidx 新一轮改动之前，独立 kernel
package 实际运行结果为 322 项通过、1 项既有忽略，覆盖 class/export、
精确来源 adapter、nested export 与索引耗尽拒绝。定向静态复审已确认
canonical source 匹配与延迟索引分配的修复；错误 variant 回归也已修正。
这不是最终 `strict`、workspace 或全局质量门结果。

同一阶段实际 CLI 对固定 `isabelle-source/src/HOL/HOL.thy` 返回
`KernelTrustedClosed: TrueI`，并明确输出只验证 projection、未编译完整
theory。投影要求完整 class/base-sort 来源与 function-arity proof tail，
不能接受删除来源 setup、局部化声明或 trailing `oops`/`sorry` 的输入。
该结果不增加 sampled 125 项中的可信数量，也不证明原生 ROOT 已执行。

目前正在整合精确 HOLBasisV1 子集、原引入 basis 依赖身份、完整 Pure
composition/owner transfer 与保留 maxidx 的 replay。其实现、独立审查及
后续运行结果尚未全部收敛，不能将这一轮接口改动标作 K3 验收通过。
ML 的类型驱动 Poly/ML 打印器亦已获得明确授权：使用编译器的真实类型
证据，保留 opaque/functor 身份、callback、GC、异常和取消语义，不按
值形状、文件名或 `ML_system_pp` 名称猜测类型。完整 ROOT、typedef、
THM 桥接及九根运行仍未通过。

### Native kernel and ML progress (2026-10-15)

原生闭包仍在实施，不能提交为通过验收。当前 kernel 保留 theorem 的
S/C/F/pending/mode，owner replay 比较完整负载；`theorem/v4` 身份编码
覆盖该负载。有限替换按 type pass 后的完整 `(name,index,type)` 键去重，
所有 term RHS 以及被消去的 forall/axiom 参数保留其 sort 要求。

本轮发现 `theorem_builder::close_thm` 仅查 H、绕过 `try_close` 的负载检查；
最小合同先稳定失败，统一关闭检查后通过。接受端原本仍拒绝该负载，
因此这是候选关闭 API 的不一致，不是已经复现的 accepted-token 漏洞。
实际运行 `theorem_obligations` 8 项、独立 v4 reference encoder 2 项均通过；
独立进程 smoke 接受了 present-sort schema 并完成精确 owner 引用，同时拒绝
带消失类型约束的 `close_thm`。这些结果不代表完整 strict/workspace/global 门。

空 sort 的 proof-only 参数已有受检 `strip_shyps` 路径：原 source 完整
replay 后生成私有 bound proof，独立检查关闭的 proof/term binders 与
精确 H/P；消失的局部 Free 通过原 typed identity 和现有 `Generalize`
记录 source 参数导出，不能向最终 owner 注入声明。修复了 resolution
将实例化后结论内部 implication 误算作前提，以及 proof-only Free
类型替换/最终 replay 的作用域问题；两项均经独立窄审关闭。

该树实际运行 kernel package：237 项通过、1 项既有忽略；空 sort stripping、
完整 payload、typed substitution、owner 引用与独立 v4 encoder 回归均在内。
独立 kernel smoke 接受并引用空 sort 消去后的精确命题，保留未解非空
sort 约束的拒绝。class 图的 arity 参数域方向和重复父类处理也已修复；
图仍只在测试模块接入，布尔检查不提供类证明权限。

ML 的文本 Basis 以固定 distribution 的 PolyML 5.9.1 源码为准，
修正 ASCII/转义/Substring.span/scan 状态边界；`triml/trimr` 使用普通
闭包分阶段求值，不按 native 函数地址特判。该调整后 39 项定向测试与
12 个文本 smoke 契约通过，独立静态审查未留本切片 finding。
这些局部结果不是完整 strict/workspace/global 门，也不是 Pure bootstrap
或九根 HOL 兼容证明；类/arity 证书、完整 owner DAG、非空 sort 的 C4
export 与 C2 typedef 仍未完成。

solver FD smoke 曾在宿主 `umount2(MNT_DETACH)` 进入不可中断等待，
清理域未被证明排空；因此暂停新增 solver 启动，不放宽隔离、不宣称
cleanup 成功。完整宿主与包含 veriT 的闭包验收保持阻塞。

### Integrated delivery verification (2026-10-14)

`cargo +stable xtask verify` aggregates formatting, strict workspace/all-targets
Clippy, locked all-targets compilation, a zero-warning kernel check,
documentation checks, the kernel firewall and complete workspace regression.
CI uses the same matrix and independent required security scans.
`release-check` now validates the version then runs `verify`; Tier statistics
and official reference builds remain explicit diagnostics.

Quality repairs cover missing `Sort` imports, complete boxed `MixedContext`
error payloads, kernel lint issues, and valid document headings before a theory
header. The parser still rejects executable preambles; unsupported whole-file
features do not become accepted proofs. This delivery's verification is
recorded separately from the initial migration results below.

### Native Rust automation verification (2026-10-14)

Historical automation-only run, before the follow-on integrated quality
repairs. These failures and counts describe that tree, not the final delivery.

| Executed check | Observed result and boundary |
|---|---|
| `cargo +stable xtask selftest` | 156 passed, none failed or ignored; includes independent supervisor, reference, archive, install/package and hook contracts. Does not build the product/kernel. |
| `cargo +stable clippy --locked -p xtask --all-targets -- -D warnings` | Passed for the automation crate; not the global workspace Clippy gate. |
| Reference migration smoke against the frozen run | SQLite source map and six decoded/profile artifacts matched the frozen JSON structurally. A synthetic comparison input matched 18,895 records with zero structural differences, but correctly returned `BlockedPrerequisite` for unavailable P0 evidence. No native theory execution was claimed. |
| Real syscall trace smoke | 34 events, zero decoder errors; raw argv and environment were not persisted. The temporary smoke programs were removed after execution. |
| Native `reference prepare` | Passed against the pinned archive and fixed-source checkout, including Git global PAX comment handling. Unsupported global override metadata is rejected. |
| Fresh native `reference build` | `build-EZgqjW` rebuilt official Pure and HOL, exited 0, and recorded 26,189 selected syscall events with zero decoder errors. |
| Fresh native `reference inventory` | `inventory-yUhM4R` explicitly reused that successful build, exited 0, and exported all six decoded/profile artifacts: nine roots, 67 theory contexts, 66 executed non-Pure theories, 54,538 commands and 18,895 fact-group members. Its trace recorded 20,569 selected events with zero decoder errors. |
| Hook regression and direct CLI smoke | Five hook cases failed before the missing entry was added, then passed; actual pre/post commands printed the edited path and the tracked-source reminder. Claude event delivery/config loading was not exercised. |
| CLI and configuration checks | Help, version matching, firewall and compatibility audit ran; workflow YAML and Claude JSON parsed. No hosted CI, publication or Claude runtime enforcement was claimed. |
| `cargo +stable xtask docs` | Snippet, link and template subgates passed; the aggregate failed workspace formatting and root compilation. |
| `cargo +stable xtask test --test hol_profile_supervisor` | Blocked before product execution by the root `Sort` import error. Independent supervisor contracts passed separately. |
| Complete `~/.omp/agent/validate.sh` | 4 checks passed and 4 failed: gitleaks, trivy, cargo-audit and cargo-deny passed; workspace format, strict Clippy, build and tests failed. No successful validation stamp. |

At that stage the product build failed at `src/hol/hol_theorem_prover.rs:93`
(missing `Sort`), and kernel unit-test compilation failed at
`crates/kernel/src/theory.rs:2791` for the same type. Global kernel Clippy
reported 125 diagnostics. These were source issues in paused product work,
not missing automation fallback behavior. The migration-owned supervisor test
was formatted; other kernel/ML formatting was not part of that initial
scope. The prior official-source compatibility failure was not reached,
and no new `strict`, `core` or accepted-token result was claimed by that run.

Independent correctness/security review findings were repaired, including
embedded hooks and archive/trace boundaries. Dependency additions are limited
to the independent xtask implementation; scan success retains the existing
scan scope and exceptions. Linux behavior was exercised; native Windows/macOS
execution, a real no-rustup host and hosted release workflows remain unverified.

The fresh build and inventory runs are retained under
`/tmp/isabelle2025-reference.c2uIdUKM/runs/`; each has `command.json`,
`result.json`, stdout/stderr logs and sanitized events. Neither run was
interrupted. Each retains four unresolved relative-path observations, not
credited as source inputs; trace completion is not complete execution coverage.
The checked-in `closure.json` remains the original frozen baseline with its
original tool/artifact hashes. New run hashes do not overwrite that history.
These successful runs exercise the migrated Rust orchestration and decoders
around the **official** runtime; they do not prove native Rust HOL compilation
or increase the trusted theorem count.


### Isabelle2025 reference observations (2026-10-12)

Historical reference run, not a run of the current all-Rust cutover:
the then-current `cargo +stable xtask reference prepare|build|inventory`
used the pinned official distribution and fixed source commit
`765fb2460a57eb46e8490283241ad46f1fac857f`. The historical final build reconstructed
Pure and HOL in a fresh output directory and exited 0. A separate
`Reference_Execution = Pure +` observer session then executed the nine roots
from source and exited 0; `sessions HOL` supplies resource information, not a
parent HOL heap. Both runs had no interruption or trace-decoder error.

The frozen [reference snapshot](../../tests/fixtures/isabelle2025/closure.json)
records the exact run IDs, artifact/tool hashes, source identities, graphs,
command requirements, public ML symbol catalog and named-fact group indexes.
It is not a production loader manifest, execution permission, axiom allowlist
or accepted-token cache. Full structured propositions and per-occurrence
evidence remain in the hash-bound run artifacts outside Git; see the
[reference commands](../../scripts/README.md#isolated-isabelle2025-reference).

| Observation | Result and boundary |
|---|---|
| Logical imports | 67 theories including Pure; nine roots, not 67 Rust-accepted theories |
| Executed target source | 66 non-Pure theories, 54,538 commands, 114 command kinds; the observer theory is excluded |
| ML inputs | 236 executed file-command input bindings; 282 source-declared bootstrap loads checked against build-time file observations, not a complete nested ML call trace |
| Source reads | 1,124 distinct fixed-source files opened across the broader Pure/HOL build and observer run; this is not the minimal production dependency set |
| Public ML catalog | 67 theory contexts and a separate `ML_Bootstrap` context; declarations and type displays, not called-function evidence or structural type identity |
| Named static facts | 18,895 records; none has an observed oracle footprint, skip-proof flag, term hypothesis or flex-flex pair; 16,490 retain sort hypotheses |
| Oracle registrations | 11 registrations, distinct from oracle use |
| Official axiom table | 1,318 entries: 1,267 definition-associated, 17 base-sort arities, 2 explicit arities, 12 conditional typedef extensions, 13 HOL axiom candidates and 7 Pure primitive mirrors |

Those axiom categories describe official source provenance, not approved Rust
logical authority. Named facts do not cover anonymous intermediate facts,
unregistered proof steps or dynamic fact evaluations. Public namespace lookup
can use the final session's global fallback when enabled; it is not an
independent historical namespace snapshot for each theory. Four failed
relative Scala-source opens in each run remain explicitly unresolved and are
not credited as inputs. No aggregate full-observation claim is made.

The inventory's `owner` is the transferred observation context, not a
declaration origin or Rust `accepted_in`. Internal sort constraints are not
exported, and named-theorem dependencies are not a complete axiom/extension
leaf closure. These fields need additional evidence before a complete
Rust-to-reference differential can pass; missing evidence must not become
empty sets.

The trace contains real `veriT` executions, and original `List.thy` proofs use
`smt (verit)` at lines 3793, 5008 and 8086. The user has approved a separate
native capability for fixed `verit-2021.06.2-rmx-1`: Bubblewrap plus an already
delegated cgroup v2, one invocation at a time, 300 seconds and 2 GiB, with no
network, shell or host-directory access. Missing isolation prerequisites must
block execution. A local prerequisite probe exercised delegated limits,
namespace/path/network restrictions and normal cleanup; it did not exercise
the production launcher, actual solver, limit exhaustion or descendant cleanup.
The solver supplies untrusted proof text; Rust-checked reconstruction remains
mandatory. Neither reference-run permission nor solver success grants theorem
authority.

The user also approved replacing the complete `structure Thm` implementation
in fixed `src/Pure/thm.ML`, retaining its signatures and `Basic_Thm` aliases.
Independent correctness and security reviews accepted this representation and
execution-boundary design, not an implementation or any new logical rule.
Conditional typedef, class/arity and sort-proof replay still block P1.
Packages C–H and full native closure acceptance remain incomplete.

## Trust Metric Correction

The last executed source-backed five-file sampler, before this automation
migration, used bundled `theories/HOL/{HOL,Orderings,Set,Nat,List}.thy`, taking
the first 25 explicit-proof candidates per file. Its audited `HOL::TrueI`
returned a `TrustedTheorem` with `HOL.Trueprop HOL.True : prop` under an
immutable owner. This is historical evidence, not a fresh run of the current
native implementation:
```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

This accepted token is produced from an audited projection of the actual
sampled HOL source: checked required declarations, the source's `True`
definition RHS, and its entire `TrueI` proof. Other commands, including ML,
are not executed or inserted into the accepted owner. This is not a
whole-theory Isabelle/HOL build or an official runtime differential.
`tests/fixtures/TrustedTrueI.thy` and `TrustedPureIdentity.thy` remain
separate accepted fixtures and do not contribute to the sampled count.

Historical baseline: the 2026-10-03 run against the rebaselined
Isabelle2025 Gitlink reported `TransitionalStrictClosed: 1/125` and
`KernelTrustedClosed: 0/125` before this sampled source-backed cutover.
The former Gitlink `c8d07caca5f6b9dd351de18a7ee25d2fa0e61ab8` could
not be fetched; `.gitmodules` now pins the official mirror at
`765fb2460a57eb46e8490283241ad46f1fac857f`. Its `src/HOL/HOL.thy`
matches the published Isabelle2025 archive byte for byte, but the current
sampler uses the different bundled `theories/` snapshot. Old admitted-reason
counts are not comparable to the current run.

The standalone HOL fixture still installs only the structurally checked
`refl` basis and generic conservative `True_def`. The Pure fixture checks
`!!P::prop. PROP P ==> PROP P` via `by assumption`, `assume`,
`implies_intr`, and `forall_intr`. Exact-owner replay seals both. Neither
path provides a general HOL loader or legacy-to-trusted promotion; the HOL
basis has not been independently verified against Isabelle/HOL.

### Legacy search context (2026-10-07)

Proof methods, source verification and legacy term annotation now use an
explicit borrowed `HolTheoremDb` and its declaration environment instead of
an unsafe thread-local database override. The process-wide search database
is immutable and accessed only from application roots; each theory source
transaction has a separate search database for its proved local facts.
Rewrite-rule caches belong to their database, not to the process. This is a
scope and lifetime repair, not a new accepted theorem path or a measured
search acceleration; the sampled acceptance chain remains independent.

Independent security review found a remaining medium-risk cache consistency
boundary: the legacy search collections are public, so direct mutations
after a cache has been initialized can bypass invalidation. `extend`,
`add_builtins`, and `insert_named_fact` invalidate the DB-local simplifier
and four discrimination nets; the public fields remain a legacy API limitation.
No evidence links this limitation to a new accepted theorem token.

## Historical Baseline And Current Gate

The first trusted-kernel engineering checkpoint is recorded in
[BASELINE.md](../kernel/BASELINE.md). It includes four reviewable commits:

```text
e60580b kernel: harden primitive rules and checked instantiation
7465d48 trust: require closed proved theorems for trusted acceptance
2dee3d0 proofterm: add minimal burden-aware derivation replay
eef6d80 docs: reposition project as trusted Rust LCF kernel prototype
```

The current replacement gate is `cargo +stable xtask strict`, implemented in
[xtask](../../xtask/src/tasks.rs). Historical baseline runs predate this
cutover and must not be attributed to xtask.

A post-commit audit also ran normal and all-target compilation at baseline
`38c5f14` (then `origin/dev`) and each
immutable-context/acceptance/outcome/source-AST candidate commit. Normal
`cargo +stable check --locked` and the strict gate pass independently. After
a targeted `benches/kernel_benchmarks.rs` fix (commit `878d8ae`),
`cargo +stable check --locked --all-targets` also passes.

The baseline originally carried two ignored `alpha_eq` tests:

```text
Free / Const suffix matching
Var / Free index confusion
```

Strict kernel alpha-equivalence now rejects both in trusted paths. The legacy
behavior is isolated as explicit `compat_alpha_eq` parser/loader compatibility.
A completed legacy hardening step added `CTerm::certify_checked(term, type_env)`,
which provides a hard certification API that rejects residual dummy types and
ill-typed applications. Most old parser/HOL/Isar call sites still use
best-effort compatibility certification. `CTerm` now records checked vs compat
status, and strict `ThmKernel::assume` / `reflexive` reject compat CTerms; old
call sites have been made explicit as `assume_compat` / `reflexive_compat`.
`Thm` now also records construction trust as `Strict`, `Compat`, or
`Admitted`, so compatibility theorems cannot enter trusted statistics merely
because they are oracle-free and closed-shaped. `Thm::check_kernel_invariants`
now provides separate `Compat` and `Strict` invariant checks so strict trust is
auditable rather than only a source label. The first Isar proof-state
production boundary has also moved onto the strict path: local assumptions,
top-level proof goals, and checked subgoal scaffolding now use checked
certification plus strict `ThmKernel::assume`, producing Strict open theorem
obligations rather than compatibility theorem scaffolds. This proof-state
boundary now uses an explicit `ProofCertContext` / `TypeEnv` source: constants
and local frees must be declared in the proof context before certification, so
raw terms can no longer self-declare their own names merely by carrying
non-dummy type annotations.

Important limitation: `check_kernel_invariants(Strict)` is an internal theorem
consistency audit, not a closed-lemma predicate and not a complete replay
certificate. Strict open theorems may pass it while failing
`is_strict_closed_proved()`. Strict derivations that use currently unsupported
replay rules are structurally audited but still fail `check_proof()` until their
replay rule is implemented.

The architectural reset is implemented in the isolated `isabelle-kernel` crate
at `crates/kernel/`; `src/kernel/` re-exports its public API. It is not another
compatibility patch over legacy `src/core` types. Its implemented chain is:
`RawTerm -> CTerm/CProp -> KernelThm -> ClosedThm ->
accept_closed_theorem -> (TrustedTheory, TrustedTheorem)`, plus a
`ProofObligation` type that is not a theorem and proof-erased `SearchFactDb`
storage.
It deliberately has no dummy type constructor or compatibility certification
API. The strict nucleus now
implements the base primitive rule set plus conservative `resolve1_match`
and `subst_premise` with invariant replay and attack tests. `resolve1_match`
uses strict matching and deterministic substitutions, rejects Free/schematic
Var namespace collisions with `RequiresLifting`, and records
`Derivation::Resolve1Match`. The historical `bicompose` alias is not exported;
the separate current `bicompose_candidate` uses checked bound-proof replay,
not full ML search. `subst_premise` is propositional-equality only, fixed
lhs -> rhs, with exact selected-subgoal matching.
See
[ADR-0001-kernel-core-rewrite.md](../adr/ADR-0001-kernel-core-rewrite.md) and
[KERNEL_PRIMITIVES.md](../kernel/KERNEL_PRIMITIVES.md).

The 2026-07-19 maturity assessment was: the Pure kernel research
nucleus is meaningful and substantially hardened. Immutable strict
signature/theory ancestry propagates through certification, theorem
construction, and replay, and one non-forgeable acceptance API now binds
closed Pure theorems and replay-derived theorem dependencies to immutable fact
ancestry. At that historical checkpoint the sampled Isabelle/Pure/HOL
trusted loop was not closed. The later source-backed `HOL::TrueI` sampler now
accepts exactly one token; other legacy and runtime callers remain unmigrated.
The implemented boundary and remaining gaps are audited in
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).

## Repository And Agent Policy

Root [AGENTS.md](../../AGENTS.md) is the versioned, harness-neutral rule source.
`.claude/`, `~/.codex/`, and harness memory are routing/cache layers and cannot
override source, tests, canonical status/trust docs, or accepted ADRs.

Short explanatory code/configuration blocks are allowed in Markdown. All
maintained automation belongs in `xtask/`; `scripts/` retains only official
reference probe inputs and classified design templates. Standalone compilation
does not establish production API compatibility or validate a trusted
architecture. The [development guide](../guides/DEVELOPMENT.md#engineering-workflow)
owns the shared lifecycle; adapters link to it.

Dependency and vendor changes remain separate from trust-boundary work.
Unexplained lock-only refreshes are not accepted merely because
`cargo metadata --locked` succeeds.

## What Is Solid

The following areas have a coherent implementation and regression coverage.
Rows naming `Thm`, `ThmKernel` or `CTerm` describe legacy `src/core`, not
the isolated strict kernel or its accepted-token API:

| Area | Current state |
|---|---|
| LCF-style theorem type | `Thm` fields are private; external construction routes through `ThmKernel`. |
| Kernel primitive rules | All 15 base primitives implemented (assume, reflexive, symmetric, transitive, combination, abstraction, beta_conversion, implies_intr, implies_elim, forall_intr, forall_elim, equal_intr, equal_elim, generalize, instantiate); several rounds of type/burden/oracle boundary hardening done. |
| Checked instantiation | Production paths use `instantiate_checked`; legacy infallible instantiation is not a production API. |
| Strict alpha equality | Trusted kernel equality uses `kernel_alpha_eq`; legacy broad matching is isolated as `compat_alpha_eq`. |
| Checked CTerm certification | `CTerm::certify_checked` exists, CTerms carry checked/compat status, and strict `assume`/`reflexive` reject compat terms. |
| Source proposition fail-closed guard | The loader records typed consumption status and a narrow source-shape classification. The registered explicit-proof `TrueI` adapter requires `FullyConsumed + StandaloneHolTrueAlias`; recovered, contextual, incomplete, or unavailable source becomes `admitted:strict_adapter_source_prop_unverified` without parser-gap or legacy fallback. This is transitional metadata, not a name-resolved AST. |
| Source proposition AST and narrow checked pipeline | `source_ast` preserves names, raw syntax, binders, annotations, and file byte spans; the new `source_parser` is bounded and fully consuming. `elaborator` resolves the supported names and syntax against `ProofContext` and produces checked `CProp : prop`. `SourceId` and spans are diagnostics, not authority. The legacy parser/adapter remains separate. |
| Proof-state strict entry points | `ProofState::assume`, `Goal::init`, and checked subgoal scaffolding construct Strict open theorem obligations from explicit proof-context certification. |
| Strict kernel nucleus | `crates/kernel/` is the isolated TCB crate, re-exported by `src/kernel/`. It has no dummy type or compat certification, separate proof obligations, proof-erased search facts, primitive Pure rules, strict matching, conservative resolution/rewriting wrappers, immutable owner/fact ancestry, and one trusted acceptance gate. |
| Immutable strict context identity | Canonical, domain-separated `SignatureId` and ancestry-sensitive `TheoryId` values propagate through `ProofContext`, certified terms/propositions, strict theorems, every current rule, and replay. Signature/theory extension is immutable; duplicates, stale objects, sibling ancestry, wrong signatures, mixed rules, and wire digest mismatches fail closed. |
| Strict trusted acceptance | `accept_closed_theorem` recursively recertifies/replays one `ClosedThm` under the exact immutable owner, reconstructs dependencies, rejects duplicates and owner/store mismatches, and returns an immutable child owner plus sealed token. `ForallIntr` and `Abstraction` scope typed Free variables only in their premises. Exact `(id, name, accepted_in)` tokens and canonical payloads are authorized before dependencies are recorded. |
| Strict theorem invariants | `check_kernel_invariants(Strict)` remains a legacy audit. New-kernel acceptance uses owner-parameterized replay across every current `Derivation` payload and compares the exact reconstructed result. |
| Proof outcome classifier | `KernelTrustedClosed` owns an accepted token and is mutually exclusive with transitional, compat, open, admitted, and failed outcomes. The sampled HOL `TrueI` source projection now contributes one token to the bundled five-file run; standalone fixtures remain separate. |
| Targeted trusted slices | Synthetic Pure `A ==> A`, the two source-backed fixtures and the external `native_thm` / `native_thm_variables` Rust consumers exercise distinct acceptance paths. The Rust consumers cover transformations, scope/owner replay and reference reuse, not complete ML `Thm: THM`; none adds to the sampled 125-theorem metric. |
| Core/kernel migration framing | `src/core` remains a legacy proof engine for compatibility, automation, diagnostics, and migration adapters. The isolated `crates/kernel` TCB is re-exported by `src/kernel`; frontend migration is incomplete. |
| Checked definition sources | `HolTheoremDb` has a separate `checked_definitions` table for non-theorem definition inputs. The first entry is `True_def`, checked against the explicit `TypeEnv`; it is not inserted into searchable facts and is not counted as `TransitionalStrictClosed` or `KernelTrustedClosed`. |
| Oracle/admit tracking | Legacy `ThmKernel::admit(ct, reason)` retains unproved propositions with explicit oracle footprints; these are not accepted strict tokens. |
| Closed theorem acceptance | The legacy filter remains transitional. New-kernel `accept_closed_theorem` returns sealed tokens for replayed closed Rust derivations; the two source fixtures and Rust THM consumers have scoped evidence. Only the audited sampled `HOL::TrueI` projection contributes to the sampled count. |
| Isar goal export boundary | `verify_lemma` no longer returns oracle-free open proof-method results as accepted lemmas. Results are exported by legal `implies_intr` discharge of known context assumptions, or admitted with `admitted:goal_export_*` / `admitted:proof_engine_failed`. |
| Simplifier rewrite-rule admission | `RewriteRule::from_thm` rejects open, admitted, unresolved, or conditional rewrite theorems instead of treating them as unconditional simp rules. Unproved HOL built-in rewrite templates are disabled until backed by closed theorem sources. |
| Searchable vs trusted facts | `HolTheoremDb` and `SearchFactDb` are search/migration indexes. Search facts contain no extractable kernel proof and cannot convert to `TrustedTheorem`; final acceptance is token-backed and reported as `KernelTrustedClosed`. |
| Attribute fallback honesty | Non-derivational theorem transformations are admitted as `admitted:attribute_transformation`. |
| Legacy T4 replay | `src/core/proofterm.rs` replays six base Pure rules with burden checks. The former `hol_object_refl` and `true_def_transport` bridges were removed. Strict-kernel acceptance separately replays every current strict `Derivation`. |
| HPC symbolic compute | Design-only parallel track for untrusted candidate generation, fingerprinting, and prefiltering; no Burn/CubeCL dependency and no kernel dependency. |
| ISIP standard suite | Design-only overview and ISIP-000 architecture draft exist. ISIP-100 through ISIP-600 are planned, not implemented specifications or runtime features. |
| Attack tests | `tests/kernel_context_identity.rs`, `tests/kernel_trusted_acceptance.rs`, `tests/kernel_rewrite_soundness.rs`, strict-kernel unit tests, and legacy core/proofterm tests encode identity, owner, replay, dependency, canonical-ID, type, burden, and compatibility regressions. |

Important distinction:

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hyps + no unresolved tpairs
is_strict_closed_proved() == strict construction + is_closed_proved() + no dummy types
check_kernel_invariants(Strict) == strict construction + theorem invariant audit
```

`assume(A)` is a valid theorem of shape `A |- A`; it is not `|- A` and must not
be counted as a closed proved lemma.
`assume_compat` / `reflexive_compat` may still create closed-shaped facts, but
they are `ThmTrust::Compat` and must not be counted as trusted verified lemmas.
Passing `check_kernel_invariants(Strict)` means the theorem is internally
consistent as a legacy strict theorem. The transitional legacy table additionally
requires `is_strict_closed_proved()`; final acceptance instead requires a
context-bound new-kernel `TrustedTheorem` and the `KernelTrustedClosed` gate.

## What Is Not Complete

The project is not close to full Isabelle/HOL:

| Layer | Honest current assessment |
|---|---|
| Term / type / certification boundary | Strict `CTerm::certify_checked` exists and is status-tracked, but legacy best-effort certification is still widely used through explicit `_compat` paths. |
| Pure kernel | Research-grade prototype with a strict invariant checker for core theorem internals, not full Isabelle `thm.ML` equivalence. |
| Proofterm replay | Minimal derivation replay, not full Isabelle `proofterm.ML` checking. |
| Isar | Partial state machine and method dispatch, far from full Isabelle/Isar semantics. |
| HOL tools | Simplifier/Metis/Meson/linarith/datatype packages are partial or heuristic. |
| HOL library coverage | Small subset; many searchable legacy facts are admitted or generated, not accepted strict tokens. |
| Session/PIDE/LSP | Experimental document/session workers and partial LSP: bounded queues, symbol cache, workspace snapshots, diagnostics, and stale-result rejection. Built-in checks and definition lookups use a supervised, killable direct child; custom executors stay cooperative. This is not Isabelle session/PIDE infrastructure or an OS memory/privilege sandbox. |
| AFP / ecosystem | Out of scope for the current research slice. |

Historical snapshot before the declaration/proof-result hardening, from the
2026-10-03 core run on the pinned Isabelle2025 source:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
ProofOutcome summary:
  TransitionalStrictClosed: 1
  CompatClosedOracleFree: 1
  Admitted(goal_export_unknown_hyps): 64
  Admitted(goal_export_open_subgoals): 3
  Admitted(parser_gap): 2
  Admitted(datatype_stub): 2
  Admitted(proof_engine_failed): 52
```

Historical post-hardening snapshot before the source-backed sampled cutover
(`scripts/dev-check.sh core`): the library and binary samplers agreed;
standalone fixtures were not counted.

```text
KernelTrustedClosed: 0/125
TransitionalStrictClosed: 1/125
CompatClosedOracleFree: 0
Admitted(parser_gap): 2
Admitted(datatype_stub): 2
Admitted(proof_engine_failed): 120
```

The current run moves only the existing `HOL::TrueI` from transitional to
kernel-trusted; remaining admitted facts are not proved by that change.

The historical legacy `quick_verify::test_batch1_core` returned a green test
result only because its assertion required at least one generated theorem.
Its run reported **53 theorems, 1233 errors, 0/5 files passed**; this was not
successful theory compilation or a trusted acceptance metric. That test,
the equivalent `single_verify`/`one_by_one` tests, and the ignored approximate
loader-success test were removed during the fail-closed loader migration.
`theory_load_contract` and `session_load_contract` cover actual supported
declarations, completed proofs, failed transactions, and dependency rejection.

The 2026-10-03 `scripts/dev-check.sh tier2` run also returned a green test
status while reporting **0/3872 verified**, **3872 axiom-accepted (not
proved)** across 97 files, and four file timeouts. A green runner result is
not evidence of a successful theory build or a proof; earlier Tier2 figures
were measured on a different source baseline and are not comparable.

The targeted `A ==> A` kernel smoke slice is intentionally not counted in this
core batch unless an existing sampled core-file lemma routes through that
shape. It demonstrates Pure kernel construction but is not an existing sampled
theorem and does not repair HOL source elaboration.

Historical investigation before the sampled cutover: no scanned parsed
proposition in the 125 was a plain `A ==> A` / `P ==> P`, so the separate
Pure identity adapter could not move the count. `HOL::TrueI`, with source
proof `unfolding True_def by (rule refl)`, then used legacy checked payloads
and a named transport bridge, yielding `1/125` transitional and `0/125`
kernel-trusted. That legacy bridge and its old proof tags have since been
removed from the accepted path. The current sampler receives an actual
owner-bound kernel token instead; the historical bridge observations do
not describe its present acceptance semantics.

The public legacy `parse_term` now requires full consumption. Missing operands
such as `True =`, conflicting annotations, and unmatched delimiters fail rather
than recovering a success-shaped term. Only `parse_term_with_status`, used by
the search loader, retains explicitly incomplete prefixes for diagnostics.
The `TrueI` adapter still requires
`FullyConsumed + StandaloneHolTrueAlias`; contextual, incomplete, and unavailable
source provenance is rejected before the legacy parser-gap override.

For independent parsed statements, `DefLocation::proposition_text` now keeps
the original text instead of deriving source from the formatted legacy theorem.
Contextual, premise-bearing, generated, unavailable, or truncated quoted
statements provide no complete source text to the checked elaborator. The
legacy parser may still return a compatibility theorem for them; raw text is
diagnostic provenance, not proof of the sampled `TrueI`.

This is a transitional fail-closed guard for the search loader, not that
loader's checked source elaboration. The separate strict parser/elaborator
resolves supported names and certifies both standalone TrueI and Pure identity.

Historical pre-cutover transitional milestone: the narrow `HOL::TrueI`
adapter used the following legacy payload chain, not current token authority:

```text
1. True_def checked legacy payload: done, non-theorem input only
2. HOL object-equality/reflexivity bridge: implemented as narrow legacy bridge
3. theorem-specific transport/fold-back to True: implemented for the payload
4. try_strict_hol_true_i adapter: implemented
```

The bridge designs are tracked in
[HOL_OBJECT_EQUALITY_BRIDGE.md](../design/HOL_OBJECT_EQUALITY_BRIDGE.md) and
[CHECKED_DEFINITION_TRANSPORT.md](../design/CHECKED_DEFINITION_TRANSPORT.md). They are
explicitly not a general unfolding engine, simplifier, or broad HOL proof
engine.

Do not generalize this `TrueI` path by returning `True` directly, using the
current compat `refl` fact, or turning it into a general unfolding/simp engine.
The `TrueI` path is now routed through the minimal strict adapter dispatcher in
`src/isar/method.rs`. The dispatcher currently registers only this adapter and
returns explicit `NotApplicable` / `Proved` / `Rejected(reason)` outcomes so
future strict slices do not turn `verify_lemma` into a theorem-name switchboard.
Shape-hit rejections are admitted with `admitted:strict_adapter_*` reasons
instead of falling through as ordinary legacy proof-engine failures.
The ranked scan of the remaining 124 sampled theorems is retained as a
diagnostic inventory in
[NEXT_STRICT_SLICE_CANDIDATES.md](../design/NEXT_STRICT_SLICE_CANDIDATES.md); its original
adapter recommendation is superseded by immutable context acceptance.

The `TrueI` dispatcher entry now relies on an explicit parser alias:
source-level `True` / `HOL.True` becomes canonical `Const("HOL.True", bool)`.
The strict normalizer no longer converts a `Free("True")` or dummy-typed True
into a checked proposition. For lemmas with an explicit proof, registered
strict adapters run before the legacy builtin Var/Free parser-gap shortcut;
only `NotApplicable` continues to compatibility verification.

`HOL::trans` remains deferred. General checked propositions and the
object-logic trust layer are specified in
[CHECKED_HOL_PROPOSITION_NORMALIZATION.md](../design/CHECKED_HOL_PROPOSITION_NORMALIZATION.md)
and
[ADR-0003-hol-logic-trusted-extension.md](../adr/ADR-0003-hol-logic-trusted-extension.md).
The standalone TrueI implementation is narrower than those general designs.
The earlier sampled `1/125` was a legacy `core::Thm` migration classification.
The current audited projection instead constructs a new owner-bound
`TrustedTheorem`; it does not upgrade that old payload.

The earlier `OPEN_HAS_HYPS` and `goal_export_unknown_simp_context` observations
are historical diagnostics from before the full proof-result gate. Current
proof completion checks Strict/checked construction, the complete proposition,
permitted assumptions, and scope export. Results that cannot satisfy that
contract are rejected or explicitly admitted by the outer sampled verifier;
they are not oracle-free accepted lemmas. Admitted-reason distributions above
belong to the dated runs and inputs that produced them; do not extrapolate
current distributions from historical snapshots.

The strict kernel has separate synthetic Pure `A ==> A`, source-backed Pure
identity and source-backed HOL `TrueI` acceptance demonstrations. These fixtures
do not add to the sampled count. The five-file sampler independently routes
its real `HOL::TrueI` source through the audited projection:

```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

The Pure identity token uses `!!P::prop. PROP P ==> PROP P` with
`by assumption`; `(rule impI)` is not an alias. Replay scopes its typed Free
under `forall_intr`; `Abstraction` now uses the same premise-local scope,
and the owner still rejects unscoped Free variables and forged premises.
The HOL token requires a fully
consumed source proposition, checked `CProp : prop`, authorized `refl` schema,
generic conservative `True_def`, Pure transport, and exact-owner acceptance.
`HOL.subst` is excluded: its previous manifest schema used unrelated
schematic variables and was not sound. Neither standalone CLI path gives
the legacy theory batch loader accepted-theorem authority. Sampled
`verify_lemma` carries explicit token evidence only for the audited projection.
LSP DB hover/completion label facts as legacy search results; WASM exposes
only legacy search metadata handles, and demo output distinguishes the
standalone accepted token from transitional legacy examples.

### 声明、加载与证明结案的当前边界

strict signature 显式记录类型构造器和 arity，并将完整类型表纳入
`SignatureId`；当前身份版本见
[严格内核不变量](../kernel/KERNEL_PRIMITIVES.md#global-invariants)。
认证递归检查注解和缓存类型；basis 在安装前检查完整公理，
不是等待某个实例使用时才报错。定义入口与 replay 共用 RHS 单态检查，
owner ancestry 校验规范 theorem token 及其证明负载。

legacy 完整加载入口与 HOL 搜索库分离。`TheoryProcessor` 只支持单个真实
import、`typedecl`、已实现 lemma/证明命令及文档命令；未实现声明、多个
imports、`sorry`、`accept_all`、缺少 `end` 和尾随输入均失败。不返回 partial
Theory，类型声明必须实际写入最终 signature。`SessionBuilder` 重建每轮
registry，阻断失败父项及其后代，同时保留独立成功项。

两套 proof 状态在结案前核对实际 Strict/checked 结果、完整命题、许可假设
及作用域导出；初始 goal、Compat fact、未闭合子证明不算完成。源方法必须
完整解析，不能因拼错方法而改跑 Auto。底层五条已用 Pure 规则保留正确类型
与 trust 传播，但不赋予 legacy 结果新 kernel 权威。

simp 证书覆盖整个重写的输入输出；schematic 实例化作用于整个 theorem，
Free 保持 rigid，条件规则和篡改缓存拒绝。Metis/Meson/ATP 的最终出口检查
完整目标和负担；ATP 每步按命名事实和实际推理核对公式，坏证据不回退搜索。
这些修复收紧“成功”的含义，不代表广义 Isabelle 语法或自动化已实现。

legacy `parse_term` 只返回词法完整且消费到 EOF 的项；独立搜索诊断
`parse_term_with_status` 仍可标记 Incomplete，但不能授权证明。尚未支持的
Unicode 运算符和 mixfix 必须拒绝，不能丢弃字符后计作成功；属性测试使用
已支持的 Isabelle 转义语法。原先仅靠解析/生成数量或残缺解析名称判断
成功的 loader 测试已移除，改由完整命题、畸形规则不生成事实以及事务
发布契约覆盖；没有降低数量阈值来维持绿色。

## Historical Maturity Estimates

The following earlier subjective engineering estimates are retained for
historical context only. They have no reproducible measurement method and are
not current completion metrics or acceptance criteria.

| Scope | Earlier estimate |
|---|---:|
| Full Isabelle/HOL + Isar + PIDE + AFP ecosystem | 15%-25% |
| Isabelle/Pure-inspired Rust kernel research slice | 45%-60% |
| Minimal end-to-end Isabelle/Pure trusted kernel | 45%-55% |
| Oracle footprints + closed theorem acceptance specialty | 65%-75% |
| T4 proofterm replay/checker | 10%-20% |
| HOL tools and automation | 10%-20% |
| PIDE/session ecosystem | 5%-15% |

Use the implemented contracts, remaining gates, and observed sampled outcomes
instead of these estimates. Do not market the project as "Rust Isabelle" or
"feature-compatible with Isabelle".

## Known T2 Debts

These are trusted-boundary issues that T4 replay does not automatically solve:

| Debt | Why it matters | Correct direction |
|---|---|---|
| `compat_alpha_eq` Free/Const suffix matching | Still available for legacy parser/loader compatibility, but no longer used by trusted kernel equality. | Fix parser/loader/type annotation, then remove/narrow compat usage. |
| `compat_alpha_eq` Var/Free matching | Still available for schematic-variable parser gaps, but no longer used by trusted kernel equality. | Align theorem DB/parser representation of schematic variables. |
| Transitional source status/shape metadata | `parse_term` now requires complete lexical and syntactic consumption; only the separate diagnostic `parse_term_with_status` can retain an incomplete prefix. Neither source metadata nor complete parsing is name resolution or proof authority. | Keep the legacy adapter isolated; the strict source parser/elaborator handles the checked standalone TrueI and Pure identity source slices, not general HOL/Isar or every legacy caller. |
| `Typ::dummy()` in legacy kernel consumers | Lets ill-typed legacy terms remain too long; the isolated strict kernel has no dummy constructor. | Make parser/type inference/CTerm certification produce well-typed certified terms. |
| Best-effort `CTerm::certify` call sites | Legacy paths can still wrap dummy-tainted terms. | Use checked certification and real derivations; complete-source failures must reject. Only explicit legacy search/diagnostic paths may retain admitted results. |
| Kernel to legacy conversion (`src/core/kernel_convert.rs`) | Untrusted compatibility-only adapter, moved out of `src/kernel/`; it still uses `Debug`/`format!` for type-name extraction and cannot convert Forall/Eq/Imp. | Replace debug-string logic with structural conversion before relying on it for migration; never treat conversion as proof authority. |
| Compatibility theorem taint | `_compat` constructors still exist for many old call sites. | Keep them searchable only; use `is_strict_closed_proved()` solely for transitional filtering and require `KernelTrustedClosed` for final trust. |
| `Option<Thm>` errors | Type mismatch and normal non-match can both become `None`. | Gradually move trusted boundaries toward `Result<Option<Thm>, KernelError>`. |

## Legacy T4 Replay Status

Supported replay rules in `src/core/proofterm.rs`:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

Current replay behavior:

- `Thm::check_proof()` reconstructs theorem shape and compares `prop`, `hyps`,
  `tpairs`, and `oracles`.
- `Thm::validate_proof()` uses the same burden-aware replay gate.
- `ProofBody::check(expected_prop)` is proposition-only compatibility code and
  is not a trusted theorem validation gate.
- `POracle` / admitted theorem replay fails for independent kernel replay.
- Unsupported rules fail explicitly; they are not silently trusted.

The former `hol_object_refl` and `true_def_transport` bridges and proof tags
were removed during the source-backed cutover. This six-rule legacy checker
is neither the isolated strict-kernel acceptance checker nor a full Isabelle
proofterm checker. Its remaining backlog includes proof reconstruction,
`PThm` expansion, compression, type abstraction/application, stored graph replay
and full legacy rule coverage.


## Historical Feature Branch Checkpoint (2026-07-21)

Commit `03d28a6` from `wip/kernel-trusted-slice` was integrated into `dev`
by merge commit `bc056ed`; this records history, not current branch existence:

**Delivered:**
- Recursive `is_concrete_type` with nested TypeVar test
- `is_monomorphic_instance_of` with `BTreeMap<TypeVarId, Ty>` + concrete check
- Atomic `AxiomDependencyId` = hash(basis_id, schema_id) — no longer "some basis exists"
- `prove_true_i` routes through accepted `True_def` theorem via `KernelRules::theorem_ref`
- 10 TCB attack tests: 5 polytype, 1 axiom dep, 4 conservative definition
- `strict` gate passes; `prove_true_i_succeeds` with dest_app-based proposition check

**Completed (2026-07-21):**
- `ConservativeDefinition` is atomic via `DefinitionId` stored in `TheoryExtension::DefineConst`. Replay walks owner ancestry to find the certificate.
- `PolyType::new` validates param sort consistency and requires every declared param appears in the body. `monomorphic_instance_matches` authorizes instances against params.

**Deferred at that checkpoint:** production source-to-kernel compilation and
sampled kernel acceptance did not yet exist. On 2026-10-07, the two standalone
fixtures and one audited `HOL::TrueI` projection from bundled sampled source
have accepted tokens. The latter is `1/125` in `scripts/dev-check.sh core`, not
whole-theory HOL compilation.

## Next Priority Order

The A–H program in [ROADMAP.md](ROADMAP.md#approved-native-compatibility-program)
owns delivery order. Preserve these invariants while maintaining the native
automation, continuing the approved Pure/ML closure work and addressing B's
offline evidence gaps; this list grants no additional implementation authority:

1. **Implemented:** keep exact `TheoryId` / `SignatureId` propagation and
   mixed-context rejection stable.
2. **Implemented:** keep the unique context/dependency-aware,
   conflict-safe, mutually exclusive `KernelTrustedClosed` acceptance gate
   stable; synthetic Pure tests remain outside the HOL benchmark.
3. **Narrow source-backed slice implemented:** the standalone TrueI CLI
   parses into a data-only AST, elaborates checked `CProp`, installs a minimal
   `refl` basis, defines True conservatively, and accepts the closed theorem.
   It does not implement general declaration parsing or polymorphic source
   annotations.
4. **Narrow sampled slice implemented:** the bundled five-file sampler checks
   the real source proposition, definition and proof for `HOL::TrueI` and
   records one owner-bound accepted token. The other 124 entries remain
   legacy/diagnostic; no general HOL compiler follows from this result.
5. **Automation implemented; quality blocked:** retain A's xtask cutover and
   address known quality blockers through explicitly scoped work, without
   lowering the official-source regression or global lint policy.
6. **B reference observed; closure incomplete:** retain the frozen Isabelle2025
   baseline and fill explicit evidence gaps only through independently approved
   offline inputs. Local official execution is disabled by the JVM-free policy.
   Native P2/P3/P4 implementation has resumed under P1; its scoped THM/ML
   evidence does not complete ROOT/HOL or compatibility acceptance.
7. Explicit borrowed search contexts and direct-child compute isolation are
   implemented repairs, not future prerequisites to reimplement. Keep their
   cache, ownership and cancellation boundaries intact.
8. Later theorem producers need individual source/owner/replay contracts.
   `HOL::trans` and any `2/125` work require separate soundness review; no
   legacy `Thm` relabeling or new HOL axiom follows from the current token.
9. Follow C–H for Pure, native ML, Isar/HOL, other logics/tools, product runtime
   and delivery evidence. Keep `src/core` hardening limited to migration and
   focused soundness fixes, not new trusted proof power.
10. ISIP remains design-only; broader session extraction, project-system and
    adapter work need their own reviewed contracts. Its old stages are not the
    A–H program and cannot substitute for official ML/PIDE compatibility.
Parallel non-blocking design track: high-performance symbolic compute may
define packed IR, a deterministic CPU baseline, and future optional Burn/CubeCL
backends. It must not add GPU/backend dependencies to the kernel, produce
trusted theorems, or delay the strict-kernel / resolution / admitted-inventory
main line.

The accepted target architecture is recorded in
[ADR-0004](../adr/ADR-0004-layered-platform-architecture-v2.md);
[ADR-0002](../adr/ADR-0002-layered-platform-architecture.md) is superseded.
See the [roadmap](ROADMAP.md) for dependency-ordered phases.

## Verification Record (2026-10-03)

This and the subsequent dated records preserve historical observations.
For the post-xtask implementation checkpoint, use the
[A-package record](#xtask-automation-cutover-2026-10-11).

This is a dated execution record, not a perpetual green-worktree or release
claim. The declaration/proof-result implementation was checked as follows:

| Check | Observed result | Boundary |
|---|---|---|
| `scripts/dev-check.sh strict` | Passed: 578 tests and 11 effective doctests; one existing ignored example | Includes isolated-kernel zero-warning and dependency-boundary checks, not every frontend test |
| Proof, automation, and loading contract suites | 71 passed across eight suites | Supported public contracts, not general Isabelle compatibility |
| Final legacy consumer regressions | Four passed | Complete propositions and malformed-input behavior |
| Both `isabelle-build` fixtures and demo | Passed; the fixtures returned their respective accepted tokens | Outside the sampled 125-theorem batch |
| `scripts/dev-check.sh core` | Library and binary both reported 1/125 transitional, 0/125 kernel-trusted | Historical admitted-reason distributions are separate |
| Global format/build | Passed | Does not establish runtime correctness |
| `cargo audit` / `cargo deny check` | Passed | Rust dependency audit, not the vendored editor lockfiles |
| Global Clippy | Failed: 96 root-library diagnostics under `-D warnings` | Isolated-kernel zero-warning gate passed separately |
| Global gitleaks | Failed: one upstream Haskell function-text match, inspected as non-credential | The failed scan was not converted into a pass or suppressed |
| Global Trivy | Failed: 13 findings in upstream VSCode lockfiles | No findings reported for root `Cargo.lock` in that run |
| Full tests | First run OOM-killed at about 9.3 GiB anonymous RSS; single-thread retry timed out after 3600 seconds | No complete `cargo test` success claim |
| Official Isabelle runtime differential | Not run: executable unavailable | Rust CLI/source review is not official-runtime proof |

After documentation synchronization, `scripts/dev-check.sh docs` passed:
87 Markdown files satisfied the snippet and local-link checks, four standalone
design templates compiled, and fmt/check passed. This proves neither
production API compatibility for the templates nor the complete quality gate.
Current work still needs fresh full-gate results before a commit; this record
does not authorize bypassing a commit hook, suppressing findings, or reducing
test coverage. Independent correctness/security reviews found no remaining
finding in their reviewed implementation slices, not an absence of all project
defects.

### Scoped scanner risk acceptance (2026-10-03)

The user authorized narrowly scoped exceptions for this Rust-only verification
workflow, **not** remediation or a claim that upstream editor dependencies are
safe. The repository maintainers own review by **2026-11-03**, on any
`isabelle-source` Gitlink change, and before building or distributing an editor
extension. The upstream Isabelle2025 checkout is
`765fb2460a57eb46e8490283241ad46f1fac857f`.

- `.gitleaksignore` matches only the `generic-api-key` finding at
  `src/Tools/Haskell/Haskell.thy:3255` under that Gitlink. The matched
  `publish_stdout` function parameter is named `password`; the source does
  not contain a literal credential. This fingerprint is not content-bound,
  and the review date is a manual obligation, not an automatic expiration.
- `trivy.yaml` enables `.trivyignore.yaml` and shows suppressed findings.
  Thirteen entries cover 12 distinct CVE IDs at exact upstream editor
  lockfile paths, package versions, and PURLs, each expiring 2026-11-03.
  Trivy 0.74.0 reported **0 active and 13 ignored vulnerability entries**
  with these exceptions; all 13 still affect the pinned packages. The
  two `CVE-2022-25883` entries are separate `semver` versions and lockfiles.
  No root `Cargo.lock` finding was reported in that scan. Editor/VSIX
  delivery must run an unexcepted audit and address those vulnerabilities.

The baseline failures above remain recorded because exceptions are risk
acceptance, not fixes. Standard project and shared validators must still
finish successfully; their results are recorded separately.

## Bounded Diagnostic Record (2026-10-07)

The separate `isabelle-profile-hol` worker and the then-current
`scripts/profile-hol.sh` established a manifest-pinned historical diagnostic
baseline, not a reproduction of an unrecorded HashMap order or a performance
fix. The maintained Rust invocation is
[`cargo +stable xtask profile`](../../scripts/README.md#bounded-hol-diagnostics).

- Ten manifest tests and eight Linux supervisor tests passed. These cover
  source/context changes, conflicting source identities, quoted legacy theory
  names, replay budgets, timeout-like worker exit codes, output permissions,
  output limits, queued startup cancellation, and descendant reaping.
- A direct supervised small-source run and replay both exited 0 and reported
  `Admitted(proof_engine_failed)`. Diagnostic completion did not promote this
  result to a proof.
- The real `HOL::TrueI` diagnostic captured 200 preloaded sources from the
  Isabelle2025 Gitlink and 183 bootstrap sources from `theories/`. With a
  120-second wall limit and 4096 MiB per-process address-space limit, creation
  and replay both exited 124 with `timed_out`, before target proof search.
  Bootstrap took 103.960 seconds initially and 100.370 seconds on replay.
  The last started load was `HOL` initially and `Cong` on replay.
- GNU time measured the replay at 120.05 seconds wall time, 119.53 seconds user
  CPU, and 212660 KiB maximum resident set size. This truncated run does not
  measure the complete verifier's peak memory or establish its only hotspot.
- Independent correctness/security reviews identified target-parse context,
  conflicting theory-source identity, and output-directory permission defects;
  these were corrected. The latter two have failing-before/passing-after
  regressions. Namespace tests check host PIDs and require `/proc` entries to
  be absent immediately after the supervisor has been reaped.
- The project `docs` gate passed after adding the entry point: 87 Markdown
  files, four standalone design templates, formatting, and locked compilation.
  This scoped record does not establish full tests, global-gate success, an
  official Isabelle runtime comparison, or a new sampled accepted theorem.

## Search Acceleration Gate (2026-10-07)

A bounded 85.6-second `cpu-clock:u` sample of the five-theory core verifier
captured about 8,000 samples. Flat hot symbols were `memmove` (16.91%),
`Arc<str>` clone (10.84%), allocator/free paths, and type copying. No fact
prefilter or rewrite-candidate loop appeared above the 0.8% report threshold.
The truncated core workload alone cannot establish the profile of broader HOL
proof search. A second supervised profile of real `Set::CollectI` source with
the recorded full bootstrap finished in 143.4 seconds: bootstrap took 102.5
seconds, file loading 36.9 seconds, and search 3.0 seconds. Its diagnostic
result was `Admitted(proof_engine_failed)`, not a proof. Flat CPU hotspots were
still source masking/character scanning and copying across the whole run; the
3-second search interval was not profiled separately. These measurements do
not justify a packed candidate index, SIMD, or GPU offload. The CPU
batch-filter gate remains open pending a measured candidate-heavy consumer
and a complete-path comparison. An available NVIDIA
RTX 4060 Laptop GPU is not by itself evidence of acceleration or isolation;
no device backend is enabled on this basis. Neither the profile nor any
candidate computation authorizes trusted theorem acceptance.

## Experimental LSP Hardening Checkpoint (2026-10-07)

The protocol adapter now uses a bounded shared CPU work queue for document
checks and definition lookups. Open-document revisions and request identities
are checked at commit; replacement, rejected full sync, close, duplicate
outstanding request ID, and shutdown cancel queued definition responses.
A per-thread symbol cache retains at most 4096 names / 64 KiB of name text,
with names over 1 KiB uncached. This bounds the cache, not process RSS.
HOL loading progress uses tracing rather than synchronous stderr writes.

The targeted symbol, scheduler, handler, manifest, automation, and LSP contract
tests passed. A freshly rebuilt `isabelle-rs --lsp` binary returned a single
`-32600` for a duplicate pending definition ID and answered shutdown, exiting
zero. The `strict` gate passed, and the bundled five-theory `core` run still
reported one kernel-trusted token, zero transitional, across 125 candidates.
The `docs` gate passed. Independent correctness and security reviewers found
no new actionable issue in the LSP slice; this is scoped review, not a
whole-project safety proof.

The first shared-validator attempt passed secrets, formatting, build and
dependency audits, but Clippy found six diagnostics and the full-test gate
exceeded a 900-second wall limit. After the lint fixes, a post-lint run
passed secrets, formatting, Clippy, build, and all dependency audits; the
workspace test gate still exceeded a 180-second bounded run. Direct serial
`cargo test --lib` output identified its first long-running test as
`hol::theory_graph::scale_tests::test_load_1000_from_full_hol`: this test
scans and loads up to 1000 upstream theories and has no pass/fail assertion.
The bounded run stopped while this test was running, not after completing
the library suite; other scale experiments may also be slow. The historical
OOM / 3600-second single-thread results remain distinct. No completed
full-suite result or valid full-validator success stamp is claimed.

At this earlier checkpoint, Stage 3 still lacked a process boundary: legacy
commands and global HOL DB initialization could outlive adapter shutdown.
The measured core workload did not justify a packed CPU candidate index;
no GPU backend was enabled.

## Experimental Compute Process Cutover (2026-10-07)

The built-in `RealExecutor` paths in LSP and Session now send checks through
a reusable `--compute-worker` child. LSP definition lookups also run there;
custom executors stay cooperative and in-process. The child returns display
diagnostics and proof-state snapshots, not trusted theorem tokens. IPC checks
protocol/build identity and request IDs, caps input at 1 MiB and output frames
at 8 MiB, and serializes shared proof states by reference so repeated snapshots
cannot be deep-copied before the output cap takes effect. Stale document
lifetimes, cancellations, and worker failures cannot publish successful
snapshots. Cancel/close/shutdown kills and reaps the direct child; cleanup
failure is returned instead of reporting successful shutdown. Session retains
cleanup failures across cancelled replies and shutdown join timeouts; worker
diagnostics also report failures if the owner has already detached. A fatal
LSP worker failure ends accepted pending definition requests with errors before exit.
Session's built-in executor requires an explicit trusted worker path via
`Session::new_with_worker`; `Session::new` rejects it rather than guessing an
embedding application's executable. The CLI supplies its own binary to LSP.

This is failure isolation, not a privilege or memory sandbox: the worker
inherits the parent's credentials/environment and current directory; it has
no OS RSS limit or per-request wall-time limit for a running LSP check. A
trusted child spawning descendants is not covered by direct-child reaping.
Stage 3 remains unaccepted until the final behavior checks, independent review,
and complete quality gate finish. Stage 4 still needs a measured candidate-
heavy consumer before a packed CPU index is justified; no GPU backend is enabled.

The targeted compute IPC, Session, scheduler, handler, real-process LSP,
real-process Session, and LSP protocol tests passed after the process cutover
and fatal-failure fix. The strict gate passed;
the bundled core sampler reported `KernelTrustedClosed: 1/125` and
`TransitionalStrictClosed: 0/125`. The docs gate passed. Live LSP
smokes: from `/tmp`, a pending-lemma diagnostic, null definition lookup,
and shutdown with exit 0; from an isolated one-theory temporary directory,
`TrueI` resolved to `file:///theories/Tiny.thy` at line 1, followed by
shutdown with exit 0. A repository-CWD smoke attempting an uncancelled
definition lookup exceeded its 30-second response wait and was stopped;
full HOL definition lookup latency remains unmeasured by the small fixture.
Independent scoped correctness review accepted the fatal-cleanup follow-up;
security review found the original pre-frame memory amplification removed.
Neither review is a full-project safety proof or an OS memory bound.

A channel-gated Session regression reproduced cleanup-error loss after a
shutdown join timeout before the fix, then passed with the same error retained
on retry. This injects a worker exit result, not an operating-system kill/wait
failure. Scoped independent review accepted the error-retention follow-up.
A repository-CWD live LSP smoke observed CPU activity in the HOL lookup child,
then received the module-symbol response in 0.55 ms and cancellation in
0.34 ms; shutdown took 9.56 ms, exited 0, and the child no longer existed.
Only one definition response was observed. Sampled `/proc` high-water RSS
at that point was 9,248 KiB for the parent and 9,516 KiB for the child, not
whole-workload peaks or resource limits. No throughput improvement is claimed.

## Regression and Diagnostic Separation (2026-10-08)

With explicit approval to change the default test boundary, six report-only
HOL workloads moved to supervised `isabelle-scale-hol` modes. Their original
input selections, search budgets and classification remain; no `#[ignore]`
was added. The assertion-backed core sampler and other functional/trust
contracts remain default tests, including the existing tier targets. Exact
mode mappings and limitations are in
[the diagnostic guide](../../scripts/README.md#report-only-scale-workloads).

Before this separation, the complete shared validator passed secrets,
formatting, Clippy, build and dependency audits, but its test phase exceeded
600 seconds and last reported `test_diag_structured_proofs`. It did not
produce a successful validation stamp. A separate cancelled validator had
left cargo/test descendants; their PIDs and output-file ownership were
checked before they were terminated. This history is not a post-migration
full-suite result.

A controlled five-file batch was run through the old test executable and
the migrated worker with identical source files. Both reported the same
file order and `TransitionalStrictClosed: 0/5`. This small equivalence smoke
is not the original full HOL workload or a performance measurement.
The supervisor/manifest regression suites passed all 25 tests. Three added
input-boundary cases failed before their fixes and passed afterward:
option-like modes, directory-shaped source markers, and empty conflicting
arguments. Scoped correctness and security reviews found no remaining
blocking issue in this migration.

All six actual modes were exercised under a 2 GiB per-process address-space
limit. List sampling, four List induction attempts and full-upstream failure
analysis completed. Structured/global-DB and first-five-file diagnostics
reported `timed_out` at 10 seconds; the Nat sample did so at 15 seconds.
The batch log reached `BNF_Cardinal_Arithmetic.thy`; the structured log was
still in global DB loading. No scale worker remained after the runs.
The completed diagnostics did not establish proofs: List reported `0/10`
transitional, induction results were accepted/open, and the upstream
classifier reported 1,461 syntax-error files. No proof-coverage, throughput
or full-workspace-pass claim follows from this separation.

The post-separation complete shared validator again passed secrets,
formatting, Clippy, build and all three dependency-audit commands. Its
600-second outer deadline expired during the workspace test phase, whose
last line was `isar::linarith::tests::test_solve_ineq_trans`. This run used a
private PID namespace with its own `/proc`; no validation cargo/test process
remained afterward. No successful validation stamp or full-suite pass was
produced. The last test name alone does not establish how much of the
deadline that test consumed.

A bounded exact-test diagnostic used temporary timing markers and a 4 GiB
address-space limit: global DB initialization returned after 98.94 seconds,
but the arithmetic call had not returned at the 120-second deadline. At that
point the markers were removed without changing the test or search inputs.
A separate 60-second profile captured 5,946 CPU samples, with hot symbols in
source masking, character-prefix checks, UTF-8 iteration and memory copying.
It is not a completed arithmetic benchmark or evidence for packed candidate
filtering. The existing test asserts only non-empty output; because
`arith_tac` can return the unchanged state, that assertion alone does not
prove arithmetic success.

A subsequent local optimization dispatches formal-comment prefixes by the
first character, avoiding four failed ASCII-prefix comparisons for ordinary
characters. It does not change token forms, whitespace rules, source
selection, search budgets or proof classification. Independent correctness
and security reviews found no scoped blocking issue.
An isolated executable compared the actual old/new helpers over every
Unicode scalar, partial ASCII prefixes, EOF/invalid offsets, and all 640,958
character positions in the five bundled source files. Results were identical.
Three alternating-order helper scans measured 108.2–116.1 ms versus
10.5–12.8 ms in a dev build, and 0.767–0.796 ms versus 0.561–0.619 ms in
release. These are helper-only measurements, not whole-loader or proof-search
speedups. All 44 existing source-boundary tests passed before and after;
the rebuilt supervised List diagnostic completed and still reported `0/10`
transitional results. Full-workspace acceptance remains separate.

After that optimization, the strict, core and docs project gates passed;
the core result remained one kernel-trusted and zero transitional outcomes
out of 125. The final complete shared validator again passed all pre-test
gates but exceeded its 600-second deadline at the same arithmetic test.
Its process tree was reclaimed, and no successful validation stamp was
produced. The local parser cost reduction did not clear full-suite acceptance.

## Arithmetic Acceptance Contract Repair (2026-10-08)

With approval to repair the arithmetic test contract, six nonempty/length-only
tactic checks were replaced by isolated regressions using declared HOL
constants, `HOL.Trueprop` judgments and checked proof obligations. Without an
arithmetic basis, those goals must remain unproved. The existing 26 constraint
and Fourier-Motzkin unit tests remain, as does default global database coverage;
this is not another diagnostic migration, a new ignore, or a search-budget cut.

The repair exposed a real consumer bug: `ArithSolver` had initialized the goal
with `assume_compat` and treated zero premises as success. Six of ten initial
contract tests failed before the fix. It now uses checked certification and a
trivial obligation, accepting only the complete goal under the explicit context's
authorized hypotheses through the existing proof-result validator. It adds no
HOL axiom, arithmetic proof rule or strict-kernel accepted token.

All 16 final arithmetic regressions and 17 neighboring automation regressions
passed. The 26 retained FM tests passed separately. The unchanged default global
index integration loaded 11,168 named entries and passed in 55.50 seconds; this
does not certify those entries or measure a comparable end-to-end speedup.
An independent public-API executable observed rejection of an unproved atom
and a database-only assumption, an explicitly authorized local result retaining
one hypothesis, and a checked Pure reflexivity result with no hypotheses.
Scoped correctness and security reviews found no blocking issue. The strict,
core and docs project gates passed; sampled outcomes remained one kernel-trusted
and zero transitional results out of 125.

The subsequent complete shared validator passed all seven pre-test checks and
no longer timed out at arithmetic. Its library suite finished in 242.79 seconds:
891 passed, one failed, and eight existing tests remained ignored. The sole
failure was an outer-syntax test treating the now-supported method punctuation
`?` as a lexical error; no full-suite pass or successful stamp was produced.

That assertion was moved to the actual whole-file acceptance boundaries rather
than changing production parsing: strict HOL/Pure builds reject `end ?`, and
the legacy loader discards staged theorems on that suffix. Malformed lexical
suffix checks remain. The nine outer-syntax tests, 18 trusted-loader tests and
16 theory-load contract tests passed. The rebuilt `isabelle-build` accepted both
unchanged fixtures and rejected both `end ?` variants with exit 1 and no token.
These scoped results do not substitute for the complete shared gate.

After the suffix-test correction, independent correctness and security reviews
found no scoped blocker, and strict/core/docs passed again. The next complete
shared gate passed the same seven pre-test checks. The library suite completed
with 893 passed, zero failed and eight existing ignores in 236.80 seconds;
arithmetic, automation and diagnostic-supervisor integration suites also passed.
The gate then failed at `tests/integration_tests.rs::test_batch_verify_core_files`:
the old assertion requires nine upstream HOL files to avoid `SyntaxError`, while
the supported whole-file loader rejects the official HOL header's leading
`section` command before reaching its multiple imports and other unsupported
declarations. The validator exited with failure after 305.32 seconds, not a
timeout; no successful stamp was produced and no validation processes remained.
This is a remaining upstream-capability contract conflict, not evidence of
broader HOL acceptance. The nine-file assertion has not been relaxed or skipped.

A separate bounded `--no-fail-fast` run exercised the remaining legacy proof,
LSP, property, search-context, Session and ATP integration targets: all 84 tests
passed. Tier2's single statistics test also completed in 403.26 seconds. Tier3
had not finished when the combined diagnostic's 600-second deadline expired;
that is not a measured 600-second Tier3 duration. Its process tree was reaped.
At that point, both scale tests only asserted that at least one file was
processed; their success was not a theory-build or proof-coverage guarantee.
No Tier2/Tier3 target, source list, search budget or default-test registration
had been changed in that run.

The separately executed root doctests exposed nine failures: three Rust examples
lacked usable imports, and six Isabelle formula blocks were mislabeled as Rust.
Only documentation changed: public imports were repaired, and the formulas were
retained as `text` blocks. All 17 actual Rust doctests then passed, with zero
failures or ignores; the docs project gate also passed. This removes a separate
documentation blocker, not the upstream integration or scale-workload blockers.

## Tier Statistics Diagnostic Migration (2026-10-08)

The user explicitly retained the nine official HOL files' no-`SyntaxError`
compatibility requirement. It remains a default regression and a delivery
blocker until the actual loading capability satisfies it; rejection alone
must not be substituted for that requirement.

Separately, the user approved moving Tier2/Tier3 statistics out of default
tests and into supervised `isabelle-scale-hol tier2` / `tier3` modes. The
active input sequences, Tier2 per-file deadlines and adaptive `AUTO_LIMIT`,
Tier3 search behavior, and counters remain the diagnostic contract. No
ignore, proof-search budget reduction, trusted theorem power or change to
the nine-file compatibility assertion is authorized by this migration.

The migrated module preserves all 97 Tier2 path/budget pairs and all 30 Tier3
paths in their original order, checked against copies of the original tests.
The original and migrated runners were also executed under the same supervisor
against controlled first/last-list fixtures. Each tier processed two files,
attempted two unproved lemmas, and counted zero proofs before and after;
Tier2's separate trust counters were also unchanged. This is an equivalence
smoke, not coverage of the full HOL source set.

All 16 supervisor contracts passed, including empty Tier2 input, unreadable
Tier3 input, hard timeout and descendant cleanup. Formatting and ShellCheck
passed, and independent correctness/security reviews found no scoped blocker.
Cargo metadata registers 28 integration targets without the obsolete two
statistics tests; the compatibility, arithmetic, supervision, LSP and Session
contract targets remain registered.

The actual `scripts/dev-check.sh tier3` entry was run with a 30-second wall
budget and 4096 MiB per-process limit. It returned 124 with
`supervisor.json` reporting `timed_out` and `scale_mode: tier3`; no Tier3
worker remained afterward. This verifies bounded termination, not completion
of the 30-file workload or a speed improvement.

The full-input Tier2 entry did not finish within the default resource envelope:
after 146.41 seconds it aborted on `memory allocation of 88 bytes failed`
under the 4096 MiB address-space cap. The supervisor returned 134 and recorded
`error`, not `completed` or `timed_out`; no Tier2 worker remained. The default
cap is a safety bound, not a guarantee that the complete source set will fit.
An explicit 8192 MiB retry was terminated with exit 143 and supervisor
classification `error`; no worker remained. It produced only partial output,
so neither full Tier2 completion nor adequacy of that larger cap is established.

The post-migration strict, core and docs project gates passed. The sampled
result remained one kernel-trusted and zero transitional outcomes out of 125.
These scoped results do not clear the full-workspace compatibility requirement.

Before the final shared validation, `Cargo.lock` no longer matched its
start-of-migration fingerprint, despite no intentional dependency edit or
upgrade in this migration. Its origin was not established; it was preserved,
not reverted or claimed as part of the migration. `Cargo.toml`, the nine-file
integration test and `scripts/profile-hol.sh` still matched their initial
fingerprints. Any subsequent full-gate evidence applies to the current lockfile.

### Final shared-gate result (2026-10-11)

The bounded docs-plus-full-validation command returned exit 1 in 461.06
seconds, not a timeout. The docs gate passed; the shared validator reported
six checks passed and two failed. Gitleaks, formatting, Clippy, workspace
checking, `cargo audit` and `cargo deny check` passed.

Trivy initially failed to download its vulnerability database with
`unexpected EOF`. Retrying the same scan scope and policy succeeded:
the scanned Rust lockfile had no reported vulnerabilities. The existing
13 upstream editor findings remained explicitly suppressed by the prior
Rust-only risk acceptance; no exception was added or broadened. This
standalone retry does not turn the failed full run into a passing gate.

The library suite passed 893 tests with zero failures and eight existing
ignores in 302.61 seconds. Arithmetic (16), automation (9), rewrite (8),
manifest (10) and supervisor (16) contract tests also passed. The general
integration target passed seven tests and failed
`test_batch_verify_core_files`: the actual official `HOL.thy` was rejected
at its leading `section` with `Expected 'theory' at position 96`.
The nine-file compatibility assertion and its inputs remain unchanged.
Later test targets were not reached by this fail-fast run; their earlier
scoped results are separate evidence. No successful validation stamp or
commit was produced, and the compatibility requirement still blocks delivery.

## xtask Automation Cutover (2026-10-11)

This is historical package-A evidence, not a run of the current all-Rust
automation migration.

Package A of the [native compatibility program](ROADMAP.md#approved-native-compatibility-program)
introduces an independent `xtask` crate, not a new proof or parser path.
The explicit workspace contains the product, kernel and xtask; the default
member remains only the product. Offline locked metadata passed, and a
comparison with the pre-cutover lockfile found only the added xtask package
record, with all previous package records preserved. The kernel dependency
tree remains `sha2` plus `thiserror`.

CI/install commands and active guidance now use xtask; the old `dev-check.sh`
and `check-strict-kernel.sh` orchestration files were removed. Their dated
historical results above remain evidence for the old invocations. CI matrix,
advisory properties, release artifact paths and release permissions are unchanged.
The product demo changed only its obsolete verification-command hint.

Observed package-A evidence:

| Check | Result and boundary |
|---|---|
| `cargo +stable xtask selftest` | 18 passed: real-process failure aggregation, dependency blocking, spawn/signal errors, artifact selection/stale-worker rejection, CLI/version validation and firewall execution errors. |
| Root and subdirectory `help`, `check`, `build` | Passed. Help bootstrapped only xtask and its small dependencies. `check --all-targets` also passed. |
| Toolchain inheritance | Current nightly `cargo xtask check` passed, separately from canonical stable calls. Direct Cargo/Rustc paths also passed check/build without invoking the rustup shim for those commands. |
| CLI fixture smoke | The actual Cargo-reported `isabelle-build` executable accepted `TrustedTrueI.thy` and `TrustedPureIdentity.thy`; demo displayed the new command. |
| Supervised Tiny/Context profile | Actual custom `CARGO_TARGET_DIR` with spaces, fresh output, and relative-path manifest replay completed. Budget stayed `auto_limit=1`; result remained `Admitted(proof_engine_failed)`, `proof_authority=false`, not a proof. |
| Supervisor cancellation baseline | Existing 16 deterministic supervisor tests passed before migration; no new parent-PID cascading-cancellation claim. |
| Output failure | Real `/dev/full` stdout and stderr cases both returned 1, not success or a panic exit. |
| `cargo +stable xtask strict` | All 14 actual steps passed, retaining the old gate inventory including kernel zero-warning checking and firewall. |
| `cargo +stable xtask core` | Passed; `KernelTrustedClosed: 1/125`, `TransitionalStrictClosed: 0/125`, unchanged. |
| `cargo +stable xtask docs` | 87 Markdown files, four standalone templates, workspace formatting and root check passed. Template compilation is not product API compatibility. |
| `cargo +stable xtask lint` | Both existing root CI policy and strict xtask Clippy passed. Existing kernel dependency Clippy warnings and test-only root warnings were not suppressed. |
| Static configuration/shell checks | Workflow YAML and harness JSON parsed; Bash syntax passed. ShellCheck still reports pre-existing unused `PLATFORM` in `install.sh`; no unrelated installer cleanup was made. |
| Independent reviews | Correctness and security reviews approved after three minor findings were fixed; neither review is a dependency or secret scan. |

The complete `cargo +stable xtask test` run finished in 285.34 seconds with
exit 1. The root library passed 893 tests with eight existing ignores; the
kernel's 158 tests and all 18 xtask tests passed. `--no-fail-fast` continued
through the remaining targets and doctests. Only `integration_tests` failed:
`test_batch_verify_core_files` rejected official `HOL.thy` at position 96,
where legal `section` precedes `theory`. No new ignore or altered assertion
was used to hide this compatibility failure.

The subsequent full `RUSTUP_TOOLCHAIN=stable ~/.omp/agent/validate.sh` run
finished in 302.07 seconds: **6 passed, 2 failed, 0 skipped**. Gitleaks,
format, workspace build, Trivy, Cargo audit and Cargo deny passed under the
existing scan policies. Strict global Clippy failed with 121 diagnostics
in the now-workspace kernel (including `result_large_err` and style lints);
the narrower CI lint policy passing does not waive this gate. The global
test gate again failed at the retained official-source assertion and did not
reach later targets; the complete no-fail-fast run above is separate evidence.
No successful validation stamp was produced. Fixing kernel APIs or expanding
source-language support is not part of this automation-only cutover; these
remain explicit delivery blockers, not a reason to lower the quality gates.

No full Tier2/3 workload was rerun for wrapper proof. macOS/Windows runtime,
PowerShell execution, a genuinely rustup-free host, and a missing-stable
toolchain environment were not available for execution. No installer
network/update branch, commit, tag, push, release or external corpus download
was performed. Full-project acceptance remains separate from this automation
evidence; the retained official-source compatibility requirement was not weakened.

## Recommended Project Description

Use this in papers, README summaries, or external descriptions:

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel evolving into a layered proof engineering platform.
It focuses on explicit oracle footprints, closed-theorem acceptance,
proof-object replay, and agent-native proof interaction rather than broad
Isabelle/HOL feature parity.
```

Avoid:

```text
Rust rewrite of Isabelle
Feature-complete Isabelle/HOL in Rust
Full Isabelle-compatible prover
```
