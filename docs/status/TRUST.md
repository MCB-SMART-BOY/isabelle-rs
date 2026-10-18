# Trust Model

Core promise:

```text
The system must not lie about what was proved.
```

Search and diagnostic paths may retain an unproved proposition only through an
explicit oracle/admit footprint. Complete source compilation instead rejects
unsupported or unproved input; it does not fall back to admission. Open theorems,
admitted facts, search records, and closed proved lemmas remain distinct.

Agents should read root [AGENTS.md](../../AGENTS.md) first. This document should
then be read together with
[PROJECT_STATUS.md](PROJECT_STATUS.md),
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md),
[KERNEL_RULES.md](../kernel/KERNEL_RULES.md), [KERNEL_PRIMITIVES.md](../kernel/KERNEL_PRIMITIVES.md),
[RESOLUTION_DESIGN.md](../design/RESOLUTION_DESIGN.md), and
[KERNEL_ATTACK_TESTS.md](../kernel/KERNEL_ATTACK_TESTS.md).

## Current Position

Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired LCF
kernel. The current trusted-engineering focus is:

1. non-forgeable theorem construction;
2. sound primitive inference boundaries;
3. explicit oracle/admit propagation;
4. closed theorem acceptance;
5. proofterm replay.

It is not a full Isabelle proofterm checker or a feature-complete Isabelle/HOL
implementation.

### Rust THM variable transformations

局部固定类型/项可经 `generalize` 和显式 `export_scope` 返回 owner scope。
scope capsule 只能由内核 context 创建，记录原 stamp 与声明但不授予 proof；
接受仍完整回放其来源、重建依赖，并在无 local 声明的 owner 重认证输出。
词法 typed-Free 授权按精确 `(Name, Ty)` 和 binder 来源隔离；类型变换、
RHS 复制、同 key 合并不丢来源，退出 binder 撤销其全部派生授权，
不删除独立外层授权。bound checker 的私有 context view 只接收已验证来源环境，
不从候选结果、ML 值或 metadata 创建权限。
proof-only 局部参数也须经过确定性泛化后逐 operand 检查。

泛化/索引变换不删除真实假设、sort/flex/pending 义务；类型先泛化、项后泛化
与两种类型实例化均须走同一 replay/accept 路径。具体规则和索引限制见
[变量变换合同](../kernel/KERNEL_PRIMITIVES.md#generalize--固定类型与项的统一泛化)；
Rust consumer 证据不是完整 Isabelle/ML、ROOT 或九根兼容验收。

这两个外部 Rust consumer 的实际闭环、拒绝测试与剩余失败以
[2026-10-18 首个闭环](PROJECT_STATUS.md#first-native-rust-thm-closure-2026-10-18)、
[2026-10-19 变量闭环](PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19)
及 [THM 逐项清单](NATIVE_THM_INTERFACE_INVENTORY.md) 为准；
`src/ml/host/context.rs` 的局部 Context 替换不代表完整 `Thm: THM` 或 ROOT 已运行。

## P1 Native Trust Design

**P1 设计已批准，部分 Rust 内核能力已分段实施；这不是九根闭包/完整兼容的运行验收。** 固定 Isabelle2025 `765fb2460a57eb46e8490283241ad46f1fac857f` 的九根及完整依赖闭包必须原样由 native Rust 执行；上文和下文的历史采样、单个 `HOL::TrueI`、P0 官方 snapshot/探针不因此变成新证据，也不提供 theorem authority。`crates/kernel/` 是唯一 TCB，`src/core/`、ML VM/THM/Context、源 hash、官方 heap/exit、solver 输出、报告均不能 seal theorem。P1 的 C1–C7 已报告设计 Major/Blocker 经定向复审收敛（C4 最后 owner/Γp/SemanticArity 和 composition 的 no-flatten/异常修正也已限范围批准）；Rust checker、宿主、十二 witness 和完整闭包仍须独立审查和真实运行。内核规则/完整负载见 [P1 kernel 合同](../kernel/KERNEL_PRIMITIVES.md#p1-native-closure-kernel-contract-design)，证据缺口见 [P1 验收路由](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md#p1-design-and-implementation-gap)。

### P1 HOLBasisV1 policy

用户批准的**唯一**新增初始逻辑假设集合为下列 13 条 `HOLBasisV1` 精确 schema；每项登记全限定名、原始结构 AST (`Type/TVar/Const/App/Abs`，含 Pure/HOL connectives)、类型/sort、引入 owner 和 policy 版本，按固定源码 [HOL.thy](../../isabelle-source/src/HOL/HOL.thy)、[Hilbert_Choice.thy](../../isabelle-source/src/HOL/Hilbert_Choice.thy)、[Nat.thy](../../isabelle-source/src/HOL/Nat.thy)、[Set.thy](../../isabelle-source/src/HOL/Set.thy) 核对，不按表面字符串授权。HOL 项默认 `'a,'b::HOL.type`、`t,s,a,x,y:'a`、`f,g:'a⇒'b`、`P,Q:bool`；例外：`HOL.subst` 的 `P:'a⇒bool`；choice 的 `P:'a⇒bool,x:'a`；Nat 的 `x,y:Nat.ind`、`Zero_Rep:ind`、`Suc_Rep:ind⇒ind`；Set 的 `a:'a,P:'a⇒bool,A:'a set`。object `=`/`⟶`/`∨` 与 Pure `≡`/`⟹`/`⋀` 不可互换，所有省略的类型变量与 sort 由结构 schema 固定。

|批准的 basis slot|原始精确命题|
|---|---|
|`HOL.refl`|`t = (t::'a)`|
|`HOL.subst`|`s=t ⟹ P s ⟹ P t`|
|`HOL.ext`|`(⋀x::'a. (f x::'b)=g x) ⟹ (λx. f x)=(λx. g x)`|
|`HOL.the_eq_trivial`|`(THE x. x=a) = (a::'a)`|
|`HOL.impI`|`(P ⟹ Q) ⟹ P ⟶ Q`|
|`HOL.mp`|`P ⟶ Q ⟹ P ⟹ Q`|
|`HOL.True_or_False`|`(P=True) ∨ (P=False)`|
|`HOL.eq_reflection`|`x=y ⟹ x≡y`|
|`Hilbert_Choice.someI`|`P x ⟹ P (Eps P)`|
|`Nat.Suc_Rep_inject`|`Suc_Rep x = Suc_Rep y ⟹ x=y`|
|`Nat.Suc_Rep_not_Zero_Rep`|`Suc_Rep x ≠ Zero_Rep`|
|`Set.mem_Collect_eq`|`member a (Collect P) = P a`|
|`Set.Collect_mem_eq`|`Collect (λx. member x A) = A`|

`Nat` 两项连同 fresh `ind`、`Zero_Rep/Suc_Rep` 是真实 infinity 假设；`HOL.eq_reflection` 是 object/meta bridge 的独立 basis slot；Set 的 fresh `set`、`Collect/member` 和两项 Set slot 是整个签名/假设序列，不声称保守。每条原始 sorted schema 经原样 `more_thm.ML` 的 OFCLASS wrapper、sort-stripping、varify/recover、class 前提消除，必须分别逐节点检查并与 C4 唯一 export view 相联；这不是为 stripped 命题开放公理 API。第 14 条、新 class axiomatization、任意同名实例或名字/文件/hash 白名单一律 `UnapprovedAxiom`；任何真正新增公理须先单独审全限定名、完整命题、sort、引入 owner 与相对一致性并获批准。

`HOL.type` 本身仅 `EmptyClassDeclCert`（无 superclass/操作/局部公理）与非空 object carrier 语义。以下不是新的初始公理：`HOL.fun_arity` 用函数空间非空的 `FunctionTypeArityCert`；`HOL.itself_arity` 用单元素标签的 `ItselfArityCert`。17 个 `arity_type_*` 中五个是 fresh/type 声明路径：`HOL.arity_type_bool`、`Nat.arity_type_ind`、`Set.arity_type_set` 分别随准确 basis 声明序列，`SMT.arity_type_pattern`、`SMT.arity_type_symb_list` 使用独立 fresh 非空证书；其余十二个必须走带 parent witness 的 `TypedefCert`：`BNF_Cardinal_Order_Relation.arity_type_suc`、`Int.arity_type_int`、`List.arity_type_list_IITN_list`、`List.arity_type_list`、`Nat.arity_type_nat`、`Num.arity_type_num_IITN_num`、`Num.arity_type_num`、`Option.arity_type_option_IITN_option`、`Option.arity_type_option`、`Product_Type.arity_type_unit`、`Product_Type.arity_type_prod`、`Sum_Type.arity_type_sum`。前五不能冒充 typedef，后十二不能以官方存储项先出现而提前发布。对应十二项条件 extension 与父语言 witness 对照如下（仅源码提供的 proof 方案，**非 Rust replay 记录**）：

|conditional typedef 存储名|父语言 representing set `A` 与 witness 来源|
|---|---|
|`BNF_Cardinal_Order_Relation.suc.type_definition_suc`|`Field(cardSuc |UNIV::'a set|)`；`Field_cardSuc_not_empty/card_of_Card_order`，不含新 `suc`|
|`Int.int.type_definition_int`|`{c. ∃x::nat×nat. intrel x x ∧ c=Collect(intrel x)}`；`part_equivp_typedef`，父 nat/prod/set|
|`List.list.list_IITN_list.type_definition_list_IITN_list`|`UNIV::II_repT set`；`exI; UNIV_I`，不含 internal 新型|
|`List.list.type_definition_list`|`min_alg_list str_init_list`；`ex_in_conv/alg_not_empty_thms/alg_init_thm`，先提交 internal 型|
|`Nat.nat.type_definition_nat`|`{n::ind. Nat n}`；`Nat.Zero_RepI`，父 ind/Zero_Rep|
|`Num.num.num_IITN_num.type_definition_num_IITN_num`|`UNIV::II_repT set`；`exI; UNIV_I`|
|`Num.num.type_definition_num`|`min_alg_num str_init_num`；`ex_in_conv/alg_not_empty_thms/alg_init_thm`，先提交 internal 型|
|`Option.option.option_IITN_option.type_definition_option_IITN_option`|`UNIV::II_repT set`；`exI; UNIV_I`|
|`Option.option.type_definition_option`|`min_alg_option str_init_option`；`ex_in_conv/alg_not_empty_thms/alg_init_thm`，先提交 internal 型|
|`Product_Type.unit.type_definition_unit`|`{True}`；witness `True`，父 bool/set|
|`Product_Type.prod.type_definition_prod`|`{f.∃a b. f=Pair_Rep a b}`；父参数非空，representing-set 常量与新 tycon 不同|
|`Sum_Type.sum.type_definition_sum`|`{f.(∃a.f=Inl_Rep a)∨(∃b.f=Inr_Rep b)}`；父参数非空，新 tycon 不参与 A|

1,267 个 definition-associated 官方存储项只由各自受检保守定义/规则授权，7 个 Pure equality mirror 必须从已审 Pure.eq 基础和规则重建，不扩大 basis；13+2+17+12 的分类仅为固定源观察，不能通过数量或 `arity_type_` 前缀判定权限。完整 type/sort、四类模型 arity、条件 typedef 与 C4 class proof 证书见 [P1 kernel 合同](../kernel/KERNEL_PRIMITIVES.md#p1-c2-conservative-definitions-and-staged-typedef)。

### P1 Host authority and immutable context

本节是批准的目标语义和逐项验收要求，不是 Host 全接口已完成的声明。
当前 Rust 映射见 [THM 清单](NATIVE_THM_INTERFACE_INVENTORY.md)；
实际执行范围及未解除的前置条件以
[交付记录](PROJECT_STATUS.md#current-delivery-state) 为准。

用户批准完整替换固定 `isabelle-source/src/Pure/thm.ML:202-2747` 的**整个** `structure Thm: THM` 与 `context.ML:124-728` 的**整个** `structure Context: PRIVATE_CONTEXT`，不是局部 constructor bridge，也不解释原私有 Thm/Thy/Prf 表示；外围原 THM/Context signatures、`Basic_Thm`、data functors、`more_thm.ML`、普通 HOL 包和加载顺序保留。替换范围不等于授权任意新推理。Host `ctyp/cterm/thm/theory/proof context` 使用 VM 内私有、runtime/generation/phase 校验的不透明对象，真实 SML generative type stamp 和 namespace/type sharing 仍须满足公开签名，`conv = cterm -> thm`；整数、serial、record/bytes、Any、错误静态类型展示文本、可构造的 ML certificate wrapper 都不能恢复 Rust 句柄。`TrustedTheorem` 仅由 `accept_closed_theorem`，开放 ML `thm` 和 pending proof 不等于 accepted token。

用户随后批准以 Rust 实现替代 `Pure/General/sha1.ML` 的 C/Foreign 散列路径；选用工作区已锁定的 RustCrypto `sha1 0.10.7`，不自行设计算法。加载适配仅替换该外部实现，保留官方 `SHA1` 签名、`digest` 类型、`rep`/`fake` 与原八项加载自检；原始源码与实际转换执行内容分别记录，不能声称该文件完全原样执行。不开放通用 FFI，不修改固定 Gitlink，不向 `isabelle-kernel` 添加依赖。SHA-1 仅用于 Isabelle 兼容，不能作为定理授权或安全身份；证据文件身份仍使用 SHA-256。此条是实施授权，不是已通过 bootstrap 或兼容验收的证据。

用户另批准真实的类型驱动 Poly/ML 打印器实现，以支持原样
`ML_system_pp`/`ML_system_pretty` 和 SHA1 的打印回调。打印派发仅消费
编译器认证且按调用实例化的类型证据；闭包、functor、opaque sealing
和动态 namespace 必须保留各自类型身份。没有静态证据的公开
`Vm::apply` 调用不能按运行时值形状猜类型。注册表是 VM-local 的实际
callback 强根，替换与 GC、普通 ML 异常及不可恢复停止分别保留语义；
不改变 `Vm::apply` 的公开 API，也不增加宿主效果或 theorem 权限。
此项为实施授权，打印器及后续原样 ROOT 仍须实际运行验收。

内部 native callback 必须按认证调用的参数位置及 tuple/record 字段取得类型；
同一闭包可在不同位置具有不同多态实例，不能按 `Rc` 身份寻找第一个匹配项。
composition、Context data、打印器和编译器回调均传递相应认证输入类型；
公开无类型调用仍拒绝无证据的 weak/polymorphic/opaque 输入。
无类型入口先检查 callable 和参数所属 VM，再查类型；外来句柄不可用普通
`Type` 错误遮盖不可恢复停止。FileHostBridge 的 VM 绑定失败须撤销调用方与
bridge 所属域，失败后的读源和再次求值均不得恢复。
`PolyML.Exception.traceException` 成功时返回 action 结果；普通异常时返回
reporter 结果，reporter 可自行重抛。原 exception packet 和已发生的 ref
副作用保留；permission、停止或 fatal 不进入普通 ML handler/reporter。

THM 的所有公开函数必须提供真实语义而非假值：认证/transfer/trim 根据准确 owner 与类型/sort；`CONTEXT/CTERM/THM` 保留单一真实 SML exception identity、0-based ctyp 与 1-based premise 下标、负旋转和溢出边界、callback 次序及其已发生的 ref 副作用；trim 后仍应按公开 API 抛 `CONTEXT`，即使内核私存 owner。`rep_thm`、fold/proofterm/ZTerm 是**只出不进**投影，`Proofterm.proofs=0` 不删除 kernel 完整 DAG。普通 `Seq.make` 的重复 pull 重新求值、不得使用单次消耗 cursor/缓存异常；`RSN` 仅取至多两个结果区分 0/1/多。`add_oracle` 的注册可观察，调用默认结构化拒绝，不把 oracle 输出/solver exit 变 theorem。搜索、unifier、bicompose 只提交已列 core IR 候选；未知规则 fail closed。初始化 `Thm` 的 `at_begin` 缓存清理和 classrel/arity completion 仍需真实运行，K 在入图前检查完整 proof。

Context 的 ML identity/stage/有序父和 ancestry、immutable theory/proof data、`Theory_Data/Proof_Data` generative exceptions 与真实 init/merge callback、证书 full/trimmed、thread-local dynamic context、异常恢复、late-kind fallback 都由宿主保留；logical owner 与 ML serial 分离。`Context.make_parents` 首次输入次序、身份去重和覆盖祖先删除后，K 再独立核联合 DAG/class/Defs；callback **之前**必须绑定受检或真实 provisional logical state，callback 抛出的普通可捕获 SML 异常保留原异常及 ref 副作用，本次无新 context 返回但旧值可继续。异常逃逸构建边界、permission/cancel 或 fatal K invariant 才令本次构建不可逆失败；metadata `put` 本身不导入签名、owner 或 theorem。

typedef `RS` 仅生成同 tx `CommitReady`，不修改 lthy。原样 `Local_Theory.note -> Global_Theory.register_proofs -> Thm.register_proofs -> Proofs.map/put` 在 `Proofterm.proofs=0` 仍可由 immutable `Lazy.Value` 承载真实 theorem；**新** `Theory_Data.put` 的新 data 输入中仅扫描 immutable tuple/list/datatype/exception/已完成 lazy 值，不能执行 closure、读 ref/array/另一 context、反序列化 bytes、强制未完成 lazy。扫描只是证据候选：K 重放同一 tx、parent、完整 ledger、raw/recover、staged arity、唯一 Q witness/TD discharge、联合依赖/限制；有未决 reservation 不发布普通 owner。成功只生成携新 committed owner 的**新** context 值，旧 theory/proof context/aliases、旧 pending theorem 永不 mutable redirect/自动升级；原样全局与局部 `Thm.transfer` 显式逐节点用最终证书重放旧 proof，才能在新 context 引用/seal。无证据则保持 provisional，失败无 partial context 或 registry。完整上下文来源是仓库 `isabelle-source/src/Pure/{context,global_theory,more_thm}.ML` 和 `isabelle-source/src/HOL/Tools/typedef.ML`。

### P1 Effects, runtime barrier and fixed solver

所有 `Basis TextIO/BinIO/OS.FileSys/OS.Process/Posix`、`File/Bytes/File_Stream`、`Bash/Scala/Isabelle_System`、动态 `PolyML.compiler/ML_file/use` 以及闭包的实际 IO/环境/进程入口走**同一个** `effective = caller-approved ∩ manifest-declared ∩ current-build-phase` gate；源码/文件 hash、namespace 及注册 callback 只能请求，不能提权。只读固定且校验的 `isabelle-source/` 与实际需要的同版资源，写入仅本次隔离 staging，环境变量按批准 key/用途读取，路径用受限根及 fd 级安全解析防 symlink/TOCTOU，未批准网络、FFI、任意 shell、宿主 HOME 与额外命令默认拒绝；动态编译的闭包继承原权限。普通 ML exception 被 handler 捕获不扩大能力。

环境快照区分三态：批准条目中的字符串（包括空字符串）、批准条目中的显式不存在，以及缺少条目。前两者分别映射 SML `SOME` 与 `NONE`；缺少条目或缺少任一层 key/用途授权仍拒绝并撤权，绝不回退宿主环境。host-config 的 `value` 字段必须存在，`null` 仅表达显式不存在，不能把漏填默认为 `NONE`。native stdout/stderr 经同一有效 lease 和 staging 写权限同步保存有序通道块，不直接写宿主控制台；输出失败不能假报成功。

成功生命周期 `active -> draining -> closed -> succeeded`：draining 只停顶层新任务，已登记根及其受管同根子任务在原有或更小权限下排空；future、回调、stream、进程及 proof obligation 的计数与未决状态在同一同步边界归零，才原子 closed 撤销 VM 能力。publisher 独立于 ML，只能冻结报告与原子发布；发布失败无 registry。失败 `cancelling -> failed` 在构建边界设置不可被 ML handler/interrupt-defer 清除的 epoch，立即撤权并取消受管任务；所有 VM backedge/host 调用检查停止，进程域/流完全等待回收，清理超限为 fatal、不发布而由 supervisor 保持回收责任。runtime handle 失效不撤销已独立成立的 Rust token，但失败 build 不发布其 registry；source hash/报告也不能替代这条屏障。

唯一另获批准的外部程序是固定 `verit-2021.06.2-rmx-1`（SHA256 `b7cb42f384bcabd156ef3176e3706b5cb3479f1769d9be716d339568faa81526`），对应固定 `isabelle-source/src/HOL/List.thy` 的三处调用；`ISABELLE_VERIT` 只是请求，运行前从**同一 sealed executable snapshot**验 hash。`Bash.strings` 只受检还原 argv 并重编码逐字节一致，**绝不运行 shell**：仅六个固定 proof 参数，加 `default` 空、`best` 四项或 `del_insts` 九项（保留次序/重复），可选正毫秒 `--max-time` ≤ 300000，额外 options 禁止。stdin≤64MiB、合并 stdout/stderr≤256MiB，保留 `Cache_IO` startup rc 127 语义并分别处理 solver 0/14/255、timeout/cancel；输出不含 theorem 权限。每次 solver 必须先进入已委托 cgroup v2 域并施加 memory 2GiB/no swap、pids 16、cpu.max=100000/100000，加独立 Bubblewrap user/mount/PID/network/IPC/UTS namespace、只读已校验 executable/interpreter/libs、私有≤64MiB tmpfs、清洁环境/全量 fd 关闭、capabilities drop/no_new_privs、无外部网络或宿主目录；单并发、wall 300s、每进程 CPU 120s。正常退出与 cancel/timeout 均等待域内全部进程/流收敛；缺隔离前置即 `BlockedPrerequisite`，不能降级裸进程。官方 reference 与本机隔离**前置探针**未验证生产 launcher、超限、全量 fd 和 Rust reconstruction；即使 veriT 返回 `unsat`，还必须由原样重建步骤及 Rust kernel replay 才能证明。

上述 solver 是批准的**目标能力合同**，不是已可启动的当前服务：
[最新交付记录](PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19)
仍保留 solver cleanup 前置阻塞；在解除前不得启动新 solver，也不能将
launcher 拒绝路径或官方历史运行当作生产 solver/reconstruction 验收。

### 原生插件与独立兼容验收（2026-10-16 批准）

本机不安装或启动 JVM、Scala、JAR 或官方 Isabelle runtime。Rust 插件采用编译期链接和可信调用方显式注册，不扫描 PATH、不加载动态库、不自动下载。注册表必须先整体校验 identity/version、宿主 API、精确依赖、环、保留名/重复名、服务签名和预算，再成为不可变的 build-local 值；失败不得留下部分注册。发现元数据与实际已注册操作同源，未实现服务不列为可用。

同进程 Rust 插件是受信代码，不是恶意插件沙箱。服务仅经既有宿主 gate 和同 build 子 lease 使用已批准能力，插件声明只能收窄权限；参数和累计请求/响应预算在读入、分配前约束。不得向插件暴露 VM 句柄表、publisher 或可变 logical owner。普通服务 Null/ERROR/Fail/interrupt 经业务结果通道还原 ML 异常；permission、build cancellation 和 fatal 仍走不可恢复的宿主失败通道。保留 `Scala.function*` 源级名称不表示 JAR 二进制兼容。

原生构建与官方兼容采用不同公开结果类型和报告 purpose。原生 `native_build_result` 只有在真实源执行、kernel replay/acceptance、排空及 Closed 屏障后才能原子发布；不消费官方 heap、exit 或 reference 作为证明条件。旧 `native_closure_diagnostics` 的完整差分成功语义不得被新结果覆盖。兼容验收独立执行，缺材料不授予 `Matched`，也不能增加 sampled trusted 计数。

官方材料的 SHA-256、manifest 和结构校验只证明字节自洽，不认证执行来源。可信操作者必须独立批准官方执行方和交付记录，包外批准绑定 producer、固定源码、observer/变换、真实 run、执行/排空收据、源材料及完整 manifest 原字节摘要。导入包和原生报告不能自行指定或生成其来源信任锚。同 fd 普通文件读取须拒绝符号链接、越界、重复 JSON 字段，并有单文件与总量限额；来源、运行记录或六字段覆盖不足均保持 `BlockedPrerequisite`。这些约束是批准的实施合同，不是已通过完整原生或官方验收的证据。

v2 原始 observation frame 恰有六个 TLV 字段；其中 bootstrap load payload
恰有七个字段，包含可为空的 theory、从 1 起的 source order 和
`actual_read_bytes` / `immutable_bootstrap_use` 来源模式。
`src/` 与 `session/` 路径都须绑定批准的实际源摘要；未 sealed 的记录也要
逐帧核对已有 begin/end 身份和 consumed bytes，缺 seal 仍不完整。
bootstrap registration 使用 `observer/event`，其原始 phase 必须是
`original_bootstrap`，并核对 run/load/local identity、源摘要、field 和
typed payload；不接受另造的 `bootstrap/event`。空 ML 文件的实际读取合法，
但仍须匹配空字节的 SHA-256，不能把非空源的缺失字节当作空文件接受。
命名定理按官方 `Thm_Name.make_list` 编号：单成员为 0，多成员为 1..N；
缺成员事件或覆盖不能算完整证据。修改 observer 或 patch 后，旧批准摘要
不再授权新生产者；纯离线合成输入通过不等于新的官方运行验收。

对固定 ROOT 中明确的 JVM 专属服务，用户另批准**仅加载期显式禁用的延迟链接**：
原样 ML 反引可解析准确名称/签名，但禁用项不出现在可用服务表，也不获得宿主
效果或定理权限；真实调用必须明确失败，未知函数仍立即拒绝。实际需要的 XZ
与 Zstd 服务获准增加编译期依赖 `lzma-rust2`（纯 Rust、XZ）和 `zstd`
（静态 C `libzstd`，非 JVM），必须在有界输出、取消和独立依赖审计通过后
才列为可用。此项只授权适配方案，不表示 ROOT 已原样完整执行。

## T1-T4 Criteria

The table summarizes the legacy trust-engineering criteria. Strict-kernel
acceptance is a separate, token-backed boundary described below; the legacy
replay subset is not the coverage of `crates/kernel` owner replay.

| Criterion | Meaning | Current status |
|---|---|---|
| T1 non-forgeable theorem type | `Thm` cannot be built outside the trusted constructor boundary. | Mostly established by private fields and `ThmKernel` routes. |
| T2 reliable kernel rules | Primitive rules enforce side conditions and propagate theorem burdens. | Strict kernel alpha-equivalence split out; checked CTerm certification has started; full `Typ::dummy()` migration remains pending. |
| T3 trust footprint tracking | Unproved acceptance is explicit and propagates through later inference. | Strong project area; `admitted:*`/oracle footprints are explicit. |
| T4 independent replay | A small checker replays proof objects and compares theorem burdens. | Six base Pure rules in the legacy checker; the former HOL migration bridges were removed. |

These four criteria describe legacy trust engineering, not authorization to
promote legacy values. Immutable identity, context-bound acceptance and narrow
source-aware HOL elaboration are implemented strict boundaries; migration of
other callers remains incomplete. The A–H program changes delivery order, not
these trust requirements.

## Strict Kernel Nucleus

`crates/kernel/` implements the isolated `isabelle-kernel` TCB;
`src/kernel/` re-exports its public API. It has not replaced every
`src/core`/Isar/HOL consumer.

The workspace also contains the root product, offline `isabelle-evidence`
data tooling and independent `xtask`; sharing a Cargo workspace does not make
them kernel dependencies or grant them theorem authority.

The new flow is:

```text
RawTerm
  -> immutable Signature / TheorySnapshot / ProofContext
  -> CTerm / CProp
  -> KernelRules
  -> KernelThm
  -> ClosedThm
  -> accept_closed_theorem(owner, name, candidate)
  -> immutable child TrustedTheory + TrustedTheorem
```

The non-TCB flow is:

```text
SearchFact / legacy compat fact / admitted fact
  -> search and diagnostics only
  -> no implicit TrustedTheorem conversion
```

Current strict nucleus constraints:

- no `Typ::dummy` equivalent;
- undeclared constants and local frees are rejected;
- `ProofObligation` is not a theorem;
- theorem fields are private;
- unchecked certification/theorem constructors are `pub(crate)` or narrower
  inside `isabelle-kernel`, not accessible to frontend callers;
- checked primitive rules, authorized basis instances and definition builders
  construct replayable candidate theorem values, not accepted tokens;
- `accept_closed_theorem` is the only `TrustedTheorem` constructor;
- acceptance recursively recertifies and replays the candidate under the exact
  immutable owner, reconstructs dependencies, rejects duplicate names, and
  atomically returns the child theory plus accepted token;
- accepted theorem references require the exact ancestor token (`id`, `name`,
  and `accepted_in`) before replay records its logical `TheoremId` dependency;
- replay-derived dependency sets are canonical theorem-identity data, not a
  substitute for token authority;
- the standalone HOL fixture and sampled `HOL::TrueI` source projection use
  an installed `refl` basis and conservative `True_def`; broad HOL
  declarations and proof methods remain outside this checked path;
- axiom authorization is exact `AxiomDependencyId(basis_id, schema_id)`, not "some basis exists" (2026-07-21);
- `SearchFactDb` cannot promote facts to trusted theorems.

Current strict nucleus implementation includes the base primitive rule set,
`generalize`, `instantiate`, explicit `export_scope`/transfer/index
transformations, partial class/sort handling and checked bound-proof candidate
composition. Current `resolve1_match` uses one-way matching and rejects
namespace collisions with `RequiresLifting`; the earlier thin `bicompose`
alias is no longer exported. `subst_premise` rewrites a selected propositional
equality premise in fixed lhs-to-rhs direction, not arbitrary object equality.
The later `bicompose_candidate`/`lift_rule`/assumption interfaces check constrained
Rust candidates, not full Isabelle/ML unification, lazy `Seq`, or `Thm: THM`.
`bicompose_candidate(owner, context, options, rule, state, candidate)` takes
`CompositionOptions` with flags, elimination mode, premise count and a 1-based
subgoal index. This input bundle has no proof authority and does not bypass
source replay or residual-burden checks. Evidence-side `ObserverHostInputs`
likewise bundles inputs; the host validation and evidence checks still apply.
Exact supported operations and deficits are recorded in the
[THM inventory](NATIVE_THM_INTERFACE_INVENTORY.md); neither family
licenses new unreviewed trusted proof rules.

## Theorem Status Semantics

The following predicates belong to legacy `src/core::Thm`; they are not
the strict kernel's acceptance API:

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hypotheses + no unresolved tpairs
is_strict_closed_proved() == strict construction + is_closed_proved() + no dummy types
check_kernel_invariants(Strict) == strict construction + structural invariants + supported replay burden check
```

These predicates are deliberately not interchangeable:

```text
check_kernel_invariants(Strict)
  => the theorem is internally consistent as a strict theorem
  != the theorem is a closed lemma

is_strict_closed_proved()
  => the legacy theorem is eligible for TransitionalStrictClosed statistics
  != the theorem is eligible for new-kernel TrustedTheory acceptance
  != proof replay has necessarily covered every primitive rule used

check_proof() / validate_proof()
  => independent derivation replay for the currently supported rule subset
  != a complete Isabelle proofterm checker
```

For example, strict `assume(A)` may pass strict invariants and replay as a valid
open theorem `A |- A`, but it must not satisfy `is_strict_closed_proved()`.
Conversely, a strict theorem whose derivation contains a currently unsupported
rule may pass structural strict invariants but still fail `check_proof()` until
that replay rule is implemented.

Use these terms:

| Status | Meaning | Counts as trusted proved lemma? |
|---|---|---|
| Transitional strict closed theorem | legacy `core::Thm + ThmTrust::Strict`, closed-shaped, oracle-free, no dummy types | No; migration/reporting only |
| Kernel-trusted closed theorem | `isabelle_kernel::TrustedTheorem`, sealed by exact-owner acceptance with a `CProp : prop` conclusion and authorized dependencies | Yes |
| Compat closed-shaped theorem | no oracle/hyps/`tpairs`, but constructed through legacy compatibility paths | No |
| Oracle-free open theorem | `A1, ..., An |- P`, no oracle footprint | No |
| Admitted theorem | legacy proposition retained with `admitted:*` oracle footprint | No |
| Searchable fact | fact available to proof search; may be open/admitted/generated/compat/transitional | No |

`ThmKernel::assume(A)` constructs:

```text
A |- A
```

It does not construct:

```text
|- A
```

Therefore `assume(A)` may be `is_fully_proved()` but must not be
`is_closed_proved()`.

## Admit / Oracle Footprints

Legacy `ThmKernel::admit(cterm, reason)` retains an explicitly unproved
proposition for search/diagnostics. The isolated strict kernel has no `admit`;
this is never the accepted-token constructor.

Recommended reason names:

```text
admitted:proof_engine_failed
admitted:parser_gap
admitted:unsupported_method
admitted:attribute_transformation
admitted:datatype_stub
admitted:class_stub
admitted:metis_fallback
admitted:simp_fallback
admitted:sledgehammer_stub
admitted:strict_adapter_source_prop_unverified
admitted:strict_adapter_prop_mismatch
admitted:strict_adapter_proof_shape_mismatch
admitted:strict_adapter_missing_checked_definition
admitted:strict_adapter_certification_failed
admitted:strict_adapter_replay_failed
admitted:strict_adapter_kernel_invariant
```

Rules:

- Only explicit legacy search/reporting fallback may use `admit`; complete
  source loading and interactive proof completion return errors instead.
- A transitional adapter shape hit that fails checks reports a specific
  `admitted:strict_adapter_*` reason rather than silently trying legacy proof.
- The registered explicit-proof `TrueI` adapter must require both
  `SourcePropositionStatus::FullyConsumed` and
  `SourcePropositionShape::StandaloneHolTrueAlias`. Any other status or shape
  is rejected as
  `admitted:strict_adapter_source_prop_unverified`, not reclassified as
  `admitted:parser_gap` and not sent to legacy proof fallback.
- Unsupported complete-source features must fail; experimental generated
  search facts retain explicit admission and cannot become accepted tokens.
- Attribute transformations that do not have a real kernel derivation must use
  `admitted:attribute_transformation`.
- Oracle footprints must union through multi-premise rules and be preserved
  through single-premise rules.

## Closed Theorem Reporting And Acceptance

The current legacy batch increments its transitional verified count only if
`thm.is_strict_closed_proved()`; the exact implementation is in
[`src/isar/method.rs`](../../src/isar/method.rs).

`is_closed_proved()` remains a useful closed-shape predicate:

```text
thm.oracles().is_empty()
&& thm.hyps().is_empty()
&& thm.tpairs().is_empty()
```

It is not sufficient even for the transitional count because a compatibility
theorem can have that shape. The legacy strict filter additionally requires:

```text
thm.trust_status() == ThmTrust::Strict
&& !thm.contains_dummy_type()
```

For audit gates, use
`thm.check_kernel_invariants(KernelCheckMode::Strict)` from the legacy theorem
API rather than copying a detached Rust snippet.

`is_strict_closed_proved()` is the cheap legacy table/statistics predicate.
`check_kernel_invariants(Strict)` is stronger: it rejects compat/admitted
provenance, residual dummy types, malformed proposition CTerms, `maxidx` drift,
oracle-tainted strict theorems, and burden mismatches for the currently
replay-supported derivation subset.

It is not a closed-lemma predicate. Open strict theorems are legal theorem
values. New-kernel acceptance separately requires a `ClosedThm` over
`CProp : prop`; only successful owner-parameterized replay can seal the
`TrustedTheorem` later classified as `KernelTrustedClosed`.

Current architecture:

```text
HolTheoremDb / theorem_index
  = proof-search fact indexes
  = may contain open/admitted facts

HolTheoremDb.checked_definitions
  = checked definition sources
  = not theorem facts
  = not proof progress

legacy Theory theorem table
  = transitional/export compatibility table
  = currently filters with is_strict_closed_proved()

new-kernel TrustedTheory
  = immutable, ancestry-sensitive owner and accepted-fact chain
  = accepts only through context-bound replay and dependency validation
  = rejects duplicate theorem names without overwriting
  = returns a non-forgeable TrustedTheorem token
  = reported as KernelTrustedClosed
```

`SessionBuilder::BuildResult::theorems` counts completed transitional legacy
results only; it does not contain new-kernel tokens. The five-file sampled
verifier records accepted tokens separately. `ProofOutcome::KernelTrustedClosed`
owns a real accepted token and is exclusive of every legacy outcome; the last
recorded bundled sample counted `1/125` for the source-backed `HOL::TrueI`
projection. Later external Rust consumers do not enter that sampler.

## T2 Kernel Status

Implemented hardening includes:

- known concrete type mismatch checks in several kernel paths;
- `instantiate_checked` production path;
- legacy infallible instantiation removed from production use;
- strict kernel alpha-equivalence separated from compatibility matching;
- `CTerm::certify_checked(term, type_env)` rejects undeclared constants,
  ill-typed applications, unbound de Bruijn indices, and residual
  `Typ::dummy()`;
- `CTerm` records whether it came from checked or compatibility certification;
- strict `ThmKernel::assume` and `ThmKernel::reflexive` reject compatibility
  CTerms, while old behavior is explicitly named `assume_compat` /
  `reflexive_compat`;
- `ProofState::assume`, `Goal::init`, and checked proof-state goal/subgoal
  constructors now create Strict open theorem obligations through checked
  certification instead of defaulting to compatibility theorem construction;
- proof-state checked certification now goes through an explicit
  `ProofCertContext` / `TypeEnv` source. Constants and local frees must already
  be declared in that context; raw terms are no longer allowed to self-declare
  their own Const/Free types into a temporary trusted environment;
- `Thm` records `ThmTrust::{Strict, Compat, Admitted}` so compatibility
  theorems cannot be counted as trusted even if they are oracle-free and closed;
- legacy tables, `SessionBuilder`, and `HolTheoremDb::closed_proved_count`
  currently use `is_strict_closed_proved()` for transitional filtering; this is
  not the implemented strict `TrustedTheory` authorization gate;
- the strict kernel derives deterministic, domain-separated `SignatureId` and
  ancestry-sensitive `TheoryId` values from canonical validated data;
- `ProofContext`, `CTerm`, `CProp`, `KernelThm`, and `TrustedTheorem` retain the
  exact context stamp, and every current multi-input rule rejects mismatch
  before logical matching;
- strict signature/theory extension is immutable, duplicate declarations fail,
  and untrusted signature snapshots must match a recomputed digest;
- `TrustedTheory` is an immutable owner/fact ancestry; public table mutation and
  table-agnostic `ClosedThm::trust` are removed;
- `accept_closed_theorem` revalidates every checked theorem/derivation payload,
  replays every current Pure derivation under the exact owner, reconstructs
  theorem-reference dependencies, and seals one canonical `TrustedTheorem`;
- theorem identity uses a versioned fixed-width canonical encoding, omits proof
  structure and binder display names, and includes exact context, proposition
  constructors/types, and sorted dependency kinds;
- equal theorem content accepted under different fact names may share a logical
  `TheoremId`, but the sealed tokens have different `accepted_in` values and
  are not interchangeable across sibling branches; dependent theorem IDs also
  commit to the exact branch `ContextStamp`;
- `ProofOutcome::KernelTrustedClosed` is token-backed and mutually exclusive;
  the sampled `HOL::TrueI` source projection produces one token, whereas the
  standalone HOL and Pure fixtures are not added to the sample;
- `HolTheoremDb::checked_definitions` holds untrusted definition inputs,
  starting with `True_def`, apart from searchable facts and trusted theorem
  tables; accepted `True_def` is rebuilt from the audited source RHS by
  generic `define_const`, not promoted from this legacy table;
- `try_strict_adapter` registers only the sampled `HOL::TrueI` candidate.
  It requires a complete explicit proof and `FullyConsumed +
  StandaloneHolTrueAlias` source provenance, a parser-sealed full source and
  exact parent command byte offset, and a checked legacy payload that may
  reject but never grant theorem authority. The audited projection checks
  required declaration names, shapes, ordering, scope, syntax bindings,
  actual definition RHS and complete lemma proof. It produces a new-kernel
  owner plus token via `refl`, generic conservative definition, Pure
  transport and exact-owner replay; no legacy `Thm` is upgraded.
  Unsupported or mismatched candidates become explicit admitted diagnostic
  reasons, not accepted facts. Missing and empty proof scripts remain
  `NotApplicable`, retaining legacy parser-gap behavior.
- `Thm::check_kernel_invariants(KernelCheckMode::{Compat, Strict})` separates
  legacy structural checks from strict trusted-kernel invariant checks;
- `tpairs`, `shyps`, and `oracles` propagation audits;
- `beta_conversion` uses real bound substitution;
- `abstraction` and `forall_intr` capture typed Free variables as correctly
  scoped Bound indices and check free-variable side conditions;
- attribute transformation fallback is admitted, not assumed;
- complete theory loading rejects `accept_all` and `sorry`; explicitly admitted
  search/reporting paths remain legacy diagnostics, never accepted tokens.

Known debts:

| Debt | Why it matters | Direction |
|---|---|---|
| Compatibility Free/Const suffix matching | `compat_alpha_eq` still exists for parser/loader legacy paths. | Keep it out of trusted rules; fix parser/loader/type annotations and remove the compat need. |
| Compatibility Var/Free matching | `compat_alpha_eq` still exists for schematic-variable parser gaps. | Keep it out of trusted rules; align theorem DB and parser variable representation. |
| Transitional source-shape guard | The search loader can retain an explicitly incomplete prefix, and local context may shadow a surface name. Status/shape metadata is not name resolution or certification. | Require `FullyConsumed + StandaloneHolTrueAlias` for the narrow adapter; only checked source elaboration can replace this guard. |
| `Typ::dummy()` tolerance | Lets ill-typed terms survive too far. | Migrate trusted paths to `CTerm::certify_checked` and checked kernel entry points. |
| Best-effort `CTerm::certify` | Still widely used by parser/HOL/Isar compatibility paths. | Keep it compatibility-only; explicit `_compat` theorem constructors are migration debt, not TCB. |
| `Option<Thm>` proof-search APIs | Can hide `KernelError` diagnostics. | Move trusted paths toward `Result<Option<Thm>, KernelError>`. |

The broader checked HOL proposition contract and its narrow implemented slice
are specified in [CHECKED_HOL_PROPOSITION_NORMALIZATION.md](../design/CHECKED_HOL_PROPOSITION_NORMALIZATION.md).
The proposed target separation between the Pure kernel, a trusted HOL
object-logic extension, Isar adapters, and legacy core is recorded in
[ADR-0003-hol-logic-trusted-extension.md](../adr/ADR-0003-hol-logic-trusted-extension.md).
The last recorded bundled five-file sampler reports
`TransitionalStrictClosed: 0/125` and `KernelTrustedClosed: 1/125` for its audited
`HOL::TrueI` source projection; it has not been rerun for the subsequent Rust
consumer work. The 2026-10-03 pre-cutover sample reported `1/125`
transitional and `0/125` kernel-trusted; that is historical. Separately,
`isabelle-build` accepts a HOL `TrueI` fixture and a Pure identity fixture as
new-kernel `TrustedTheorem` tokens; neither is counted in the sampler.
The Pure proof is `!!P::prop. PROP P ==> PROP P` with `by assumption`,
replayed via `assume`, `implies_intr`, and `forall_intr` with a proof-local
typed Free. The sampled HOL projection checks only dependencies necessary
for `TrueI`; unrelated commands and ML are not executed and cannot supply
owner authority. The minimal `refl` basis of this sampled path is
structurally validated, not independently checked against upstream
Isabelle/HOL; the sample does not install `HOL.subst`. That does not undo
its separate approval as one of the 13 `HOLBasisV1` slots above. No general
HOL/Isar compilation follows from this milestone.

The source proposition AST itself remains data only. It retains raw
`SourceName` / `SourceSyntax` spellings and file-byte spans; `SourceId`
and spans are caller-supplied diagnostic metadata, never proof authority.
The strict source parser/elaborator consumes it for a narrow subset, not
for every Isabelle/Pure expression.

Trusted kernel rules use `Hyps::kernel_alpha_eq`. The old broad matching is
isolated as `Hyps::compat_alpha_eq` and must remain explicitly marked as
compatibility-only until front-end representation gaps are fixed.

### 声明与 legacy 结果的拒绝边界

strict 类型认证要求所有 constructor 已声明且 arity 正确；目前
`SignatureId` 使用 v4 域，包含已受检的 type、class/arity 和常量声明
（实际编码见 [`identity.rs`](../../crates/kernel/src/identity.rs)）。
schema 模式用于 basis 安装前检查；公开多态常量
scheme 的实例化要求 concrete 类型，普通常量按声明类型精确匹配，允许其中
含合法类型变量。judgment 声明另要求 concrete 类型。定义入口与 owner replay
共享闭合、单态和父声明验证；后代不能为祖先补装 basis，引用必须匹配规范
accepted token 的负载。

完整 legacy 文件只有在 header/import、词法、声明、证明及最终 `end` 全部成功
后才发布。单文件失败丢弃暂存成果；session 每轮清空旧 registry，失败父项
不能被上次成功结果替代。多个可用 import 按声明与父身份无冲突合并；缺失、
失败或合并冲突的任一父项均阻断子项，不回退到其他父项。未实现命令仍明确
拒绝；这些 legacy 合并不授予 kernel accepted 权力。

legacy 结案门要求真实 Strict/checked 结果、完整命题匹配、已许可假设和合法
作用域导出；逻辑目标本身含 implication 不代表存在未解义务。源方法无隐式
Auto fallback。rewrites 需完整端点证书，ATP replay 需逐步消费证据并验证最终
完整目标。Compat/Admitted 结果不能因重写、搜索或结案获得 Strict 或 kernel
accepted 权威。

## Legacy T4 Proofterm Replay Status

Supported independent replay rules in `src/core/proofterm.rs`:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

Current legacy replay behavior:

- `Thm::check_proof()` reconstructs theorem shape from stored proof data and
  compares `prop`, `hyps`, `tpairs`, and `oracles`.
- `Thm::validate_proof()` uses the same burden-aware validation semantics.
- `ProofBody::check(expected_prop)` is proposition-only compatibility code and
  is not a trusted theorem validation gate.
- Admitted/oracle-backed theorems fail independent replay.
- Unsupported replay rules fail explicitly.
- Open theorem replay can succeed, but open theorems still do not count as
  closed proved lemmas.
- `check_kernel_invariants(Strict)` only invokes replay when the stored
  derivation is in the currently supported replay subset. Unsupported strict
  derivations are structurally audited but are not replay-checked.

The former `hol_object_refl` and `true_def_transport` bridges were removed
during the source-backed cutover. This six-rule legacy checker is neither
the isolated strict kernel's exact-owner acceptance checker nor full Isabelle
`proofterm.ML` or `Proof_Checker.thm_of_proof`.

Deferred replay backlog:

```text
beta_conversion / forall_intr / forall_elim
combination / abstraction / equal_intr / equal_elim
instantiate_checked / generalize
legacy resolution-family coverage
```

This legacy backlog is separate from strict-kernel acceptance, which replays
every current strict `Derivation`, including installed axiom and conservative
definition evidence. Resume legacy replay only for a focused soundness fix;
other theorem-producing callers still require individual source, owner, and
replay contracts after the one-token sampled milestone.

## Verification Commands

Use `cargo +stable xtask strict` for the trusted boundary and `core` for the
bundled 125-candidate regression. `tier2`/`tier3`/`profile` are opt-in supervised
diagnostics, not proof gates. Full workspace regression is
`cargo +stable xtask test`; bare Cargo defaults to the root product.

Follow the [engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow):
behavior proof, applicable project gates, then the complete global
`~/.omp/agent/validate.sh`. `verify` and CI use strict workspace all-targets
Clippy; neither that matrix nor `release-check` replaces the independent
security/global gates. `all` remains an explicit diagnostic aggregate.

The [historical A-package record](PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
contains a completed workspace run with an official HOL-source compatibility
failure; global strict Clippy also failed. This is not the current all-Rust
automation migration's validation result. The
[current record](PROJECT_STATUS.md#current-delivery-state) separates automation,
integrated quality repairs and observed gate outcomes. Earlier failures and
OOM/timeout records are historical. Scope, scan exceptions, toolchains and
observed outcomes are evidence, not permanent green guarantees. P2/P3/P4
implementation has resumed, but complete native compatibility remains unaccepted
even when narrow consumer checks or quality repairs pass.

## Reporting Rules

When reporting project status:

- Label `is_strict_closed_proved()`-derived counts as
  `TransitionalStrictClosed`, not kernel-trusted verified lemmas.
- Report `KernelTrustedClosed` only from sealed
  `isabelle_kernel::TrustedTheorem` evidence (root re-export:
  `isabelle_rs::kernel`); the bundled five-file sample is `1/125`.
- State admitted counts separately.
- State open theorem facts separately when relevant.
- Do not equate searchable facts with trusted theorem-table entries.
- Do not market the project as a full Isabelle rewrite.
- Keep A–H target capability, source-backed sampled acceptance, diagnostic
  completion and full-project quality status separate. Official reference
  results are not Rust theorem authority.
- The [Isabelle2025 reference snapshot](../../tests/fixtures/isabelle2025/closure.json)
  records official observations, not accepted Rust facts, execution permission
  or an axiom allowlist. Its 18,895 named static records include 16,490 with
  sort hypotheses; absent term hypotheses/oracles do not erase those burdens.
- Official axiom-table membership does not identify logical authority:
  definition-associated entries, conditional typedef extensions, class/arity
  evidence and Pure primitive mirrors require their own checked Rust mapping.
- The fixed `veriT` production capability has separate, restricted
  [scope approval](PROJECT_STATUS.md#isabelle2025-reference-observations-2026-10-12),
  not implementation acceptance. Rust proof reconstruction is still required.
  Neither an external solver's `unsat` nor a reference build's exit code can
  construct or authorize a trusted token.
