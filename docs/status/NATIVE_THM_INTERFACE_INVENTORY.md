# Fixed THM interface inventory (Rust mapping updated 2026-10-19)

固定源码 `isabelle-source/src/Pure/thm.ML:12-200`，BASIC_THM 8 项 + THM 自有 163 项 = 171 项（4 type、3 exception、164 val）；include 不重复计数。以下逐项签名仅规范空白并去掉注释。

K = 内核认证/规则/受检投影；D = 非可信派生算法、matcher 或数据投影；M = ML 不透明表示/异常/可观察效果。状态只描述 Rust 对应能力，所有条目均未声称通过完整 Isabelle/ML 兼容验收。路径缩写 `*.rs` 对应 `crates/kernel/src/` 或其 `tests/` 中同名文件；bound_proof 路径已显式标明。

外部 Rust [`native_thm`](../../crates/kernel/examples/native_thm.rs) 和
[`native_thm_variables`](../../crates/kernel/examples/native_thm_variables.rs)
的局部执行闭环分别见
[2026-10-18](PROJECT_STATUS.md#first-native-rust-thm-closure-2026-10-18) 和
[2026-10-19](PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19)
交付记录。它们只消费 `isabelle-kernel` 公共受检 API；`src/ml/host/context.rs`
的局部 Context 实现和 bootstrap 前缀不等于完整 `structure Thm: THM`
或 ROOT/HOL 九根验收。下表签名仍为固定官方清单，状态不随日期自动升级。

表中“Rust 窄项已实现”只指所列内核 API 或 consumer 的能力，不表示 ML
签名接线、generative opaque type、异常身份、callback 或完整源码执行已验收。

|#|官方声明|归属|Rust 内核/consumer 映射状态|当前对应与测试证据|
|---:|---|---|---|---|
|1|`type ctyp`|M|部分|`CType` / `CTerm` / `KernelThm, OpenThm, ClosedThm, TrustedTheorem`（`cterm.rs, thm.rs, theory.rs`）；认证/关闭/接受测试见下列规则行。未实现 ML opaque type/句柄生命周期。|
|2|`type cterm`|M|部分|`CType` / `CTerm` / `KernelThm, OpenThm, ClosedThm, TrustedTheorem`（`cterm.rs, thm.rs, theory.rs`）；认证/关闭/接受测试见下列规则行。未实现 ML opaque type/句柄生命周期。|
|3|`exception CTERM of string * cterm list`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|4|`type thm`|M|部分|`CType` / `CTerm` / `KernelThm, OpenThm, ClosedThm, TrustedTheorem`（`cterm.rs, thm.rs, theory.rs`）；认证/关闭/接受测试见下列规则行。未实现 ML opaque type/句柄生命周期。|
|5|`type conv = cterm -> thm`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|6|`exception THM of string * int * thm list`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|7|`val RSN: thm * (int * thm) -> thm`|D+M|缺失|无官方搜索/Seq adapter 和契约测试；RSN 至多消费两个结果、重复 pull 等语义未验收。|
|8|`val RS: thm * thm -> thm`|D+M|缺失|无官方搜索/Seq adapter 和契约测试；RSN 至多消费两个结果、重复 pull 等语义未验收。|
|9|`val typ_of: ctyp -> typ`|K|Rust 窄项已实现|`CType::ty`（`cterm.rs`）；无独立投影契约测试，不能推断 ML 兼容。|
|10|`val global_ctyp_of: theory -> typ -> ctyp`|K|部分|`ProofContext::new(owner.snapshot().clone())` + `certify_type`（`context.rs`）；显式 owner；无完整 ML 认证测试。|
|11|`val ctyp_of: Proof.context -> typ -> ctyp`|K|部分|`ProofContext::new(owner.snapshot().clone())` + `certify_type`（`context.rs`）；显式 owner；无完整 ML 认证测试。|
|12|`val dest_ctyp: ctyp -> ctyp list`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|13|`val dest_ctypN: int -> ctyp -> ctyp`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|14|`val make_ctyp: ctyp -> ctyp list -> ctyp`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|15|`val maxidx_of_ctyp: ctyp -> int`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|16|`val term_of: cterm -> term`|K|Rust 窄项已实现|`CTerm::term/ty`（`cterm.rs`）；`theorem_instantiation.rs::instantiate_replacement_type_mismatch_rejects` 经规则使用认证结果。|
|17|`val typ_of_cterm: cterm -> typ`|K|Rust 窄项已实现|`CTerm::term/ty`（`cterm.rs`）；`theorem_instantiation.rs::instantiate_replacement_type_mismatch_rejects` 经规则使用认证结果。|
|18|`val ctyp_of_cterm: cterm -> ctyp`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|19|`val maxidx_of_cterm: cterm -> int`|K|部分|`CTerm::max_var_index` 为 crate-private；无外部同义 API/完整 ML 测试。|
|20|`val global_cterm_of: theory -> term -> cterm`|K|部分|`ProofContext::certify_term`（`context.rs`）；`fixed_type_scope.rs::certify_polymorphic_constant_requires_local_type_scope`。|
|21|`val cterm_of: Proof.context -> term -> cterm`|K|部分|`ProofContext::certify_term`（`context.rs`）；`fixed_type_scope.rs::certify_polymorphic_constant_requires_local_type_scope`。|
|22|`val renamed_term: term -> cterm -> cterm`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|23|`val fast_term_ord: cterm ord`|D|缺失|无官方排序/fold/回调次序契约实现或测试。|
|24|`val term_ord: cterm ord`|D|缺失|无官方排序/fold/回调次序契约实现或测试。|
|25|`val dest_comb: cterm -> cterm * cterm`|K|部分|`Term::dest_app/dest_abs` 只投影裸 Term；没有同义 certified-result API、新鲜命名效果或契约测试。|
|26|`val dest_fun: cterm -> cterm`|K|部分|`Term::dest_app/dest_abs` 只投影裸 Term；没有同义 certified-result API、新鲜命名效果或契约测试。|
|27|`val dest_arg: cterm -> cterm`|K|部分|`Term::dest_app/dest_abs` 只投影裸 Term；没有同义 certified-result API、新鲜命名效果或契约测试。|
|28|`val dest_fun2: cterm -> cterm`|K|部分|`Term::dest_app/dest_abs` 只投影裸 Term；没有同义 certified-result API、新鲜命名效果或契约测试。|
|29|`val dest_arg1: cterm -> cterm`|K|部分|`Term::dest_app/dest_abs` 只投影裸 Term；没有同义 certified-result API、新鲜命名效果或契约测试。|
|30|`val dest_abs_fresh: string -> cterm -> cterm * cterm`|K|部分|`Term::dest_app/dest_abs` 只投影裸 Term；没有同义 certified-result API、新鲜命名效果或契约测试。|
|31|`val dest_abs_global: cterm -> cterm * cterm`|K|部分|`Term::dest_app/dest_abs` 只投影裸 Term；没有同义 certified-result API、新鲜命名效果或契约测试。|
|32|`val rename_tvar: indexname -> ctyp -> ctyp`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|33|`val free: string * ctyp -> cterm`|K|部分|`RawTerm::free/var/app/abs` 后显式 `ProofContext::certify_term`；`fixed_type_scope.rs`、`theorem_instantiation.rs`。raw 构造不认证，lambda 不是已实现的 cterm binder adapter。|
|34|`val var: indexname * ctyp -> cterm`|K|部分|`RawTerm::free/var/app/abs` 后显式 `ProofContext::certify_term`；`fixed_type_scope.rs`、`theorem_instantiation.rs`。raw 构造不认证，lambda 不是已实现的 cterm binder adapter。|
|35|`val apply: cterm -> cterm -> cterm`|K|部分|`RawTerm::free/var/app/abs` 后显式 `ProofContext::certify_term`；`fixed_type_scope.rs`、`theorem_instantiation.rs`。raw 构造不认证，lambda 不是已实现的 cterm binder adapter。|
|36|`val lambda_name: string * cterm -> cterm -> cterm`|K|部分|`RawTerm::free/var/app/abs` 后显式 `ProofContext::certify_term`；`fixed_type_scope.rs`、`theorem_instantiation.rs`。raw 构造不认证，lambda 不是已实现的 cterm binder adapter。|
|37|`val lambda: cterm -> cterm -> cterm`|K|部分|`RawTerm::free/var/app/abs` 后显式 `ProofContext::certify_term`；`fixed_type_scope.rs`、`theorem_instantiation.rs`。raw 构造不认证，lambda 不是已实现的 cterm binder adapter。|
|38|`val adjust_maxidx_cterm: int -> cterm -> cterm`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|39|`val incr_indexes_cterm: int -> cterm -> cterm`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|40|`val match: cterm * cterm -> ctyp TVars.table * cterm Vars.table`|D|部分|`KernelRules::match_terms_certified`（`rules.rs`）为受限一阶候选；`match_terms_certified_repeated_var_inconsistent`、`match_terms_certified_rejects_bound`；无完整高阶 matcher/ML 表接口。|
|41|`val first_order_match: cterm * cterm -> ctyp TVars.table * cterm Vars.table`|D|部分|`KernelRules::match_terms_certified`（`rules.rs`）为受限一阶候选；`match_terms_certified_repeated_var_inconsistent`、`match_terms_certified_rejects_bound`；无完整高阶 matcher/ML 表接口。|
|42|`val fold_terms: {hyps: bool} -> (term -> 'a -> 'a) -> thm -> 'a -> 'a`|D|缺失|无官方排序/fold/回调次序契约实现或测试。|
|43|`val fold_atomic_ctyps: {hyps: bool} -> ('a -> typ -> bool) -> (ctyp -> 'a -> 'a) -> thm -> 'a -> 'a`|D|缺失|无官方排序/fold/回调次序契约实现或测试。|
|44|`val fold_atomic_cterms: {hyps: bool} -> ('a -> term -> bool) -> (cterm -> 'a -> 'a) -> thm -> 'a -> 'a`|D|缺失|无官方排序/fold/回调次序契约实现或测试。|
|45|`val terms_of_tpairs: (term * term) list -> term list`|D|缺失|无官方排序/fold/回调次序契约实现或测试。|
|46|`val full_prop_of: thm -> term`|D|部分|`KernelThm::prop` 与私有 `ProofPayload::flex_pairs` 分存；`pure_composition.rs::bicompose_candidate_unsolved_flex_never_closes`。无完整官方 full/plain projection adapter。|
|47|`val theory_id: thm -> Context.theory_id`|M|部分|`CTerm::context`、`KernelThm::context/proved_in`、`TrustedTheory::find_ancestor_by_id`；`thm.rs::transfer_committed_ancestor_replays_in_target_owner`；不是 ML theory object/identity。|
|48|`val theory_name: {long: bool} -> thm -> string`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|49|`val theory_long_name: thm -> string`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|50|`val theory_base_name: thm -> string`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|51|`val maxidx_of: thm -> int`|K|部分|`KernelThm::max_var_index`、`KernelRules::adjust_max_index`；`thm.rs::max_index_instantiation_retains_then_adjusts_checked_upper_bound`；Option/usize 不是 ML int 全域契约。|
|52|`val maxidx_thm: thm -> int -> int`|K|部分|`KernelThm::max_var_index`、`KernelRules::adjust_max_index`；`thm.rs::max_index_instantiation_retains_then_adjusts_checked_upper_bound`；Option/usize 不是 ML int 全域契约。|
|53|`val shyps_of: thm -> sort Ord_List.T`|K|部分|`KernelThm::shyps` 与私有 payload 校验；`theorem_obligations.rs::theorem_erased_empty_sort_preserves_extra_sort_hypothesis`；无完整 extra_shyps ML 投影。|
|54|`val hyps_of: thm -> term list`|K|部分|`KernelThm::hyps/prop` 返回 CProp；`theorem_instantiation.rs::instantiate_real_hypothesis_is_preserved_exactly`；ML 返回类型/异常尚无 adapter。|
|55|`val prop_of: thm -> term`|K|部分|`KernelThm::hyps/prop` 返回 CProp；`theorem_instantiation.rs::instantiate_real_hypothesis_is_preserved_exactly`；ML 返回类型/异常尚无 adapter。|
|56|`val tpairs_of: thm -> (term * term) list`|D|部分|`KernelThm::prop` 与私有 `ProofPayload::flex_pairs` 分存；`pure_composition.rs::bicompose_candidate_unsolved_flex_never_closes`。无完整官方 full/plain projection adapter。|
|57|`val concl_of: thm -> term`|D|部分|`Term::dest_imp_chain/nprems/select_subgoal`；`rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise`；无完整官方索引/异常 adapter。|
|58|`val prems_of: thm -> term list`|D|部分|`Term::dest_imp_chain/nprems/select_subgoal`；`rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise`；无完整官方索引/异常 adapter。|
|59|`val take_prems_of: int -> thm -> term list`|D|部分|`Term::dest_imp_chain/nprems/select_subgoal`；`rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise`；无完整官方索引/异常 adapter。|
|60|`val nprems_of: thm -> int`|D|部分|`Term::dest_imp_chain/nprems/select_subgoal`；`rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise`；无完整官方索引/异常 adapter。|
|61|`val no_prems: thm -> bool`|D|部分|`Term::dest_imp_chain/nprems/select_subgoal`；`rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise`；无完整官方索引/异常 adapter。|
|62|`val prem_of: thm -> int -> term`|D|部分|`Term::dest_imp_chain/nprems/select_subgoal`；`rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise`；无完整官方索引/异常 adapter。|
|63|`val major_prem_of: thm -> term`|D|部分|`Term::dest_imp_chain/nprems/select_subgoal`；`rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise`；无完整官方索引/异常 adapter。|
|64|`val cprop_of: thm -> cterm`|K|部分|`KernelThm::hyps/prop` 返回 CProp；`theorem_instantiation.rs::instantiate_real_hypothesis_is_preserved_exactly`；ML 返回类型/异常尚无 adapter。|
|65|`val cprem_of: thm -> int -> cterm`|K|缺失|无同义 certified-result 投影 API/契约测试；Term 投影本身无认证权限。|
|66|`val cconcl_of: thm -> cterm`|K|缺失|无同义 certified-result 投影 API/契约测试；Term 投影本身无认证权限。|
|67|`val cprems_of: thm -> cterm list`|K|缺失|无同义 certified-result 投影 API/契约测试；Term 投影本身无认证权限。|
|68|`val take_cprems_of: int -> thm -> cterm list`|K|缺失|无同义 certified-result 投影 API/契约测试；Term 投影本身无认证权限。|
|69|`val chyps_of: thm -> cterm list`|K|部分|`KernelThm::hyps/prop` 返回 CProp；`theorem_instantiation.rs::instantiate_real_hypothesis_is_preserved_exactly`；ML 返回类型/异常尚无 adapter。|
|70|`val thm_ord: thm ord`|D|缺失|无官方排序/fold/回调次序契约实现或测试。|
|71|`exception CONTEXT of string * ctyp list * cterm list * thm list * Context.generic option`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|72|`val theory_of_cterm: cterm -> theory`|M|部分|`CTerm::context`、`KernelThm::context/proved_in`、`TrustedTheory::find_ancestor_by_id`；`thm.rs::transfer_committed_ancestor_replays_in_target_owner`；不是 ML theory object/identity。|
|73|`val theory_of_thm: thm -> theory`|M|部分|`CTerm::context`、`KernelThm::context/proved_in`、`TrustedTheory::find_ancestor_by_id`；`thm.rs::transfer_committed_ancestor_replays_in_target_owner`；不是 ML theory object/identity。|
|74|`val trim_context_ctyp: ctyp -> ctyp`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|75|`val trim_context_cterm: cterm -> cterm`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|76|`val transfer_ctyp: theory -> ctyp -> ctyp`|K|部分|目标 context 可重新 certify；无专用 ancestry-preserving ctyp/cterm transfer 或 ML generic-context 契约测试。|
|77|`val transfer_ctyp': Proof.context -> ctyp -> ctyp`|K|部分|目标 context 可重新 certify；无专用 ancestry-preserving ctyp/cterm transfer 或 ML generic-context 契约测试。|
|78|`val transfer_ctyp'': Context.generic -> ctyp -> ctyp`|K|部分|目标 context 可重新 certify；无专用 ancestry-preserving ctyp/cterm transfer 或 ML generic-context 契约测试。|
|79|`val transfer_cterm: theory -> cterm -> cterm`|K|部分|目标 context 可重新 certify；无专用 ancestry-preserving ctyp/cterm transfer 或 ML generic-context 契约测试。|
|80|`val transfer_cterm': Proof.context -> cterm -> cterm`|K|部分|目标 context 可重新 certify；无专用 ancestry-preserving ctyp/cterm transfer 或 ML generic-context 契约测试。|
|81|`val transfer_cterm'': Context.generic -> cterm -> cterm`|K|部分|目标 context 可重新 certify；无专用 ancestry-preserving ctyp/cterm transfer 或 ML generic-context 契约测试。|
|82|`val transfer: theory -> thm -> thm`|K|部分|`KernelRules::transfer(&TrustedTheory, &KernelThm)`；`thm.rs::transfer_committed_ancestor_replays_in_target_owner`、`transfer_sibling_and_altered_source_are_rejected`。|
|83|`val transfer': Proof.context -> thm -> thm`|M|缺失|仅有显式 TrustedTheory 目标的 Rust transfer；无 Proof.context/Context.generic/join wrapper 或契约测试。|
|84|`val transfer'': Context.generic -> thm -> thm`|M|缺失|仅有显式 TrustedTheory 目标的 Rust transfer；无 Proof.context/Context.generic/join wrapper 或契约测试。|
|85|`val join_transfer: theory -> thm -> thm`|M|缺失|仅有显式 TrustedTheory 目标的 Rust transfer；无 Proof.context/Context.generic/join wrapper 或契约测试。|
|86|`val join_transfer_context: Proof.context * thm -> Proof.context * thm`|M|缺失|仅有显式 TrustedTheory 目标的 Rust transfer；无 Proof.context/Context.generic/join wrapper 或契约测试。|
|87|`val renamed_prop: term -> thm -> thm`|K|缺失|无对应受检公开操作/契约测试。|
|88|`val weaken: cterm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::weaken`；`pure_rule_extensions.rs::weaken_real_hypothesis_requires_discharge_before_acceptance`。|
|89|`val weaken_sorts: sort list -> cterm -> cterm`|K|缺失|无对应受检公开操作/契约测试。|
|90|`val proof_bodies_of: thm list -> proof_body list`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|91|`val proof_body_of: thm -> proof_body`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|92|`val zproof_of: thm -> zproof`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|93|`val proof_of: thm -> proof`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|94|`val reconstruct_proof_of: thm -> Proofterm.proof`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|95|`val consolidate: thm list -> unit`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|96|`val expose_proofs: theory -> thm list -> unit`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|97|`val expose_proof: theory -> thm -> unit`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|98|`val future: thm future -> cterm -> thm`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|99|`val thm_deps: thm -> Proofterm.thm Ord_List.T`|K|部分|`TrustedTheorem::dependencies`、私有 `DependencySet` 成员；`theory.rs::dependency_resolution_is_ancestry_bound`。无 ML Proofterm.thm 投影。|
|100|`val extra_shyps: thm -> sort list`|K|部分|`KernelThm::shyps` 与私有 payload 校验；`theorem_obligations.rs::theorem_erased_empty_sort_preserves_extra_sort_hypothesis`；无完整 extra_shyps ML 投影。|
|101|`val strip_shyps: thm -> thm`|K|部分|`KernelRules::strip_shyps`（`bound_proof/mod.rs`）；`sort_stripping.rs::strip_instantiated_empty_sort_closes_with_exact_statement`。|
|102|`val derivation_closed: thm -> bool`|M|缺失|`try_close/accept_closed_theorem` 检查逻辑闭合与接受，不是官方 derivation 的 lazy/name/position 效果；无同义 API/测试。|
|103|`val derivation_name: thm -> Thm_Name.T`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|104|`val derivation_id: thm -> Proofterm.thm_id option`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|105|`val raw_derivation_name: thm -> Thm_Name.P`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|106|`val expand_name: thm -> Proofterm.thm_header -> Thm_Name.P option`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|107|`val name_derivation: Thm_Name.P -> thm -> thm`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|108|`val close_derivation: Position.T -> thm -> thm`|M|缺失|`try_close/accept_closed_theorem` 检查逻辑闭合与接受，不是官方 derivation 的 lazy/name/position 效果；无同义 API/测试。|
|109|`val trim_context: thm -> thm`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|110|`val axiom: theory -> string -> thm`|K|部分|`theorem_builder::axiom_theorem` 只消费已授权 basis schema；`theory.rs::axiom_rejects_missing_basis_at_accept`。本闭环不调用。|
|111|`val all_axioms_of: theory -> (string * thm) list`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|112|`val get_tags: thm -> Properties.T`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|113|`val map_tags: (Properties.T -> Properties.T) -> thm -> thm`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|114|`val norm_proof: thm -> thm`|D|缺失|无对应公开转换/Proofterm 归一化 API 或契约测试。|
|115|`val adjust_maxidx_thm: int -> thm -> thm`|K|部分|`KernelThm::max_var_index`、`KernelRules::adjust_max_index`；`thm.rs::max_index_instantiation_retains_then_adjusts_checked_upper_bound`；Option/usize 不是 ML int 全域契约。|
|116|`val the_classrel: theory -> class * class -> thm`|K|部分|`TrustedTheory::find_class_relation/find_arity_certificate/install_class_relation/install_class_arity`；`class_proof_contract.rs::of_class_copied_graph_without_certificate_does_not_authorize`。certificate 查询/安装不是 ML thm 查询/更新。|
|117|`val the_arity: theory -> string * sort list * class -> thm`|K|部分|`TrustedTheory::find_class_relation/find_arity_certificate/install_class_relation/install_class_arity`；`class_proof_contract.rs::of_class_copied_graph_without_certificate_does_not_authorize`。certificate 查询/安装不是 ML thm 查询/更新。|
|118|`val sorts_zproof: theory -> ZTerm.sorts_proof`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|119|`val sorts_proof: theory -> Proofterm.sorts_proof`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|120|`val add_oracle: binding * ('a -> cterm) -> theory -> (string * ('a -> thm)) * theory`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|121|`val oracle_space: theory -> Name_Space.T`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|122|`val pretty_oracle: Proof.context -> string -> Pretty.T`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|123|`val extern_oracles: bool -> Proof.context -> (Markup.T * xstring) list`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|124|`val check_oracle: Proof.context -> xstring * Position.T -> string`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|125|`val assume: cterm -> thm`|K|部分|`KernelRules::assume(CProp)`；`fixed_type_scope.rs::certify_declared_fixed_type_supports_local_open_proof`；无两种 ML exception identity。|
|126|`val assume_cterm: cterm -> thm`|K|部分|`KernelRules::assume(CProp)`；`fixed_type_scope.rs::certify_declared_fixed_type_supports_local_open_proof`；无两种 ML exception identity。|
|127|`val implies_intr: cterm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::implies_intr`；`rules.rs::implies_intr_unused_assumption_preserves_closed_proof`。|
|128|`val implies_elim: thm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::implies_elim`；`owner_contract_regressions.rs::rotate_rule_nested_nonfirst_leaf_survives_strip_and_outer_permutation`。|
|129|`val forall_intr: cterm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::forall_intr`；`theory.rs::owner_acceptance_replays_nested_universal_introduction`。|
|130|`val forall_elim: cterm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::forall_elim`；`thm.rs::forall_elim_tampered_prop_fails_invariant`。|
|131|`val reflexive: cterm -> thm`|K|Rust 窄项已实现|`KernelRules::reflexive`；`theorem_obligations.rs::theorem_present_schema_sort_remains_closable_and_accepted`。|
|132|`val symmetric: thm -> thm`|K|Rust 窄项已实现|`KernelRules::symmetric`；`theorem_obligations.rs::theorem_symmetric_preserves_disappeared_empty_sort`。|
|133|`val transitive: thm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::transitive`（`rules.rs`）；规则存在，当前清单未指定独立转移闭环回归。|
|134|`val beta_conversion: bool -> conv`|K|部分|`KernelRules::beta_conversion` 单个 redex；`thm.rs::beta_conversion_tampered_prop_fails_invariant`；无官方 bool 模式 adapter。|
|135|`val eta_conversion: conv`|K|部分|`KernelRules::eta_conversion`；`pure_rule_extensions.rs::eta_conversion_accepts_exact_pure_equality_after_strip`；无 ML conv adapter。|
|136|`val eta_long_conversion: conv`|D|缺失|无对应公开转换/Proofterm 归一化 API 或契约测试。|
|137|`val abstract_rule: string -> cterm -> thm -> thm`|K|部分|`KernelRules::abstraction`；`thm.rs::abstraction_tampered_prop_fails_invariant`；参数与 ML cterm/name adapter 不同。|
|138|`val combination: thm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::combination`；`thm.rs::combination_tampered_prop_fails_invariant`。|
|139|`val equal_intr: thm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::equal_intr`；`thm.rs::equal_intr_tampered_prop_fails_invariant`。|
|140|`val equal_elim: thm -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::equal_elim`；`thm.rs::equal_elim_tampered_prop_fails_invariant`。|
|141|`val solve_constraints: thm -> thm`|K|部分|`KernelRules::solve_constraints`；`class_proof_contract.rs::solve_constraints_nonempty_sort_replays_real_arity`；不等于完整 ML 约束求解接口。|
|142|`val flexflex_rule: Proof.context option -> thm -> thm Seq.seq`|D+M|缺失|无官方搜索/Seq adapter 和契约测试；RSN 至多消费两个结果、重复 pull 等语义未验收。|
|143|`val generalize: Names.set * Names.set -> int -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::generalize` 按 type/term 名称集合与显式 fresh usize index 变换 P/F、保留 H/S/C/pending/mode；`variable_transformations.rs` 覆盖共享索引、下划线清洗、假设拒绝、边界及 maxidx 重算。局部 scope 需显式 `export_scope`；不等于 ML int/Names adapter。|
|144|`val generalize_cterm: Names.set * Names.set -> int -> cterm -> cterm`|K|Rust 窄项已实现|`ProofContext::generalize_term` 返回派生 context 与 CTerm；保留 scope，原 context 不改；`variable_transformations.rs` 覆盖连续消费、Bound 注解和缓存。非空选择缓存取 max(old,requested,actual)，是 Rust 安全下界强化，未声明官方缓存等价。|
|145|`val generalize_ctyp: Names.set -> int -> ctyp -> ctyp`|K|Rust 窄项已实现|`ProofContext::generalize_type` 保留 scope，checked usize/u32 索引；`variable_transformations.rs` 覆盖类型变换、空/未命中集合与缓存。没有 ML ctyp/int adapter。|
|146|`val instantiate: ctyp TVars.table * cterm Vars.table -> thm -> thm`|K|部分|`KernelRules::instantiate`；`theorem_instantiation.rs::instantiate_real_hypothesis_is_preserved_exactly`、`instantiate_replacement_type_mismatch_rejects`。|
|147|`val instantiate_beta: ctyp TVars.table * cterm Vars.table -> thm -> thm`|K|部分|composition 内部受检 beta instance；`pure_composition.rs::bicompose_candidate_beta_assignment_replays_source_and_accepts`；无独立同义公开 API。|
|148|`val instantiate_cterm: ctyp TVars.table * cterm Vars.table -> cterm -> cterm`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|149|`val instantiate_beta_cterm: ctyp TVars.table * cterm Vars.table -> cterm -> cterm`|K|缺失|无同义 certified-object API/契约测试；裸 Ty/Term 变换不能代替认证。|
|150|`val trivial: cterm -> thm`|D|部分|可由 `assume` + `implies_intr` 派生；`theory.rs::implication_identity` 被接受测试使用；无同名 facade。|
|151|`val of_class: ctyp * class -> thm`|K|部分|`KernelRules::of_class` 需要 ClosedOfClassProof；`class_proof_contract.rs::of_class_checked_theorem_accepts_exact_annotation`。|
|152|`val unconstrainT: thm -> thm`|K|部分|`KernelRules::unconstrain_t`；`class_proof_contract.rs::unconstrain_t_sorted_atom_exports_real_class_premise`。|
|153|`val varifyT_global': TFrees.set -> thm -> ((string * sort) * (indexname * sort)) list * thm`|K|缺失|无同义公开 theorem 变换 API/完整契约测试；内部 index freshening 不能当作 API 实现。|
|154|`val varifyT_global: thm -> thm`|K|缺失|无同义公开 theorem 变换 API/完整契约测试；内部 index freshening 不能当作 API 实现。|
|155|`val legacy_freezeT: thm -> thm`|K|缺失|无同义公开 theorem 变换 API/完整契约测试；内部 index freshening 不能当作 API 实现。|
|156|`val plain_prop_of: thm -> term`|D|部分|`KernelThm::prop` 与私有 `ProofPayload::flex_pairs` 分存；`pure_composition.rs::bicompose_candidate_unsolved_flex_never_closes`。无完整官方 full/plain projection adapter。|
|157|`val get_zproof_serials: theory -> serial list`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|158|`val get_zproof: theory -> serial -> {name: Thm_Name.P, thm: thm, zboxes: ZTerm.zboxes, zproof: zproof} option`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|159|`val store_zproof: Thm_Name.P -> thm -> theory -> thm * theory`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|160|`val dest_state: thm * int -> (term * term) list * term list * term * term`|D|部分|Term premise 投影与私有 flex payload 分离；`pure_composition.rs` 覆盖受检选择，不是完整 dest_state 投影契约。|
|161|`val lift_rule: cterm -> thm -> thm`|K|部分|`KernelRules::lift_rule`（`bound_proof/composition_lift.rs`）；`pure_composition.rs` 的 lift_rule 回归；不等于 ML context/cterm adapter。|
|162|`val incr_indexes: int -> thm -> thm`|K|Rust 窄项已实现|`KernelRules::incr_indexes`（`bound_proof/composition_index.rs`）先精确 owner/source replay，复用 SourceRenameIndex/AdjustMaxIndex；`native_thm_variables` 已执行双类型接受/引用链。局部 theorem 先 export_scope，usize 增量不覆盖负 ML int。|
|163|`val assumption: Proof.context option -> int -> thm -> thm Seq.seq`|D+K|部分|`KernelRules::assumption_candidate`（`bound_proof/composition_assumption.rs`）；`pure_composition.rs::assumption_candidate_existing_implication_after_substitution_replays`；无自动搜索/重复 pull Seq。|
|164|`val eq_assumption: int -> thm -> thm`|K|部分|`KernelRules::eq_assumption`；`pure_composition.rs::eq_assumption_outer_forall_then_implication_discharge_selected_goal`。|
|165|`val rotate_rule: int -> int -> thm -> thm`|K|部分|`KernelRules::rotate_rule`；`pure_premise_permutation.rs::rotate_selected_nested_forall_preserves_outer_tail`。|
|166|`val permute_prems: int -> int -> thm -> thm`|K|部分|`KernelRules::permute_prems`；`pure_premise_permutation.rs::permute_tail_negative_rotation_preserves_order_and_accepts`。|
|167|`val bicompose: Proof.context option -> {flatten: bool, match: bool, incremented: bool} -> bool * thm * int -> int -> thm -> thm Seq.seq`|D+K|部分|`KernelRules::bicompose_candidate(owner, context, options, rule, state, candidate)`；`CompositionOptions` 的 subgoal index 为 1-based；`pure_composition.rs::bicompose_candidate_exact_rule_premise_replays_and_accepts`、`bicompose_candidate_unsolved_flex_never_closes`；有限无权候选，不实现 ML unifier/Seq。|
|168|`val biresolution: Proof.context option -> bool -> (bool * thm) list -> int -> thm -> thm Seq.seq`|D+M|缺失|无官方搜索/Seq adapter 和契约测试；RSN 至多消费两个结果、重复 pull 等语义未验收。|
|169|`val theory_names_of_arity: {long: bool} -> theory -> string * class -> string list`|M|缺失|无对应 ML API/契约测试；不以 legacy core 或普通 VM 能力代替。|
|170|`val add_classrel: thm -> theory -> theory`|K|部分|`TrustedTheory::find_class_relation/find_arity_certificate/install_class_relation/install_class_arity`；`class_proof_contract.rs::of_class_copied_graph_without_certificate_does_not_authorize`。certificate 查询/安装不是 ML thm 查询/更新。|
|171|`val add_arity: thm -> theory -> theory`|K|部分|`TrustedTheory::find_class_relation/find_arity_certificate/install_class_relation/install_class_arity`；`class_proof_contract.rs::of_class_copied_graph_without_certificate_does_not_authorize`。certificate 查询/安装不是 ML thm 查询/更新。|

与 [P1 Host 合同](TRUST.md#p1-host-authority-and-immutable-context) 的差距：Rust 对象不能代替 ML generative opaque type/runtime-generation-phase 句柄；Result 错误不能代替 CTERM/THM/CONTEXT 的单一异常身份。fold callback 次序、trim 后 CONTEXT、Seq 重复 pull、oracle 注册及默认拒绝、future/proof/ZTerm 效果均须另外实现与验收。接受 token 只由 accept_closed_theorem 创建；本清单不授权补规则，也不将清单缺项加入首个闭环范围。
