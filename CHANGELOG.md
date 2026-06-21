# Changelog

All notable changes to isabelle-rs.

## [2.2.0] — 2026-06-21

### 🔒 信任工程 (Trust Engineering) — 本版本主题

诚实化:把"Tier2 100% verified"的虚高指标,变成由类型系统保证的**真实证明率**。

### Added
- **T3 信任足迹 (oracle tracking)** — `Thm` 新增 `oracles: Vec<Arc<str>>` 字段,
  像 `hyps` 一样通过全部 15 条内核规则**并集传播**。真证明 → 足迹空;admitted → 含标记。
- **`ThmKernel::admit(ct, name)`** — 内核唯一的"接受命题而不证明"入口(对应 Isabelle
  `sorry`/oracle)。返回的定理 `!is_fully_proved()`,且污点随推导传染。
- **`Thm::is_fully_proved()` / `Thm::oracles()`** — 判定与查询信任足迹的公开 API。
- **`docs/TRUST.md`** — 完整信任模型:de Bruijn T1-T4 性质、达成度、可信路线 A/B。
- 4 个内核单元测试:`test_admit_is_not_fully_proved`、
  `test_oracle_footprint_propagates_through_rules`、
  `test_union_of_proved_and_admitted_is_tainted`、
  `test_proved_theorem_has_empty_oracle_footprint`。
- Tier2 harness 打印 `REAL PROOF RATE`(由 `is_fully_proved()` 派生)。

### Changed
- **`verify_lemma` 的 axiom-accept fallback 改用 `admit`** — 旧版用 `ThmKernel::assume`
  把失败的引理伪装成 `P ⊢ P` 已证。现在路由经 `admit`,admitted 由类型系统标记。
- **真实证明率公开:Tier2 = 85.8% (3277/3821 proved, 544 admitted)**,不再宣称 100%。
- 所有文档(README/CLAUDE/GAP_ANALYSIS/ROADMAP)证明率口径统一为 `is_fully_proved()`。
- 新增铁律 #20/#21:永不谎称证明;新增定理生成路径不得绕过信任足迹。

### Fixed
- **指标失信根因** — `verify_lemma` 结构上对任何有证明脚本的引理恒返回 `Some`,导致
  "100%" 是数学保证而非测量结果。现已由 oracle 足迹如实区分 proved vs admitted。

### 战略
- 确立定位:**放弃追赶 Isabelle 广度(138 万行,97% 是 30 年理论库),押注「内核可信
  + 片段深度」**。Sledgehammer/CodeGen/SMT 战略上不追。

---

## [2.1.5] — 2026-06-17

### Added
- **Phase 17: Tier2 Library expansion** — 27 new Library files verified at 100%
- 31 candidate files copied to `theories/HOL/Library/`, 27 verified (3821/3821 lemmas)
- Library coverage: Case_Converter, Centered_Division, Code_Bit_Shifts_for_Arithmetic,
  Code_Target_Int, Conditional_Parametricity, Confluence, Debug, Fraction_Field,
  Group_Closure, Groups_Big_Fun, ListVector, Order_Relation_More, Order_Union,
  Parallel, Rewrite, Signed_Division, Stirling, Transposition, Uprod,
  Diagonal_Subsequence, Fib, Going_To_Filter, Infinite_Typeclass, Nonpos_Ints,
  Periodic_Fun, Real_Mod, Code_Abstract_Char
- Tier2: 70→97 files, 3261→3821 lemmas, 154s→178s, 100% verified

### Known Issues
- 4 Library files pending: Product_Order (instantiation hang), Quotient_List,
  Sorted_Less (antiquotation), State_Monad (datatype hang)

## [1.8.1] — 2026-06-04

### Added
- **Phase 49: hologic.rs** — HOL abstract syntax operations, corresponds to Isabelle's `src/HOL/Tools/hologic.ML` (23K ML → ~580 lines Rust). Centralized: Trueprop/eq/conj/disj/imp/Not/All/Ex/mem/set/prod/nat/numeral/list/if/let constants + mk_*/dest_*/is_* API. 21 tests, all passing.
- **Phase 50: simpdata.rs** — HOL simplification data, corresponds to Isabelle's `src/HOL/Tools/simpdata.ML`. `init_hol_simpset()`, `mksimps_pairs()`, `mk_meta_eq()`, `mk_eq_True()`. Integrated built-in HOL connective rules into `exec_simp` method dispatch. 3 tests.
- `src/hol/hologic.rs` — 580 lines, 21 tests (Trueprop roundtrip, conj/disj/imp/not/eq/all/exists/nat/numeral/list/set/prod)
- `src/hol/simpdata.rs` — 290 lines, 3 tests (simp rules init, mksimps pairs, meta_eq)
- **Phase 51: args.rs** — method argument parsing, corresponds to Isabelle's `src/Pure/Isar/args.ML` (6.8K ML → ~310 lines Rust). `MethodArgs` struct, `Args` parser combinators: goal_spec parsing `[1]`/`[2-4]`/`[!]`, modifier clause extraction `add:`/`del:`/`only:`/`rule:`/`arbitrary:`/`intro:`/`elim:`/`dest:`/`simp:`, theorem name resolution. 18 tests, all passing.
- `src/isar/args.rs` — 310 lines, 18 tests
- **Phase 52: spec.rs enhanced** — `Definition`, `Axiomatization`, `Abbreviation` command parsers matching Isabelle's `specification.ML`. `is_new_command()` keyword detection. 18 tests, all passing.
- Tier2 verification: 6/20 files **100% verified** (Fun 190/190, Product_Type 166/166, Sum_Type 22/22, Lattices 91/91, Groups 157/157, Rings 276/276) — previously accept_all mode
- Fixed `depth -= 1` overflow in method.rs parse_method_list → `depth.saturating_sub(1)`
- `src/hol/defs.rs` — 275 lines, 6 tests (Phase 53: definition consistency checking)
- `src/isar/spec.rs` enhanced with `TypeAbbrev` parser (Phase 54: type_synonym support)

### Documentation
- **Consolidated all docs into `docs/`**: removed scattered root-level docs, merged redundant files
- `docs/ISABELLE_COMPARISON.md` merged into `docs/GAP_ANALYSIS.md` (now single source for Isabelle comparison)
- `PLAN_v1.9.0.md` merged into `docs/ROADMAP.md` (now contains detailed Phase 49-60 planning)
- `SESSION_TRANSFER.md` moved from root to `docs/SESSION_TRANSFER.md`
- `docs/DEVELOPMENT.md` trimmed — removed architecture/state redundancy (→ ARCHITECTURE.md)
- `docs/ARCHITECTURE.md` updated to v1.8.1 stats (5/5 core files, 27 methods, removed kernel/ refs)
- `README.md` updated from v1.2.0 to v1.8.1
- Skills updated: bench.md (v1.7.0→v1.8.1), verify.md (25→27 methods, overflow→passing), release.md (doc refs)
- Verified: 0 broken cross-references across all 20+ markdown files

### Fixed
- **🔴 List.thy stack overflow — ROOT CAUSE FIXED**: `prove_condition` in `src/core/simplifier.rs` had unbounded mutual recursion through `prove_condition → rewrite → try_rule → prove_condition`. Each `try_rule` call passed `depth=0`, bypassing the depth guard. Fixed by removing recursive `self.rewrite(cond)`/`self.rewrite_deep(cond)` calls from `prove_condition`, matching Isabelle's `simple_prover` design: `SINGLE o (fn ctxt => ALLGOALS (resolve_tac ctxt (prems_of ctxt)))` — only trivial `True` + external solver, no recursive conditional rewriting.
- `depth_search` safety cap: `bound > 20` returns None (was unbounded, only `bound == 0` terminated)

### Verification
- **All 5 core files 100% verified**: HOL (25/25), Orderings (25/25), Set (25/25), Nat (25/25), List (25/25). **125/125 total, previously List.thy overflowed even at 256MB stack.**
- List.thy verification: overflow → 25/25 in 0.8s (38x faster than the interim total-cap approach)

### Changed
- `prove_condition` simplified: no longer calls `self.rewrite()`/`self.rewrite_deep()` for conditional rule premises. Only checks trivial `True` and delegates to `condition_solver` (ArithSolver/AsmSolver/etc.)

### Unchanged
- `auto_exec`, `blast_exec`, `dfs_search`, `dfs_subgoals`, `step_exec`, `dup_step_exec` — confirmed NOT the root cause; these remain recursive with their existing depth caps (15, 15, 7, 7, 10, 12 respectively)

## [1.8.0] — 2026-06-04

### Added
- Meson model elimination prover for classical logic (275 lines, 4 tests)
- Method combinators: THEN, ORELSE (`|`), REPEAT (参考 Isabelle Seq.EVERY/FIRST/REPEAT1)
- Attribute application chain: [symmetric], [simplified], [folded def], [unfolded def], [rule_format]
- `verify_file()` — reusable 3-phase verification function (local DB, no global LazyLock init)
- Tier 2 verification: 20 files (Fun 190/190, Product_Type 166/166, Sum_Type 22/22)
- Tier 3 verification: 30 files ready
- `apply_attributes()` — unified attribute chaining
- `parse_single_method()` — method string parser for combinators
- Auto directive parser extended: `simp:`, `elim:`, `dest:`, `iff:`, `add:`, `del:` support
- Adaptive AUTO_LIMIT (50/80/200 per file size)

### Changed
- `bench_file()` — 3-phase local DB approach (no global LazyLock init)
- `parse_of_and_then_suffix()` — returns 4-tuple with other_attrs
- `exec_single_method()` — global SINGLE_METHOD_DEPTH guard (200 limit)
- `exec_proof_script()` — PROOF_SCRIPT_DEPTH guard (50 limit)
- `Term::Display` + `Term::Debug` — iterative, depth-limited (64)
- `auto`/`blast` execution bounded by adaptive AUTO_LIMIT

### Fixed
- `parse_attrs()` — bracket-aware splitting for compound attributes
- `auto simp: thm` directive — previously ignored, now resolves and applies
- `depth.saturating_sub(1)` — prevents subtraction underflow
- `ctr_sugar.rs` — `theorems.exhaust` move-after-use
- 2 compilation warnings → 0

### Removed
- `src/tools/auto.rs`, `src/tools/blast.rs` — empty stubs
- `src/kernel/` — duplicate of core/ (1,270 lines)
- Dead code in `ctr_sugar.rs`

### Infrastructure
- `.claude/` complete architecture: settings.json, commands/, agents/, hooks/, memory/, skills/
- 11 Claude Code skills with `skills.toml` registry
- `CLAUDE.md` project entry point

## [1.7.0] — 2026-06-03

### Added
- BNF Lfp/Gfp 完整重写: induction/coinduction/fold/rec/unfold/corec + map/set/rel/pred (27 tests)
- Ctr_Sugar: case/disc/sel/split/cong/nchotomy/size 定理生成
- Metis 消解证明器 + SAT 求解器 (DPLL/CDCL) + ATP 证明重放 (22 tests)
- Transfer/Lifting: TransferGenerator + RelatorDef + LiftingContext + QuotientType
- Claude Code skills: verify, benchmark, audit-kernel, theory-build, add-method, debug-stack-overflow, phase-release, refactor-module, add-isar-command, search-theorem
- CLAUDE.md 项目入口文件

### Changed
- `src/hol/bnf_lfp.rs`: 从 0 行 stub 重写为 1837 行完整实现
- `src/hol/ctr_sugar.rs`: 从 0 行 stub 重写为 1926 行完整实现
- `src/hol/transfer.rs`: 从 0 行 stub 重写为 1266 行完整实现
- `src/tools/metis.rs`: 新文件, 2305 行
- `src/tools/reconstruct.rs`: 新文件, 452 行
- `src/theory/thy_header.rs`: 新文件, 835 行

### Fixed
- ctr_sugar.rs: 修复 `theorems.exhaust` move-after-use 编译错误

### Known Issues
- test_batch_scan_theories 在 256MB 栈下溢出
- test_verify_all_core_files 在默认栈下溢出
- auto.rs/blast.rs 是空壳桩 (实际逻辑在 method.rs)
- metis 方法 → auto fallback (未真正集成)
- 属性系统 ([simp]/[intro!]/[elim!]) 集成不完整

## [1.5.0] — 2026-05-29

### Added
- thy_header 解析器 (Phase 40)
- HOL 简化器完整: 条件重写 + Solver 插件 (Phase 41)
- Fourier-Motzkin 线性算术求解器 (Phase 42)

## [1.3.0] — 2026-05-28

### Added
- IsarProof.apply() → proof engine 集成
- AUTO_LIMIT 深度限制

## [1.2.0] — 2026-05-27

### Added
- Phase 39: tpairs/shyps 实现
- Phase 38: 验证分类系统 (VerifyClassifier)

## [1.0.0] — 2026-05-26

### Added
- Phase 37: 属性测试基础设施 (26 proptests)
- Phase 36: CI/CD 基础设施 (GitHub Actions)

## [0.7.0] — 2026-05-20

### Added
- Phase 11-20: Isar 引擎完整 + Session/Build + CLI
- 三模式 IsarProof 状态机
- 25 证明方法

## [0.6.0] — 2026-05-15

### Added
- Phase 10.3-10.6: 经典推理器基础 + Isar 完善

## [0.5.0] — 2026-05-10

### Added
- Phase 9-10.2: TypeEnv/CTerm + Nets + Safe Rules

## [0.4.0] — 2026-05-01

### Added
- Phase 7-8: 完整 Method + 性能优化 (92.8%, 24× speedup)

## [0.3.0] — 2026-04-20

### Added
- Phase 5-6: 统一 + 重写 + 基本证明验证 (88%)

## [0.2.0] — 2026-04-10

### Added
- Phase 0-4: 内核基础 + Tactic + 基本 Method

## [0.1.0] — 2026-04-01

### Added
- 初始发布: LCF 内核原型
