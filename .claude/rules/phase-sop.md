---
description: 阶段完成后的标准操作流程。
globs: "**/*"
alwaysApply: false
version: 1.5
updated: 2026-06-03
---

# 阶段完成 SOP

> 每完成一个 Phase 或一组关联任务后，按此流程操作。

## 流程

```
1. SUMMARIZE -> 2. AUDIT -> 3. TEST -> 4. UPDATE -> 5. VERIFY
```

⚠️ **硬性要求**：每次完成任何任务/Phase/功能后，必须执行完整的 AUDIT + UPDATE 流程。不可跳过。

## 审计检查清单 (Step 2: AUDIT — 每次必须执行)

| 检查项 | 命令/方法 | 通过标准 |
|--------|----------|:--:|
| 零警告编译 | `cargo check --lib` | 0 warnings |
| 相关模块测试 | `cargo test --lib <changed_modules>` | 全部通过 |
| 无 `Typ::dummy()` 回退 | `rg 'Typ::dummy()' src/core/thm.rs src/core/logic.rs src/core/drule.rs` | 仅允许在非推理规则中 |
| 无裸 `Term::const_("HOL.xxx")` 绕过 hologic | `rg 'Term::const_\("HOL\.' src/ --glob '!src/hol/hologic.rs'` | 仅允许在 hologic.rs 内部 |
| 无重复实现 | `rg 'fn mk_conj\|fn mk_disj\|fn mk_imp\|fn mk_not\|fn mk_eq\b' src/ --glob '!src/hol/hologic.rs'` | 空结果（无本地重复） |
| hologic 常量覆盖 | 检查新增 Term::const_("HOL.xxx") 是否已有 hologic 等价 | 应有尽有 |

## 必须更新的文件

| 文件 | 更新内容 |
|------|---------|
| `README.md` | 版本号、验证数、新特性 |
| `Cargo.toml` | version, description |
| `CHANGELOG.md` | 版本变更记录 |
| `CLAUDE.md` | 项目状态表, 已知问题, Iron Laws, Module Map, Skills 列表 |
| `docs/ARCHITECTURE.md` | 状态标记、速查表 |
| `docs/ROADMAP.md` | Phase 标记 v, 验证数 |
| `docs/DEVELOPMENT.md` | 性能基准、项目统计, 已知问题 |
| `docs/GAP_ANALYSIS.md` | 覆盖度百分比、完成模块 |
| `.claude/rules/README.md` | 项目状态表、铁律, 已知问题 |
| `.claude/rules/phase-sop.md` | 完成确认清单 |
| `.claude/settings.json` | 新权限、新命令、env 变更 |
| `.claude/skills/SKILL.md` | Master skill index（如有新增/删除 skill） |
| `.claude/skills/skills.toml` | Skill 注册表（如有新增/删除 skill） |
| `.claude/skills/*.md` | 各 skill 文件的命令/工作流变更 |
| `.claude/skills/run-isabelle-rs/SKILL.md` | 运行命令、gotchas 变更 |
| `.claude/skills/run-isabelle-rs/driver.sh` | 冒烟测试脚本变更 |

## Phase 40-42 完成确认 (v1.3.0)

- [x] `src/theory/thy_header.rs` — 完整理论头解析器 (24 tests)
- [x] `src/tools/simp.rs` — HOL 简化器重写: 条件重写 + Solver 插件 (26 tests)
- [x] `src/isar/linarith.rs` — Fourier-Motzkin 算术求解器重写 (32 tests)
- [x] `src/core/simplifier.rs` — ConditionSolver 内核钩子
- [x] `src/isar/method.rs` — 集成 HolSimplifier (exec_simp/exec_simp_all)
- [x] Method::Simp 枚举从 Simplifier 迁移到 HolSimplifier
- [x] `src/main.rs` — 添加 mod tools;
- [x] docs 全线更新: ARCHITECTURE v17.0, ROADMAP v18.0, GAP v1.3.0
- [x] Cargo.toml v1.3.0
- [x] .claude/rules/README.md 更新项目状态表
- [x] 零警告编译 (cargo check --lib)
- [x] 82 新测试全部通过

## Phase 43-48 完成确认 (v1.7.0)

- [x] `src/hol/bnf_lfp.rs` — BNF Lfp/Gfp 完整重写: induction/coinduction/fold/rec/unfold/corec (27 tests)
- [x] `src/hol/ctr_sugar.rs` — Ctr_Sugar: case/disc/sel/split/cong/nchotomy/size 定理生成
- [x] `src/tools/metis.rs` — Metis 消解证明器 + DPLL/CDCL SAT solver + ATP 证明重放 (22 tests)
- [x] `src/tools/reconstruct.rs` — 集成 Metis: sledgehammer_prove() + reconstruct_from_atp()
- [x] `src/hol/transfer.rs` — Transfer/Lifting: TransferGenerator + RelatorDef + LiftingContext + QuotientType
- [x] docs 全线更新: Cargo.toml v1.7.0, ROADMAP v20.0, ARCHITECTURE v20.0
- [x] .claude/rules/README.md 更新项目状态表
- [x] CLAUDE.md 更新
- [x] 10 个 Claude Code skills 创建 (`.claude/skills/`)
- [x] 零警告编译 (cargo check --lib)
- [x] ctr_sugar.rs move-after-use 编译错误修复

## v1.7.0 已知遗留问题

- [ ] test_batch_scan_theories 256MB 栈溢出 — 需迭代化
- [ ] test_verify_all_core_files 默认栈溢出 — 需迭代化
- [ ] auto.rs/blast.rs 空壳桩 — 待清理
- [ ] metis 方法 → auto fallback — 待集成
- [ ] 属性系统集成不完整 — 待完成
- [ ] CHANGELOG.md 缺失 — 待创建
- [ ] kernel/ 与 core/ 功能重叠 — 待合并
