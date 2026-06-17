---
description: 每次任务完成后的标准操作流程。Route A: 稳定性优先。
globs: "**/*"
alwaysApply: true
version: 2.0
updated: 2026-06-16
---

# 任务完成 SOP

> 每完成一个任务、一组改动、或对话结束时，按此流程操作。

## 流程

```
1. CHECK -> 2. AUDIT -> 3. TEST -> 4. UPDATE -> 5. COMMIT
```

⚠️ **硬性要求**：每次对话结束时必须执行 UPDATE 步骤，更新 .claude/ 以反映最新状态。
   下次对话开始时 .claude/ 就是唯一真相源，不需要用户反复强调。

## Step 1: CHECK — 编译检查

```bash
cargo check --lib  # 必须 0 warnings
```

## Step 2: AUDIT — 审计检查清单

| 检查项 | 命令 | 通过标准 |
|--------|------|:--:|
| 零警告编译 | `cargo check --lib` | 0 warnings, 0 errors |
| 无 `Typ::dummy()` 回退 | `rg 'Typ::dummy()' src/core/thm.rs src/core/logic.rs src/core/drule.rs` | 仅允许非推理规则 |
| 无裸 `Term::const_("HOL.xxx")` | `rg 'Term::const_\("HOL\.' src/ --glob '!src/hol/hologic.rs' --glob '!src/hol/simpdata.rs' --glob '!src/hol/hol_consts.rs'` | ≤3 (有意的) |
| 无重复 hologic 实现 | `rg 'fn mk_conj\|fn mk_disj\|fn mk_imp\|fn mk_not\|fn mk_eq\b' src/ --glob '!src/hol/hologic.rs'` | 空结果 |
| hologic 常量覆盖 | 任何新的 HOL const 必须有 hologic 函数 | 完整 |
| **Rust 风格错误** | 新错误有错误码 (E0xxx)、`= help:` 建议、源位置 | 全部通过 |
| **无裸 String 报错** | `rg 'format!("error\|eprintln!("error\|Err(.*format!' src/` | 倾向于 0 |

## Step 3: TEST — 测试

```bash
# 内核测试 (快速)
cargo test --lib core::thm core::unify

# 相关模块测试
cargo test --lib <changed_modules>

# 核心验证 (需要大栈)
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files --lib -- --nocapture
```

## Step 4: UPDATE — 必须更新的文件 (每次对话结束)

⚠️ **这是最重要的步骤。不执行会导致下次对话状态不一致。**

### 每次必更新

| 文件 | 更新内容 |
|------|---------|
| `.claude/rules/README.md` | 状态表、已知问题、铁律 |
| `.claude/rules/phase-sop.md` | 本文件 — 完成确认清单 |
| `CLAUDE.md` | 项目状态、Module Map、Known Issues、Skills |

### 有变更时更新

| 文件 | 触发条件 |
|------|---------|
| `.claude/settings.json` | 新权限、新命令、env 变更 |
| `.claude/skills/*.md` | Skill 命令/工作流变更 |
| `docs/ARCHITECTURE.md` | 架构层变更 |
| `docs/ROADMAP.md` | Phase 完成/规划变更 |
| `docs/GAP_ANALYSIS.md` | 覆盖度变更 |
| `docs/DEVELOPMENT.md` | 统计/命令变更 |
| `Cargo.toml` | 版本号变更 |

## Step 5: COMMIT — 提交

- 提交信息使用中文
- 不含 `Co-Authored-By:` 或任何 AI 署名
- 作者: MCB-SMART-BOY

---

## Phase 49-54 完成确认 (v1.9.0-dev)

- [x] `src/hol/hologic.rs` — HOL 抽象语法层巩固: 15+ 新函数, 100+ 裸 const 调用归口
- [x] `src/isar/term_parser.rs` — 32 处 Term::const_("HOL.xxx") → hologic 函数
- [x] `src/isar/linarith.rs` — 2 处 plus/Suc → hologic
- [x] `src/tools/tptp.rs` — 3 处 conj/All/eq → hologic
- [x] `src/tools/metis.rs` — 9 处 False → hologic
- [x] `src/hol/hol_loader.rs` — 14 处 Not/True/False/disj → hologic
- [x] `src/tools/simp.rs` — 41 处 → hologic
- [x] `src/isar/method.rs` — exec_induct 接入 Args::parse_modifiers()
- [x] `src/theory/loader.rs` — spec::* 解析器集成 (definition/axiomatization/abbreviation/type_synonym/typedecl)
- [x] `isabelle-source/` — Isabelle 2025 完整分发包就位 (364MB)
- [x] 构建零警告 (cargo check --lib)
- [x] 裸 HOL const 调用: 100+ → 3 (有意的)

## v2.0.0 完成确认

- [x] Route A Step 1: 5 测试修复 ✅ v1.8.1
- [x] Route A Step 2: OOM/栈溢出修复 ✅ v1.9.0-dev
- [x] Route A Step 3: Tier2 验证: 36/36 files 100% (2959/2959, 513s) ✅ v1.9.0
- [x] Route A Step 4: 属性系统补完 ✅ v1.9.0-dev
- [x] Route A Step 5: 全线文档同步 ✅ v1.9.0
- [x] Phase 3.1: 核心 simpset (8 theories, Rings 4x 加速) ✅ v1.9.0
- [x] Phase 3.2: 内存限界搜索 (PROOF_SEARCH_BUDGET) ✅ v1.9.0
- [x] Phase 3.3: rewrite 深度上限 (MAX_REWRITE_DEPTH=40) ✅ v1.9.0
- [x] Phase 4: tier2 扩展 (24→36 files) ✅ v1.9.0
- [x] Phase 5: v1.9.0 发布 ✅ v1.9.0
- [x] Cargo.toml version → 1.9.0

## 已解决的遗留问题

| 问题 | 状态 |
|------|:--:|
| auto.rs/blast.rs 空壳桩 | ✅ v1.8.0 已删除 |
| kernel/ 与 core/ 功能重叠 | ✅ v1.8.0 已合并 |
| test_verify_all_core_files 栈溢出 | ✅ v1.8.1 已修复 |
| prove_condition 设计缺陷 | ✅ v1.8.1 已修复 |
| metis 方法 → auto fallback | ✅ metis 已正确集成 |
| isabelle-source/ 为空 | ✅ 已填充 |
| hologic ops 散落 25+ 文件 | ✅ 已归口 (100→3) |
| 5 个测试失败 | ✅ v1.8.1 全部修复 |
| test_batch_scan_theories 栈溢出 | ✅ 115 files loaded cleanly |
| test_batch_verify_all OOM | ✅ 115 files 237/237 (100%) |
| repeat_conv 无限循环 | ✅ dest_equals 定点检测 |
| 属性系统 (7 gaps) | ✅ begin_lemma + lemmas + declare + attrs prop |
