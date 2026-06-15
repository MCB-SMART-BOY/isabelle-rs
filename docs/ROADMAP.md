# 开发路线图 v23.0 (v1.9.0-dev → v2.0.0)

> **当前版本**: v1.9.0-dev — Route A 稳定性优先, Tier2 验证扩展中
> **下一目标**: v1.9.0 — Route A 完成 (Tier2 + 属性集成 + 文档同步)

---

## 总体策略

```
v1.9.0-dev (当前) Route A 进行中:
                 ✅ 5 测试修复
                 ✅ OOM 根因修复
                 🔄 Tier2 验证扩展 (6/19 files 100%, tmux 运行中)
                 ✅ 属性系统补完 (begin_lemma + lemmas + declare)
                 🔄 文档同步
    ↓
v1.9.0          Route A 完成 + Tier2 ≥15/19 files 100%
    ↓
v2.0.0          Metis 真正集成 + 全库验证 1000+ files
```

---

## 版本发布计划

| 版本 | 日期 | 状态 | 关键交付 |
|------|------|:--:|------|
| v1.9.0-dev | 2026-06-16 | 🔄 current | Route A: 5 tests fixed, OOM fixed, 属性补完, Tier2 running |
| v1.8.1 | 2026-06-04 | ✅ | 5/5 core files 125/125, prove_condition 修复 |
| v1.8.0 | 2026-06-03 | ✅ | Meson, 方法组合子, 属性链, verify_file(), Tier2/Tier3 |
| v1.7.0 | 2026-06-03 | ✅ | BNF Lfp/Gfp 完整, Ctr_Sugar, Metis, Transfer/Lifting |
| v1.5.0 | 2026-05-29 | ✅ | thy_header, HOL Simplifier, FM Arith |
| v1.3.0 | 2026-05-28 | ✅ | IsarProof.apply(), AUTO_LIMIT |
| v1.2.0 | 2026-05-27 | ✅ | tpairs/shyps, VerifyClassifier |
| v1.0.0 | 2026-05-26 | ✅ | Property testing, CI/CD |
| v0.7.0 | 2026-05-20 | ✅ | Isar engine, 25 methods, Session/Build, CLI |
| v0.6.0 | 2026-05-15 | ✅ | Classical reasoner, Isar enhancements |
| v0.5.0 | 2026-05-10 | ✅ | TypeEnv/CTerm, Nets, Safe Rules |
| v0.4.0 | 2026-05-01 | ✅ | Complete Method, perf (24x speedup) |
| v0.3.0 | 2026-04-20 | ✅ | Unify, rewrite, basic verification (88%) |
| v0.2.0 | 2026-04-10 | ✅ | Kernel basics, Tactic, basic Methods |
| v0.1.0 | 2026-04-01 | ✅ | LCF kernel prototype |

---

## 已完成 Phase 详细

### Phase 0-20: 内核 + Isar + Session/Build ✅

| 版本 | 阶段 | 关键交付 |
|------|------|---------|
| v0.1.0-v0.2.0 | Phase 0-4 | 内核基础 + Tactic + 基本 Method |
| v0.3.0 | Phase 5-6 | 统一 + 重写 + 基本证明验证 (88%) |
| v0.4.0 | Phase 7-8 | 完整 Method + 性能优化 (92.8%) |
| v0.5.0 | Phase 9-10.2 | TypeEnv/CTerm + Nets + Safe Rules |
| v0.6.0 | Phase 10.3-10.6 | 经典推理器基础 + Isar 完善 |
| v0.7.0 | Phase 11-20 | Isar 引擎完整 + Session/Build + CLI |

### Phase 21: 类型安全 ✅
- `combination` → `Err(NotFunctionType)`, 0 `Typ::dummy()` fallback
- `CTerm::certify_annotated` + `CTerm::require_non_dummy`

### Phase 22: 经典推理器 ✅
- `apply_safe_rules` 三阶段: match → elim_match → resolution
- `fast_exec`/`best_exec`/`depth_exec`/`dup_step_exec`

### Phase 23: induct/cases ✅
- `lookup_theorem` DB 连接, `exec_induct` 重写, type-based rule lookup

### Phase 24: Locale/Type Class ✅
- 8 commands: locale, class, subclass, instance, interpretation, etc.

### Phase 25: Pretty Printer ✅
- 20+ operators, 7 precedence levels, binders

### Phase 26: typedef/record ✅
### Phase 27: Function 包 ✅
### Phase 28: Inductive 包 ✅
### Phase 29: 库验证扩展 ✅
### Phase 30: 稳定化 ✅
### Phase 31: Sledgehammer/TPTP ✅
### Phase 32: LSP 完善 ✅
### Phase 33: BNF/datatype 深化 ✅
### Phase 34: 文档同步 ✅
### Phase 35: 软件工程 Skills ✅
### Phase 36: CI/CD ✅
### Phase 37: 属性测试基础设施 ✅
### Phase 38: 验证分类系统 ✅
### Phase 39: tpairs/shyps ✅
### Phase 40: thy_header 解析器 ✅
### Phase 41: HOL 简化器 ✅
### Phase 42: Fourier-Motzkin 算术 ✅
### Phase 43-44: BNF Lfp/Gfp ✅
### Phase 45-46: Transfer/Lifting ✅
### Phase 47: Ctr_Sugar ✅
### Phase 48: Metis ✅

---

## v1.9.0 规划: "HOL 基础设施现代化"

> **核心洞察**: Isabelle 的 23K 行 `hologic.ML` → isabelle-rs 仅 43 行 `term_builder.rs` — 差了 500 倍。
> HOL term ops 散落 25+ 文件, `by simp` 规则不完整, 方法参数解析缺失。

### Phase 49: hologic.ML → hologic.rs (🥇 P0, 收益最大)

| 项目 | 内容 |
|------|------|
| **Isabelle 源** | `src/HOL/Tools/hologic.ML` (23K, 160+ API) |
| **新建文件** | `src/hol/hologic.rs` (~1500 行) |
| **核心 API** | `dest_Trueprop`/`mk_eq`/`dest_eq`/`mk_conj`/`dest_conj`/`mk_imp`/`dest_imp`/`mk_not`/`dest_not`/`mk_all`/`mk_exists`/`mk_mem`/`dest_mem`/`mk_set`/`mk_prod`/`dest_prod`/`mk_numeral`/`mk_if`/`dest_if` |
| **验收** | 所有 API 有单元测试; 5 core files 无退化; ≥10 文件迁移到 hologic |

### Phase 50: simpdata.ML → simpdata.rs (🥈 P0)

| 项目 | 内容 |
|------|------|
| **Isabelle 源** | `src/HOL/Tools/simpdata.ML` (7.2K) |
| **新建文件** | `src/hol/simpdata.rs` (~600 行) |
| **内容** | `init_hol_simpset()` 统一入口; `if_True`/`if_False`/`Let_def`/`case_split`; Quantifier1 量词简化 |
| **验收** | `by simp` 通过率 +10%+ |

### Phase 51: args.ML (🥉 P0)

| 项目 | 内容 |
|------|------|
| **Isabelle 源** | `src/Pure/Isar/args.ML` (6.8K) + `method.ML` (30K) |
| **新建文件** | `src/isar/args.rs` (~800 行) |
| **关键** | `Args.add`/`Args.del`/`Args.named_source`/`Args.goal_spec` |
| **验收** | `simp add:` / `induct rule:` 可解析 |

### Phase 52-54: 规范基础设施 (P1)

| Phase | 内容 | Isabelle 源 | 新/改文件 |
|:---:|------|------------|-----------|
| 52 | specification.ML | 19K | `src/isar/spec.rs` 增强 |
| 53 | defs.ML 定义一致性 | 9.4K | `src/hol/defs.rs` 新建 |
| 54 | typedecl.ML + local_defs.ML | 13K | `src/isar/typedecl.rs` 新建 |

### Post-v1.9.0

| Phase | 内容 | 优先级 |
|:---:|------|:--:|
| 55 | Tier2 验证扩展 | P1 |
| 56 | Metis 真正集成 | P1 |
| 57 | 属性系统完成 | P1 |
| 58 | Sledgehammer 深化 | P2 |
| 59 | Code Generator | P3 |
| 60 | SMT 集成 | P3 |

---

## 设计原则

1. **渐进式替换，而非大爆炸重写**
2. **先读 Isabelle 源码再写 Rust 代码**
3. **多层 fallback 优于单点完美**
4. **数据结构先行，集成后行**
5. **保留 Isabelle 语法兼容**
6. **`Typ::dummy()` 清零是最高优先级** ✅
7. **改后跑 `test_verify_all_core_files` — 不能有退化**
8. **对照 Isabelle 源码写，不要自己发明**
