# Isabelle 功能对照

## 内核基础设施

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| Thm.instantiate | ✅ | ✅ | Envir → Thm |
| Thm.bicompose | ✅ | ✅ | 核心 resolution 操作 |
| Thm.nprems_of / prem / concl | ✅ | ✅ | 目标状态访问 |
| Thm.assume | ✅ | ✅ | |
| Thm.implies_intr | ✅ | ✅ | 零 panic |
| Thm.implies_elim | ✅ | ✅ | 零 panic |
| Thm.reflexive / symmetric / transitive | ✅ | ✅ | 零 panic |
| Thm.combination / abstraction | ✅ | ✅ | 副作用检查 |
| Thm.beta_conversion | ✅ | ✅ | |
| Thm.forall_intr / forall_elim | ✅ | ✅ | 零 panic |
| **总计** | **13** | **13** | **100% 等价** |

## 定理加载能力

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| 内联引理 `lemma name: "stmt"` | ✅ | ✅ | |
| 多行 assumes/shows | ✅ | ✅ | |
| fixes/obtains | ✅ | ✅ | 跳过 fixes 绑定 |
| 匿名引理 `lemma [code]:` | ✅ | ✅ | 自动生成 [anon:...] 名称 |
| 多结论内联 `"A" "B"` | ✅ | ✅ | 生成 name_2, name_3 |
| Cartouche `\<open>...\<close>` | ✅ | ✅ | 转换为双引号 |
| Locale 引理 `(in loc)` | ✅ | ✅ | 剥离 locale 前缀 |
| `lemmas` 命令 | ✅ | ❌ | |
| `class`/`context` 块内引理 | ✅ | ❌ | |

## 语法支持

| 语法 | 状态 | 说明 |
|------|:--:|------|
| `\<forall>`/`\<exists>`/`\<And>` | ✅ | 量词 |
| `\<in>`/`\<notin>` | ✅ | 集合隶属 |
| `\<le>`/`\<ge>`/`\<subseteq>` | ✅ | 序关系 |
| `\<union>`/`\<inter>`/`\<Union>` | ✅ | 集合运算 |
| `\<lbrakk>`/`\<rbrakk>` | ✅ | 结构化前提 |
| `==>`/`-->`/`\<Longrightarrow>` | ✅ | 蕴含 |
| `&`/`|`/`~`/`=`/`~=` | ✅ | 逻辑连接词 |
| `#` (Cons) / `@` (Append) | ✅ | 列表操作 |
| `<` / `>` / `+` / `-` | ✅ | 算术/集合运算 |
| `{..n}` / `{a..b}` | ✅ | 集合范围 |
| `[a..b]` / `[a..<b]` | ✅ | 列表范围 |
| `{x. P x}` / `{x \| P x}` | ✅ | 集合推导 |
| `if C then A else B` | ✅ | 条件表达式 |
| `case E of P => R` | ✅ | Case 表达式 |
| `let x = e in b` | ✅ | Let 绑定 |
| `(<)` / `((#) x)` | ✅ | 操作符章节 |
| `\<Sqinter>` / `\<Squnion>` | ✅ | 下确界/上确界 |
| `\<exists>\<^sub>\<le>\<^sub>1` | ✅ | 至多一个存在 |

## 定理覆盖

| 理论文件 | 总声明 | 已加载 | 覆盖率 |
|----------|--------|--------|:--:|
| HOL.thy | 254 | 254 | 100% |
| Orderings.thy | 153 | 153 | 100% |
| Nat.thy | 360 | 360 | 100% |
| Set.thy | 412 | 412 | 100% |
| List.thy | 1,257 | 1,257 | 100% |
| **合计** | **2,436** | **2,436** | **100%** |

## 待实现

| 功能 | 优先级 |
|------|:--:|
| `apply`/`done` 证明脚本执行 | 🔴 |
| `simp`/`auto` tactic | 🔴 |
| `by (induct ...)` 归纳证明 | 🟠 |
| `proof ... qed` 结构化证明 | 🟠 |
| `have`/`show`/`hence`/`thus` | 🟡 |
| `case`/`cases`/`fix`/`assume`/`obtain` | 🟡 |
| 类型推理 (Typ::dummy → 实际类型) | 🟡 |
| 理论导入图 (theory DAG) | 🟢 |
| 全部 100+ .thy 文件加载 | 🟢 |
