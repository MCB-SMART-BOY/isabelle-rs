---
description: Security best practices for a trusted kernel. Unsafe code audit, supply chain, memory safety, fuzzing, cryptographic integrity.
globs: "**/*.rs"
alwaysApply: false
version: 1.0
updated: 2026-05-29
---

# Security Rules

> "Security is not a feature. It's a property of the whole system." — Every security engineer ever.

## 触发条件

使用 `unsafe`、添加外部依赖、处理不受信任输入、或修改内核时应用。

## 铁律

1. **内核层 `#[deny(unsafe_code)]`** — 除了显式允许的模块 (`src/core/thm.rs`, `src/hol/hol_loader.rs` 的裸指针)
2. **每个 `unsafe` 块必须有 `// SAFETY:` 注释** — 说明前置条件和不变量
3. **依赖必须审查** — 新增依赖需评估供应链风险
4. **不信任外部输入** — `.thy` 文件内容必须验证后再处理
5. **`cargo audit` 定期运行** — 检查已知漏洞

## 模式 1: Unsafe 审计清单

对于每个 `unsafe` 块，验证:

```rust
// SAFETY: <解释为什么安全>
// 前置条件:
//   1. ptr 非空 (由调用者保证)
//   2. ptr 指向的内存在闭包执行期间有效
//   3. 不存在数据竞争 (thread_local! 保证线程隔离)
//   4. 不存在可变别名 (RefCell 保证运行时检查)
unsafe { &*ptr }
```

### 审计清单
- [ ] 是否遵守 Rust 的引用规则？(无别名可变引用)
- [ ] 是否避免了数据竞争？
- [ ] 指针是否非空？
- [ ] 是否有内存泄漏风险？
- [ ] 是否有 use-after-free 风险？
- [ ] 是否有 buffer overflow？
- [ ] 整数溢出是否被考虑？

## 模式 2: 依赖管理

```bash
# 审计依赖
cargo audit                # 检查已知漏洞
cargo deny check           # 许可证 + 重复依赖
cargo tree --duplicates    # 检测重复依赖
cargo outdated             # 检查过期依赖
```

### 依赖评审标准

| 标准 | 要求 |
|------|------|
| 下载量 | > 10,000 (流行度信号) |
| 维护状态 | 最近 6 个月有更新 |
| 许可证 | MIT / Apache-2.0 / BSD (兼容项目) |
| `unsafe` 使用 | 最少，有文档 |
| 依赖深度 | ≤ 3 层间接依赖 |
| 作者信誉 | 已知社区成员或组织 |

## 模式 3: 输入验证

```rust
// ✅ 推荐: 验证外部输入
pub fn process_source(source: &str) -> Result<Theory> {
    // 1. 大小限制
    if source.len() > MAX_THEORY_SIZE {
        return Err(IsabelleError::Config(
            format!("theory too large: {} bytes", source.len())
        ));
    }

    // 2. 编码检查
    if source.contains('\0') {
        return Err(IsabelleError::Parse {
            msg: "null byte in input".to_string(),
            pos: 0,
        });
    }

    // 3. 解析验证
    let spans = OuterSyntax::parse_spans(source)?;

    // 4. 深度限制 (防止栈溢出)
    if spans.len() > MAX_SPANS {
        return Err(IsabelleError::Config("too many spans".to_string()));
    }

    // proceed...
}

// ❌ 避免: 信任输入
pub fn process_source_bad(source: &str) -> Theory {
    let spans = OuterSyntax::parse_spans(source).unwrap(); // panic on malformed
    // no size limit
    // no validation
    // ...
}
```

## 模式 4: 内存安全保证

```rust
// Legacy src/core LCF 内核通过设计保证安全性:
// 1. Thm 没有公开构造器 → 不能凭空构造定理
// 2. ThmKernel 是唯一创建 Thm 的路径 → 集中审计
// 3. CTerm 通过 certify 构造 → 类型检查必经之路
// 4. 所有 Term 创建经过类型检查 → 无恶意 term 注入

pub struct Thm {
    pub(crate) prop: CTerm,     // 命题
    pub(crate) hyps: Hyps,      // 假设 (α-equivalence)
    pub(crate) maxidx: usize,   // 最大索引
    pub(crate) derivation: Derivation, // 推导历史
}
// Legacy Thm 字段是 pub(crate) → 外部 crate 不能直接构造。
// Strict src/kernel 更窄：认证/定理构造 helper 必须是
// pub(in crate::kernel) 或更窄，不能对整个 crate 开放。
```

## 模式 5: Cryptographic Integrity (未来)

```rust
// 定理数据库完整性校验 (Phase 34+)
pub struct SignedTheory {
    pub theory: Arc<Theory>,
    pub hash: [u8; 32],  // SHA-256
    pub signature: Option<Vec<u8>>,
}

impl SignedTheory {
    pub fn verify_integrity(&self) -> Result<()> {
        let computed = sha2::Sha256::digest(&bincode::serialize(&self.theory)?);
        if computed.as_slice() != &self.hash {
            return Err(IsabelleError::Config("theory hash mismatch".to_string()));
        }
        Ok(())
    }
}
```

## 安全威胁模型

| 威胁 | 缓解措施 | 状态 |
|------|---------|:--:|
| 恶意 .thy 文件 → panic | 输入验证 + panic-per-span 恢复 | ✅ |
| 恶意 .thy 文件 → 错误定理 | LCF 内核保证 | ✅ |
| 依赖供应链攻击 | `cargo audit` + `cargo deny` | 🔵 |
| 内存损坏 → 错误定理 | `#[deny(unsafe_code)]` + 审计 | ✅ |
| 栈溢出 → crash | 迭代化 + 深度限制 | ✅ |
| 定理数据库篡改 | SHA-256 签名 (Phase 34+) | 🔵 |

## 定期安全检查

```bash
# 每周运行
cargo audit                              # 漏洞扫描
cargo clippy -- -W clippy::undocumented_unsafe_blocks  # unsafe 审查

# 每月运行
cargo deny check                         # 依赖审计
cargo outdated                           # 过期依赖

# 每季度
# 手动审查所有 unsafe 块
grep -rn "unsafe" src/
# 更新依赖
cargo update
```

## 反模式

| ❌ | ✅ |
|----|----|
| 信任外部输入 | 验证 + 长度限制 + 深度限制 |
| `unsafe` 块无 SAFETY 注释 | 详细文档 |
| 忽略 `cargo audit` 警告 | 及时修复或文档 |
| 依赖未维护的 crate | 评估替代方案 |
| 在 `unsafe` 中执行复杂逻辑 | 最小化 unsafe 表面 |
| 存储明文敏感数据 | 加密或使用 OS 密钥环 |
