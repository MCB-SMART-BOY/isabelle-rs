---
name: build-theory
description: Build/verify .thy files through TheoryProcessor pipeline: parse, compile, debug failures, generate verification reports.
category: theory
version: 2.0.0
triggers: [theory loading, .thy file, parse failure, batch compile, session build]
permissions: [Bash:cargo test, Bash:cargo run, Read]
---

# Build Theory

Build and verify Isabelle `.thy` theory files through the isabelle-rs processing pipeline.

## When to Use

- After modifying theory loader / parser / command processors
- When adding support for a new theory command (datatype, fun, inductive, etc.)
- Debugging a parse failure on a specific `.thy` file
- Running batch verification with statistics

## Architecture

```
.thy file
  → thy_header::parse_header() → TheoryHeader { name, imports }
  → OuterSyntax::parse_spans() → CommandSpan[]
  → TheoryProcessor::process_span()
    ├─ theory → LocalTheory::begin()
    ├─ lemma  → IsarProof::lemma()   [proof mode]
    ├─ datatype/fun/inductive → parse + generate lemmas
    ├─ apply/by → method dispatch (incl. metis, auto, blast, simp)
    ├─ qed → goal refinement
    └─ end → finalize() → Arc<Theory>
  → HolTheoremDb::extend() → by_name, intros, elims, simps, nets
```

## Workflow

### 1. Build a Single File

```bash
# CLI
cargo run --bin isabelle-build -- --file isabelle-source/src/HOL/Nat.thy

# Via test
cargo test test_load_single_file -- --nocapture
```

### 2. Batch Build with Statistics

```bash
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL --stats
# Output: per-file parse time, verify time, theorem count

# Quiet mode
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL --quiet
```

### 3. Run Tiered Verification

```bash
# Tier 0: 5 core files
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture

# Tier 2: 15 files
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture

# Tier 3: 16 files
RUST_MIN_STACK=268435456 cargo test --test tier3_verify -- --nocapture

# One-by-one (for debugging single files)
RUST_MIN_STACK=268435456 cargo test --test one_by_one -- --nocapture
```

### 4. Debug a Parse Failure

```bash
# Enable verbose output to see which command fails
RUST_BACKTRACE=1 cargo test --test single_verify -- --nocapture 2>&1 | head -50

# Common parse failures and checks:
# - "Cannot start ..." → mode assertion failed (Isar state machine)
# - "No equations" → fun/primrec definition missing equations
# - "Failed to parse datatype" → datatype syntax not recognized
# - "No introduction rules" → inductive definition has no intro rules
```

### 5. Verify Classification

```rust
// verify_classifier.rs: VerifyStatus enum
pub enum VerifyStatus {
    OK,           // All lemmas verified
    PARTIAL,      // Some lemmas verified
    SYNTAX,       // Parse error
    TYPE,         // Type error
    PROOF,        // Proof search exhausted
    TIMEOUT,      // Timeout
    NO_LEMMA,     // No lemmas in file
    IO,           // File read error
}
```

## Attribute Pipeline

When debugging why a theorem isn't in the right DB category:

```
.thy: "lemma foo [simp, intro!]: ..."
  → parse_name_attrs() → attrs = ["simp", "intro!"]
  → ParsedLemma { attributes: ["simp", "intro!"] }
  → HolTheoremDb::extend()
  → compute_db_categories(["simp", "intro!"]) → {"simp", "safe_intro"}
  → db.simps.push(), db.safe_intros.push()
```

## Key Files

| File | Role |
|------|------|
| `src/theory/loader.rs` | TheoryProcessor: .thy → commands → theorems |
| `src/theory/session_builder.rs` | Batch compilation + DAG |
| `src/theory/thy_header.rs` | Theory header parsing |
| `src/theory/verify_classifier.rs` | Verification status classification |
| `src/hol/hol_loader.rs` | HolTheoremDb + lemma parsing + attribute pipeline |
| `src/hol/theory_graph.rs` | DAG + topological sort (1,473 nodes) |

## Theory Commands Supported

| Command | Status | Command | Status |
|---------|:------:|---------|:------:|
| theory | ✅ | lemma/theorem | ✅ |
| definition | ✅ | fun/function | ⚠️ |
| inductive/coinductive | ⚠️ | datatype/codatatype | ✅ |
| primrec | ⚠️ | typedef/record | ⚠️ |
| locale | ⚠️ | class/subclass | ⚠️ |
| instance | ⚠️ | interpretation | ⚠️ |

## Related

- `.claude/rules/theory-loading.md` — Theory loading rules
- `.claude/rules/isar.md` — Isar state machine rules
- `.claude/skills/verify.md` — Lemma verification debugging
- `.claude/skills/search-db.md` — Theorem database navigation
