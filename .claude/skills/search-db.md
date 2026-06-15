---
name: search-db
description: Quick reference for navigating the HolTheoremDb (42K+ theorems): by name, type convention, net pattern, or attribute category.
category: theory
version: 2.0.0
triggers: [find theorem, lookup rule, search database, theorem by name]
permissions: [Read, Grep]
---

# Search Theorem DB

Quick reference for navigating the 42,000+ theorem database.

## Lookup Methods

### By Name (fastest)
```rust
let db = HolTheoremDb::get();
db.by_name.get("Nat.add_commute")     // exact
db.by_name.get("list.induct")         // type convention
```

### By Type Convention
```rust
// Standard naming: {type}.{kind}
format!("{type}.induct")     // "Nat.induct"
format!("{type}.cases")      // "List.cases"
format!("{type}.exhaust")    // "Bool.exhaust"
format!("{type}.simps")      // "List.simps"
format!("{type}.rec")        // "Nat.rec"
format!("{type}.distinct")   // "Option.distinct"
format!("{type}.inject")     // "Option.inject"
format!("{type}.split")      // "Product.split"
format!("{type}.map")        // "List.map"
format!("{type}.set")        // "List.set"
format!("{type}.rel")        // "List.rel"
format!("{type}.pred")       // "List.pred"
```

### By Net Pattern
```rust
// Find rules whose conclusion matches a pattern
let candidates = db.intro_net().lookup(&subgoal);
let safe = db.safe_intro_net().lookup(&subgoal);
let elims = db.elim_net().lookup(&major_premise);
let safe_elims = db.safe_elim_net().lookup(&major_premise);
```

### By Attribute Category
```rust
db.simps      // [simp] rules
db.intros     // [intro] rules
db.elims      // [elim] rules
db.safe_intros // [intro!] rules
db.safe_elims  // [elim!] rules
```

## DB Architecture
```
HolTheoremDb
├── by_name: HashMap<String, Arc<Thm>>     // exact lookup
├── all: Vec<Arc<Thm>>                     // every theorem
├── intros / elims / simps                 // categorized
├── safe_intros / safe_elims               // [intro!] / [elim!]
├── intro_net / elim_net (OnceLock)        // lazy prefix trie
├── safe_intro_net / safe_elim_net (OnceLock)
└── def_index: HashMap<String, DefLocation> // go-to-definition
```

## Debugging "Rule Not Found"

1. `db.by_name.get("name")` — check name exists
2. Check attribute: `[intro!]` → `safe_intros`, `[intro]` → `intros`
3. Check net: `db.intro_net().lookup(&term)` — pattern matches?
4. Check classification: `compute_db_categories(attrs, name, is_eq)`

## Related

- `.claude/skills/build-theory.md` — Theory building
- `.claude/skills/verify.md` — Verification debugging
- `src/hol/hol_loader.rs:2218-2430` — `HolTheoremDb` definition + `extend()`
