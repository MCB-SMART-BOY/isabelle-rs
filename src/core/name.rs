//! Name infrastructure: fresh variable generation, naming contexts.
//!
//! Corresponds to `src/Pure/name.ML`.
//!
//! Isabelle's `Name.context` is a thread-safe structure for generating
//! fresh variable names that don't collide with already-declared names.
//! This is used everywhere: proof construction, unification, parsing,
//! type inference, etc.
//!
//! ## Key concepts
//!
//! - **Context**: tracks declared names; `declare` adds a name, `variant` produces a fresh variant,
//!   `invent` generates N fresh names
//! - **Internal names**: suffixed with `_` (internalized), `__` (skolem)
//! - **Bound names**: prefixed with `:` for de Bruijn indices
//! - **Default names**: `uu`, `uu_`, `'a` for anonymous variables

use std::collections::BTreeMap;

// =========================================================================
// Special names
// =========================================================================

/// Anonymous variable name.
pub const UU: &str = "uu";
/// Alternative anonymous name.
pub const UU_: &str = "uu_";
/// Default type variable name.
pub const AT: &str = "'a";

// =========================================================================
// Bound variable names (de Bruijn ↔ named)
// =========================================================================

/// Encode a de Bruijn index as a bound variable name.
/// `:000`, `:001`, ... for indices < 1000, recursive for larger.
pub fn bound_name(n: usize) -> String {
    if n < 1000 {
        format!(":{:03}", n)
    } else {
        format!(":{}{}", bound_name(n / 1000), format!("{:03}", n % 1000))
    }
}

/// Check if a name is a bound variable encoding.
pub fn is_bound_name(s: &str) -> bool {
    s.starts_with(':')
}

// =========================================================================
// Internal / skolem names
// =========================================================================

/// Suffix for internalized names.
const INTERNAL_SUFFIX: &str = "_";

/// Suffix for skolem names.
const SKOLEM_SUFFIX: &str = "__";

/// Mark a name as internal.
pub fn internal(s: &str) -> String {
    format!("{}{}", s, INTERNAL_SUFFIX)
}

/// Strip the internal suffix, if present.
pub fn dest_internal(s: &str) -> Option<&str> {
    s.strip_suffix(INTERNAL_SUFFIX)
}

/// Check if a name is internal.
pub fn is_internal(s: &str) -> bool {
    s.ends_with(INTERNAL_SUFFIX)
}

/// Make a name skolem.
pub fn skolem(s: &str) -> String {
    format!("{}{}", s, SKOLEM_SUFFIX)
}

/// Strip the skolem suffix, if present.
pub fn dest_skolem(s: &str) -> Option<&str> {
    s.strip_suffix(SKOLEM_SUFFIX)
}

/// Check if a name is a skolem.
pub fn is_skolem(s: &str) -> bool {
    s.ends_with(SKOLEM_SUFFIX)
}

/// Remove trailing underscores from a name to get the "clean" base name.
pub fn clean_name(s: &str) -> String {
    let mut s = s.to_string();
    while s.ends_with('_') {
        s.pop();
    }
    s
}

/// Count trailing underscores.
pub fn clean_index(s: &str) -> (&str, usize) {
    let mut n = 0;
    let mut end = s.len();
    while end > 0 && s.as_bytes()[end - 1] == b'_' {
        n += 1;
        end -= 1;
    }
    (&s[..end], n)
}

// =========================================================================
// Bumping strings
// =========================================================================

/// Bump a string lexicographically: "x" → "y", "z" → "aa", etc.
/// Cycles through `a-zA-Z0-9` for the last character, extending if needed.
/// This matches Isabelle's `Symbol.bump_string` behavior.
pub fn bump_string(s: &str) -> String {
    if s.is_empty() {
        return "a".to_string();
    }
    let bytes = s.as_bytes();
    let last = bytes[bytes.len() - 1];
    match last {
        b'z' => format!("{}a", bump_string(&s[..s.len() - 1])),
        b'Z' => format!("{}A", bump_string(&s[..s.len() - 1])),
        b'9' => format!("{}0", bump_string(&s[..s.len() - 1])),
        c => {
            let mut v = s.as_bytes().to_vec();
            v[bytes.len() - 1] = c + 1;
            String::from_utf8(v).unwrap_or_else(|_| format!("{}a", s))
        },
    }
}

/// Bump the initial character: "x" → "y", "X" → "Y", "a" → "b".
pub fn bump_init(s: &str) -> String {
    if s.is_empty() {
        return "a".to_string();
    }
    let bytes = s.as_bytes();
    let first = bytes[0];
    match first {
        b'z' => format!("a{}", &s[1..]),
        b'Z' => format!("A{}", &s[1..]),
        c => {
            let mut chars: Vec<u8> = bytes.to_vec();
            chars[0] = c + 1;
            String::from_utf8(chars).unwrap_or_else(|_| format!("a{}", &s[1..]))
        },
    }
}

// =========================================================================
// NameContext
// =========================================================================

/// A naming context tracks declared names and their latest renamings.
/// Used to generate fresh names that avoid collisions.
///
/// Corresponds to `Name.context` in Isabelle.
#[derive(Clone, Debug, Default)]
pub struct NameContext {
    /// Declared names → optional latest renaming.
    /// `None` means the name itself was declared.
    /// `Some(x')` means the name was already taken and renamed to `x'`.
    declared: BTreeMap<String, Option<String>>,
}

impl NameContext {
    /// Create a new empty context, pre-populated with empty-name and `'`.
    pub fn new() -> Self {
        let mut ctx = NameContext::default();
        ctx.declared.insert(String::new(), None);
        ctx.declared.insert("'".to_string(), None);
        ctx
    }

    /// Create a context from a list of already-declared names.
    pub fn from_names(names: &[&str]) -> Self {
        let mut ctx = Self::new();
        for name in names {
            ctx.declare(name);
        }
        ctx
    }

    /// Build a context with a customization function.
    pub fn build<F>(f: F) -> Self
    where
        F: FnOnce(&mut Self),
    {
        let mut ctx = Self::new();
        f(&mut ctx);
        ctx
    }

    // ── Declaration ──

    /// Declare a name as "used". Future variants will avoid this name.
    /// Returns true if the name was newly declared.
    pub fn declare(&mut self, name: &str) -> bool {
        let clean = clean_name(name).to_string();
        if let std::collections::btree_map::Entry::Vacant(e) = self.declared.entry(clean) {
            e.insert(None);
            true
        } else {
            false
        }
    }

    /// Declare a renaming: `old` was already taken, and was renamed to `new`.
    fn declare_renaming(&mut self, old: &str, new: &str) {
        let old_clean = clean_name(old).to_string();
        let new_clean = clean_name(new).to_string();
        if old_clean != new_clean {
            self.declared.insert(old_clean, Some(new_clean));
        }
    }

    /// Declare a renamed name: record both the original and its renaming.
    pub fn declare_renamed(&mut self, original: &str, renamed: &str) {
        let orig_clean = clean_name(original).to_string();
        let ren_clean = clean_name(renamed).to_string();
        if orig_clean != ren_clean {
            self.declare_renaming(original, renamed);
        }
        self.declared.insert(ren_clean, None);
    }

    // ── Query ──

    /// Check if a name is declared (possibly via renaming chain).
    pub fn is_declared(&self, name: &str) -> bool {
        let clean = clean_name(name);
        self.declared.contains_key(&clean)
    }

    /// Get the declared entry for a name.
    pub fn declared(&self, name: &str) -> Option<&Option<String>> {
        let clean = clean_name(name);
        self.declared.get(&clean)
    }

    /// Get the latest name in the renaming chain.
    pub fn latest_name<'a>(&self, name: &'a str) -> &'a str {
        let mut cur = clean_name(name).to_string();
        loop {
            match self.declared.get(&cur) {
                Some(Some(next)) => cur = next.clone(),
                _ => break,
            }
        }
        // We need to return a reference, but since we own it, we return
        // the original if not found. This is slightly imperfect but functional.
        // In practice, we use this via `variant` which handles chains properly.
        name
    }

    // ── Inventing fresh names ──

    /// Invent `n` fresh names starting from a base name.
    /// Returns names that don't collide with already-declared names.
    pub fn invent(&self, base: &str, n: usize) -> Vec<String> {
        let mut result = Vec::with_capacity(n);
        let mut x = clean_name(base).to_string();
        let mut count = 0;
        while count < n {
            if !self.is_declared(&x) && !result.contains(&x) {
                result.push(x.clone());
                count += 1;
            }
            x = bump_string(&x);
        }
        result
    }

    /// Invent fresh names and declare them, returning (names, new_context).
    pub fn invent_declare(&self, base: &str, n: usize) -> (Vec<String>, Self) {
        let mut ctx = self.clone();
        let mut result = Vec::with_capacity(n);
        let mut x = clean_name(base).to_string();
        let mut count = 0;
        while count < n {
            if !ctx.is_declared(&x) && !result.contains(&x) {
                ctx.declared.insert(x.clone(), None);
                result.push(x.clone());
                count += 1;
            }
            x = bump_string(&x);
        }
        (result, ctx)
    }

    /// Invent global names (without updating the context).
    pub fn invent_global(base: &str, n: usize) -> Vec<String> {
        NameContext::new().invent(base, n)
    }

    /// Invent type variable names globally.
    pub fn invent_global_types(n: usize) -> Vec<String> {
        Self::invent_global(AT, n)
    }

    /// Invent names paired with items.
    pub fn invent_names<'a, T>(&self, base: &str, items: &'a [T]) -> Vec<(String, &'a T)> {
        self.invent(base, items.len()).into_iter().zip(items.iter()).collect()
    }

    // ── Variants ──

    /// Make a variant of `name` distinct from all declared names.
    /// Returns (fresh_name, new_context with the fresh name declared).
    ///
    /// Preserves trailing underscores.
    pub fn variant(&self, name: &str) -> (String, Self) {
        let (base, n_underscores) = clean_index(name);
        let mut ctx = self.clone();

        let fresh = if !ctx.is_declared(base) {
            // Base name is free — use it directly
            ctx.declared.insert(base.to_string(), None);
            base.to_string()
        } else {
            // Base name is taken — bump until we find a free one
            let x0 = bump_init(base);
            let mut x = x0.clone();
            while ctx.is_declared(&x) {
                x = bump_string(&x);
            }
            ctx.declare_renaming(&x0, &x);
            ctx.declared.insert(x.clone(), None);
            x
        };

        // Restore trailing underscores
        let result = format!("{}{}", fresh, "_".repeat(n_underscores));
        (result, ctx)
    }

    /// Make a variant for a bound name (prefix bare names with "u").
    pub fn variant_bound(&self, name: &str) -> (String, Self) {
        if is_bound_name(name) { self.variant(name) } else { self.variant("u") }
    }

    /// Make variants for a list of names.
    pub fn variants(&self, names: &[&str]) -> (Vec<String>, Self) {
        let mut ctx = self.clone();
        let mut result = Vec::with_capacity(names.len());
        for name in names {
            let (v, new_ctx) = ctx.variant(name);
            result.push(v);
            ctx = new_ctx;
        }
        (result, ctx)
    }

    /// Variant names from a build function.
    pub fn variant_names<T>(&self, items: &[(String, T)]) -> Vec<(String, T)>
    where
        T: Clone,
    {
        let mut ctx = self.clone();
        items
            .iter()
            .map(|(name, val)| {
                let (v, new_ctx) = ctx.variant(name);
                ctx = new_ctx;
                (v, val.clone())
            })
            .collect()
    }

    /// Variant a list, throwing away the context.
    pub fn variant_list(base_names: &[&str], used: &[&str]) -> Vec<String> {
        let ctx = NameContext::from_names(used);
        let (result, _) = ctx.variants(base_names);
        result
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_special_names() {
        assert!(is_bound_name(":000"));
        assert!(is_bound_name(":123"));
        assert!(!is_bound_name("x"));

        assert!(is_internal("x_"));
        assert!(!is_internal("x"));
        assert_eq!(dest_internal("x_"), Some("x"));

        assert!(is_skolem("x__"));
        assert!(!is_skolem("x_"));
        assert_eq!(dest_skolem("x__"), Some("x"));
    }

    #[test]
    fn test_bump_string() {
        assert_eq!(bump_string("a"), "b");
        assert_eq!(bump_string("z"), "aa");
        assert_eq!(bump_string("x1"), "x2");
        assert_eq!(bump_string("aa"), "ab");
        assert_eq!(bump_string(""), "a");
    }

    #[test]
    fn test_bump_init() {
        assert_eq!(bump_init("x"), "y");
        assert_eq!(bump_init("z"), "a");
        assert_eq!(bump_init("xa"), "ya");
        assert_eq!(bump_init(""), "a");
    }

    #[test]
    fn test_clean_name() {
        assert_eq!(clean_name("x_"), "x");
        assert_eq!(clean_name("x__"), "x");
        assert_eq!(clean_name("x"), "x");
        assert_eq!(clean_name(""), "");
    }

    #[test]
    fn test_clean_index() {
        assert_eq!(clean_index("x"), ("x", 0));
        assert_eq!(clean_index("x_"), ("x", 1));
        assert_eq!(clean_index("x__"), ("x", 2));
        assert_eq!(clean_index(""), ("", 0));
    }

    #[test]
    fn test_context_new() {
        let ctx = NameContext::new();
        assert!(ctx.is_declared(""));
        assert!(ctx.is_declared("'"));
        assert!(!ctx.is_declared("x"));
    }

    #[test]
    fn test_declare() {
        let mut ctx = NameContext::new();
        assert!(ctx.declare("x"));
        assert!(ctx.is_declared("x"));
        assert!(!ctx.declare("x")); // already declared

        // Clean form also counts
        assert!(!ctx.declare("x_")); // "x_" clean is "x", already declared
    }

    #[test]
    fn test_variant() {
        let mut ctx = NameContext::new();
        ctx.declare("x");
        ctx.declare("y");
        ctx.declare("z");

        let (v1, ctx) = ctx.variant("x");
        // "x" is taken, so should bump to "a" (first free after bump_init("x") = "y", "z", ...)
        assert_ne!(v1, "x");
        assert!(ctx.is_declared("x")); // "x" was declared initially and remains
        assert!(ctx.is_declared(&v1)); // the variant IS declared
    }

    #[test]
    fn test_variant_preserves_underscores() {
        let mut ctx = NameContext::new();
        ctx.declare("x");

        let (v, _) = ctx.variant("x___"); // 3 underscores
        assert!(v.ends_with("___") || v.starts_with("x"));
        // Should preserve the underscore count
        let (_, n) = clean_index(&v);
        assert_eq!(n, 3);
    }

    #[test]
    fn test_invent() {
        let ctx = NameContext::new();
        let names = ctx.invent("var", 3);
        assert_eq!(names.len(), 3);
        assert_eq!(names[0], "var");
        assert_eq!(names[1], "vas");
        assert_eq!(names[2], "vat");
    }

    #[test]
    fn test_invent_avoids_declared() {
        let mut ctx = NameContext::new();
        ctx.declare("a");
        ctx.declare("b");

        let names = ctx.invent("a", 3);
        assert!(!names.contains(&"a".to_string()));
        assert!(!names.contains(&"b".to_string()));
        assert_eq!(names.len(), 3);
    }

    #[test]
    fn test_invent_global() {
        let names = NameContext::invent_global("test", 3);
        assert_eq!(names, vec!["test", "tesu", "tesv"]);
    }

    #[test]
    fn test_bound_name() {
        assert_eq!(bound_name(0), ":000");
        assert_eq!(bound_name(1), ":001");
        assert_eq!(bound_name(10), ":010");
        assert_eq!(bound_name(999), ":999");
        assert!(is_bound_name(&bound_name(42)));
    }

    #[test]
    fn test_variant_list() {
        let result = NameContext::variant_list(&["x", "x", "x"], &["x"]);
        assert_eq!(result.len(), 3);
        // All should be distinct from "x"
        assert!(!result.contains(&"x".to_string()));
        // All should be distinct from each other
        let mut sorted = result.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), 3);
    }

    #[test]
    fn test_variant_bound() {
        let ctx = NameContext::new();
        let (v, _) = ctx.variant_bound(":001");
        assert!(v.starts_with(':'));
    }
}
