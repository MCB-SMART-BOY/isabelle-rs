use std::collections::HashMap;
use std::sync::Arc;
use std::cell::RefCell;

thread_local! {
    static TLS_SYMBOLS: RefCell<SymbolTable> = RefCell::new(SymbolTable::new());
}

pub fn intern(s: &str) -> Symbol {
    TLS_SYMBOLS.with(|syms| syms.borrow_mut().intern(s))
}

pub fn lookup_str(sym: Symbol) -> Option<Arc<str>> {
    TLS_SYMBOLS.with(|syms| {
        let syms = syms.borrow();
        if (sym.0 as usize) < syms.len() { Some(Arc::clone(syms.lookup(sym))) } else { None }
    })
}

pub fn with_symbols<F, R>(f: F) -> R where F: FnOnce(&SymbolTable) -> R {
    TLS_SYMBOLS.with(|syms| f(&syms.borrow()))
}

// Global Arena — the memory backbone of V3.
//
// All terms, types, symbols and theorems are stored in Arenas.
// This eliminates Box/Arc clone overhead and enables O(1) comparison.
//
// ## Design
//
// - `TermId = u32` — index into `TermArena`
// - `TypeId = u32` — index into `TypeArena`
// - `Symbol = u32` — index into `SymbolTable`
// - `ThmId = u32` — index into `ThmArena`
//
// ## GC Strategy
//
// Each FileWorker gets a version number. When a file closes, all
// allocations for that version are bulk-recycled via `gc(version)`.

// =========================================================================
// SymbolTable — global string interning
// =========================================================================

/// A symbol is a u32 index into the global string table.
/// Two Symbols are equal iff they point to the same string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(u32);

/// Global string interning table.
pub struct SymbolTable {
    strings: Vec<Arc<str>>,
    map: HashMap<Arc<str>, Symbol>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable { strings: Vec::new(), map: HashMap::new() }
    }

    /// Intern a string: returns existing Symbol or creates new one.
    pub fn intern(&mut self, s: &str) -> Symbol {
        if let Some(&sym) = self.map.get(s) {
            return sym;
        }
        let arc: Arc<str> = Arc::from(s);
        let sym = Symbol(self.strings.len() as u32);
        self.map.insert(Arc::clone(&arc), sym);
        self.strings.push(arc);
        sym
    }

    /// Look up the string for a Symbol.
    pub fn lookup(&self, sym: Symbol) -> &Arc<str> {
        &self.strings[sym.0 as usize]
    }

    /// Number of interned strings.
    pub fn len(&self) -> usize { self.strings.len() }

    /// Get a reference to the string (for Debug/Display).
    pub fn get(&self, sym: Symbol) -> &str {
        self.strings.get(sym.0 as usize).map(|s| { s.as_ref() }).unwrap_or("?")
    }
}

// =========================================================================
// TypeArena
// =========================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(u32);

pub struct TypeArena {
    nodes: Vec<TypeNode>,
}

#[derive(Debug, Clone)]
pub enum TypeNode {
    Type {
        name: Symbol,
        args: Vec<TypeId>,
    },
    TFree {
        name: Symbol,
        sort: SortRef,
    },
    TVar {
        name: Symbol,
        index: u32,
        sort: SortRef,
    },
}

/// Sort = set of class Symbols.
/// For now we keep a simplified version; full algebra comes later.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SortRef {
    classes: Vec<Symbol>,
}

impl Default for TypeArena {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeArena {
    pub fn new() -> Self { TypeArena { nodes: Vec::new() } }

    pub fn alloc(&mut self, node: TypeNode) -> TypeId {
        let id = TypeId(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }

    pub fn get(&self, id: TypeId) -> &TypeNode {
        &self.nodes[id.0 as usize]
    }

    pub fn len(&self) -> usize { self.nodes.len() }
}

// =========================================================================
// TermArena
// =========================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermId(u32);

pub struct TermArena {
    nodes: Vec<TermNode>,
}

#[derive(Debug, Clone)]
pub enum TermNode {
    Const { name: Symbol, typ: TypeId },
    Free  { name: Symbol, typ: TypeId },
    Var   { name: Symbol, index: u32, typ: TypeId },
    Bound(u32),
    Abs   { name: Symbol, typ: TypeId, body: TermId },
    App   { func: TermId, arg: TermId },
}

impl Default for TermArena {
    fn default() -> Self {
        Self::new()
    }
}

impl TermArena {
    pub fn new() -> Self { TermArena { nodes: Vec::new() } }

    pub fn alloc(&mut self, node: TermNode) -> TermId {
        let id = TermId(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }

    pub fn get(&self, id: TermId) -> &TermNode {
        &self.nodes[id.0 as usize]
    }

    pub fn eq(&self, a: TermId, b: TermId) -> bool {
        if a == b { return true; }
        // Full structural equality (fallback when IDs differ)
        self.structural_eq(a, b)
    }

    fn structural_eq(&self, a: TermId, b: TermId) -> bool {
        match (self.get(a), self.get(b)) {
            (TermNode::Const { name: n1, typ: t1 }, TermNode::Const { name: n2, typ: t2 }) =>
                n1 == n2 && t1 == t2,
            (TermNode::Free { name: n1, typ: t1 }, TermNode::Free { name: n2, typ: t2 }) =>
                n1 == n2 && t1 == t2,
            (TermNode::Var { name: n1, index: i1, typ: t1 }, TermNode::Var { name: n2, index: i2, typ: t2 }) =>
                n1 == n2 && i1 == i2 && t1 == t2,
            (TermNode::Bound(i1), TermNode::Bound(i2)) => i1 == i2,
            (TermNode::Abs { name: n1, typ: t1, body: b1 }, TermNode::Abs { name: n2, typ: t2, body: b2 }) =>
                n1 == n2 && t1 == t2 && self.structural_eq(*b1, *b2),
            (TermNode::App { func: f1, arg: a1 }, TermNode::App { func: f2, arg: a2 }) =>
                self.structural_eq(*f1, *f2) && self.structural_eq(*a1, *a2),
            _ => false,
        }
    }

    pub fn len(&self) -> usize { self.nodes.len() }
}

// =========================================================================
// GlobalArena — bundles all sub-arenas
// =========================================================================

pub struct GlobalArena {
    pub symbols: SymbolTable,
    pub types: TypeArena,
    pub terms: TermArena,
    /// Version counter for GC
    next_version: u64,
}

impl Default for GlobalArena {
    fn default() -> Self {
        Self::new()
    }
}

impl GlobalArena {
    pub fn new() -> Self {
        GlobalArena {
            symbols: SymbolTable::new(),
            types: TypeArena::new(),
            terms: TermArena::new(),
            next_version: 0,
        }
    }

    /// Allocate a new version (for a new FileWorker).
    pub fn new_version(&mut self) -> u64 {
        self.next_version += 1;
        self.next_version
    }

    /// Intern a string → Symbol.
    pub fn intern(&mut self, s: &str) -> Symbol {
        self.symbols.intern(s)
    }

    /// Allocate a type → TypeId.
    pub fn alloc_type(&mut self, node: TypeNode) -> TypeId {
        self.types.alloc(node)
    }

    /// Allocate a term → TermId.
    pub fn alloc_term(&mut self, node: TermNode) -> TermId {
        self.terms.alloc(node)
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_intern() {
        let mut syms = SymbolTable::new();
        let a = syms.intern("foo");
        let b = syms.intern("foo");
        assert_eq!(a, b);
        assert_eq!(syms.lookup(a).as_ref(), "foo");
        let c = syms.intern("bar");
        assert_ne!(a, c);
    }

    #[test]
    fn test_term_arena() {
        let mut arena = TermArena::new();
        let sym = Symbol(0); // placeholder
        let typ = TypeId(0); // placeholder
        let t1 = arena.alloc(TermNode::Const { name: sym, typ });
        let t2 = arena.alloc(TermNode::Const { name: sym, typ });
        // Different allocations have different IDs
        assert_ne!(t1, t2);
        // But structural equality says they're the same
        assert!(arena.eq(t1, t2));
    }

    #[test]
    fn test_term_arena_structural() {
        let mut arena = TermArena::new();
        let sym = Symbol(0);
        let typ = TypeId(0);
        let f = arena.alloc(TermNode::Free { name: sym, typ });
        let a = arena.alloc(TermNode::Free { name: sym, typ });
        let app1 = arena.alloc(TermNode::App { func: f, arg: a });
        let app2 = arena.alloc(TermNode::App { func: f, arg: a });
        assert!(arena.eq(app1, app2));
    }
}
