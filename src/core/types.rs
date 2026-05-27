//! Isabelle type system: sorts, type classes, type expressions.
//! Corresponds to src/Pure/type.ML, src/Pure/sorts.ML.
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::sync::Arc;

thread_local! { static IT: RefCell<HashMap<String, Arc<str>>> = RefCell::new(HashMap::new()); }

pub fn intern(s: &str) -> Arc<str> {
    IT.with(|t| {
        let mut t = t.borrow_mut();
        if let Some(e) = t.get(s) {
            Arc::clone(e)
        } else {
            let a: Arc<str> = Arc::from(s);
            t.insert(s.to_string(), Arc::clone(&a));
            a
        }
    })
}

/// Symbol — interned name. Currently an alias for Arc<str>.
pub type Symbol = Arc<str>;
pub type Class = Symbol; // Symbol alias

#[derive(Clone, Debug, Default)]
pub struct ClassAlgebra {
    sub_classes: HashMap<Class, Vec<Class>>,
}

impl ClassAlgebra {
    pub fn empty() -> Self {
        ClassAlgebra {
            sub_classes: HashMap::new(),
        }
    }
    pub fn add_classrel(&mut self, sub: impl Into<Arc<str>>, sup: impl Into<Arc<str>>) {
        self.sub_classes
            .entry(sub.into())
            .or_default()
            .push(sup.into());
    }
    pub fn is_subclass(&self, sub: &Class, sup: &Class) -> bool {
        if Arc::ptr_eq(sub, sup) {
            return true;
        }
        let mut seen = BTreeSet::new();
        let mut stack: Vec<&str> = vec![sub.as_ref()];
        while let Some(cur) = stack.pop() {
            if cur == sup.as_ref() {
                return true;
            }
            if !seen.insert(cur) {
                continue;
            }
            if let Some(supers) = self.sub_classes.get(cur) {
                for s in supers {
                    stack.push(s.as_ref());
                }
            }
        }
        false
    }
    pub fn sort_le(&self, s1: &Sort, s2: &Sort) -> bool {
        s1.classes
            .iter()
            .all(|c1| s2.classes.iter().any(|c2| self.is_subclass(c1, c2)))
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Sort {
    classes: BTreeSet<Class>,
}

impl Sort {
    pub const EMPTY: Sort = Sort {
        classes: BTreeSet::new(),
    };
    pub fn new(classes: impl IntoIterator<Item = Class>) -> Self {
        Sort {
            classes: classes.into_iter().collect(),
        }
    }
    pub fn singleton(class: &str) -> Self {
        Sort::new(std::iter::once(Arc::from(class)))
    }
    pub fn top() -> Self {
        Sort::singleton("type")
    }
    pub fn has(&self, class: &str) -> bool {
        self.classes.iter().any(|c| c.as_ref() == class)
    }
    pub fn is_subset_of(&self, other: &Sort) -> bool {
        self.classes.is_subset(&other.classes)
    }
    pub fn len(&self) -> usize {
        self.classes.len()
    }
    pub fn is_empty(&self) -> bool {
        self.classes.is_empty()
    }
    pub fn iter(&self) -> impl Iterator<Item = &Class> {
        self.classes.iter()
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cs: Vec<&str> = self.classes.iter().map(|c| c.as_ref()).collect();
        write!(f, "{{{}}}", cs.join(", "))
    }
}
impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Typ {
    Type {
        name: Arc<str>,
        args: Vec<Typ>,
    },
    TFree {
        name: Arc<str>,
        sort: Sort,
    },
    TVar {
        name: Arc<str>,
        index: usize,
        sort: Sort,
    },
}

impl Typ {
    pub fn base(name: impl Into<Arc<str>>) -> Self {
        Typ::Type {
            name: name.into(),
            args: vec![],
        }
    }
    pub fn apply(name: impl Into<Arc<str>>, args: Vec<Typ>) -> Self {
        Typ::Type {
            name: name.into(),
            args,
        }
    }
    pub fn free(name: impl Into<Arc<str>>, sort: Sort) -> Self {
        Typ::TFree {
            name: name.into(),
            sort,
        }
    }
    pub fn var(name: impl Into<Arc<str>>, index: usize, sort: Sort) -> Self {
        Typ::TVar {
            name: name.into(),
            index,
            sort,
        }
    }
    pub fn arrow(from: Typ, to: Typ) -> Self {
        Typ::apply("fun", vec![from, to])
    }
    pub fn arrows(from: Vec<Typ>, to: Typ) -> Self {
        from.into_iter().rfold(to, |acc, t| Typ::arrow(t, acc))
    }
    pub fn dummy() -> Self {
        Typ::base("dummy")
    }
    pub fn is_type(&self) -> bool {
        matches!(self, Typ::Type { .. })
    }
    pub fn is_tfree(&self) -> bool {
        matches!(self, Typ::TFree { .. })
    }
    pub fn is_tvar(&self) -> bool {
        matches!(self, Typ::TVar { .. })
    }
    pub fn dest_fun(&self) -> Option<(&Typ, &Typ)> {
        match self {
            Typ::Type { name, args } if name.as_ref() == "fun" && args.len() == 2 => {
                Some((&args[0], &args[1]))
            }
            _ => None,
        }
    }
    pub fn is_dummy(&self) -> bool {
        matches!(self, Typ::Type { name, args } if name.as_ref() == "dummy" && args.is_empty())
    }
    pub fn maxidx(&self) -> usize {
        match self {
            Typ::TVar { index, .. } => *index,
            Typ::Type { args, .. } => args.iter().map(|t| t.maxidx()).max().unwrap_or(0),
            _ => 0,
        }
    }
}

impl fmt::Display for Typ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Typ::Type { name, args } if args.is_empty() => write!(f, "{name}"),
            Typ::Type { name, args } if name.as_ref() == "fun" && args.len() == 2 => {
                write!(f, "({:?} => {:?})", args[0], args[1])
            }
            Typ::Type { name, .. } => write!(f, "{name}"),
            Typ::TFree { name, .. } => write!(f, "'{name}"),
            Typ::TVar { name, index, .. } => write!(f, "?'{name}.{index}"),
        }
    }
}

// =========================================================================
// TypeEnv — type signature registry
// =========================================================================

/// Registry of type information for constants and type constructors.
/// Maps constant names to their type signatures, and type constructor names
/// to their arities (number of type arguments).
#[derive(Clone, Debug, Default)]
pub struct TypeEnv {
    /// Constant name → type signature (e.g., "HOL.eq" → 'a => 'a => bool)
    pub consts: HashMap<String, Typ>,
    /// Type constructor name → arity (e.g., "list" → 1, "fun" → 2)
    pub types: HashMap<String, usize>,
    /// Free variable name → declared type
    pub frees: HashMap<String, Typ>,
}

impl TypeEnv {
    pub fn new() -> Self {
        let mut env = TypeEnv::default();
        // Built-in: Pure logic types
        env.types.insert("prop".into(), 0);
        env.types.insert("fun".into(), 2);
        env.types.insert("bool".into(), 0);
        // Built-in: Pure constants
        env.consts.insert(
            "Pure.all".into(),
            Typ::arrow(
                Typ::arrow(Typ::free("'a", Sort::top()), Typ::base("prop")),
                Typ::base("prop"),
            ),
        );
        env.consts.insert(
            "Pure.imp".into(),
            Typ::arrows(vec![Typ::base("prop"), Typ::base("prop")], Typ::base("prop")),
        );
        env.consts.insert(
            "Pure.eq".into(),
            Typ::arrows(
                vec![Typ::free("'a", Sort::top()), Typ::free("'a", Sort::top())],
                Typ::base("prop"),
            ),
        );
        env
    }

    /// Declare a type constructor with its arity.
    pub fn declare_type(&mut self, name: &str, arity: usize) {
        self.types.insert(name.to_string(), arity);
    }

    /// Declare a constant with its type signature.
    pub fn declare_const(&mut self, name: &str, typ: Typ) {
        self.consts.insert(name.to_string(), typ);
    }

    /// Declare a free variable with its type.
    pub fn declare_free(&mut self, name: &str, typ: Typ) {
        self.frees.insert(name.to_string(), typ);
    }

    /// Get the type signature of a constant.
    pub fn const_type(&self, name: &str) -> Option<&Typ> {
        self.consts.get(name)
    }

    /// Get the arity of a type constructor.
    pub fn type_arity(&self, name: &str) -> Option<usize> {
        self.types.get(name).copied()
    }

    /// Look up a constant type, with fallback to common names.
    pub fn lookup_const(&self, name: &str) -> Option<&Typ> {
        self.consts.get(name).or_else(|| {
            // Try without prefix (e.g., "eq" → "HOL.eq")
            if !name.contains('.') {
                self.consts.get(&format!("HOL.{}", name))
            } else {
                None
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_env_builtins() {
        let env = TypeEnv::new();
        assert_eq!(env.type_arity("fun"), Some(2));
        assert_eq!(env.type_arity("bool"), Some(0));
        assert_eq!(env.type_arity("prop"), Some(0));
        assert!(env.const_type("Pure.imp").is_some());
        assert!(env.const_type("Pure.eq").is_some());
        assert!(env.const_type("Pure.all").is_some());
    }

    #[test]
    fn test_type_env_declare() {
        let mut env = TypeEnv::new();
        env.declare_type("list", 1);
        env.declare_type("set", 1);
        assert_eq!(env.type_arity("list"), Some(1));
        assert_eq!(env.type_arity("set"), Some(1));
        assert_eq!(env.type_arity("nonexistent"), None);

        env.declare_const("HOL.eq", Typ::arrows(
            vec![Typ::free("'a", Sort::top()), Typ::free("'a", Sort::top())],
            Typ::base("bool"),
        ));
        assert!(env.const_type("HOL.eq").is_some());
        assert!(env.lookup_const("eq").is_some()); // fallback lookup
    }

    #[test]
    #[test]
    fn test_sort() {
        let s = Sort::singleton("type");
        assert!(s.has("type"));
    }
    #[test]
    fn test_types() {
        let b = Typ::base("bool");
        assert!(b.is_type());
    }
}
