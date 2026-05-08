//! Isabelle type system: sorts, type classes, type expressions.
//! Corresponds to src/Pure/type.ML, src/Pure/sorts.ML.
use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::sync::Arc;

/// Symbol — interned name. Currently an alias for Arc<str>.
/// Will become u32 after thread_local! interning is activated.
pub type Symbol = Arc<str>;
pub type Class = Symbol;  // Symbol alias


#[derive(Clone, Debug, Default)]
pub struct ClassAlgebra { sub_classes: HashMap<Class, Vec<Class>> }

impl ClassAlgebra {
    pub fn empty() -> Self { ClassAlgebra { sub_classes: HashMap::new() } }
    pub fn add_classrel(&mut self, sub: impl Into<Arc<str>>, sup: impl Into<Arc<str>>) {
        self.sub_classes.entry(sub.into()).or_default().push(sup.into());
    }
    pub fn is_subclass(&self, sub: &Class, sup: &Class) -> bool {
        if Arc::ptr_eq(sub, sup) { return true; }
        let mut seen = BTreeSet::new();
        let mut stack: Vec<&str> = vec![sub.as_ref()];
        while let Some(cur) = stack.pop() {
            if cur == sup.as_ref() { return true; }
            if !seen.insert(cur) { continue; }
            if let Some(supers) = self.sub_classes.get(cur) {
                for s in supers { stack.push(s.as_ref()); }
            }
        }
        false
    }
    pub fn sort_le(&self, s1: &Sort, s2: &Sort) -> bool {
        s1.classes.iter().all(|c1| s2.classes.iter().any(|c2| self.is_subclass(c1, c2)))
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Sort { classes: BTreeSet<Class> }

impl Sort {
    pub const EMPTY: Sort = Sort { classes: BTreeSet::new() };
    pub fn new(classes: impl IntoIterator<Item = Class>) -> Self { Sort { classes: classes.into_iter().collect() } }
    pub fn singleton(class: &str) -> Self { Sort::new(std::iter::once(Arc::from(class))) }
    pub fn top() -> Self { Sort::singleton("type") }
    pub fn has(&self, class: &str) -> bool { self.classes.iter().any(|c| c.as_ref() == class) }
    pub fn is_subset_of(&self, other: &Sort) -> bool { self.classes.is_subset(&other.classes) }
    pub fn len(&self) -> usize { self.classes.len() }
    pub fn is_empty(&self) -> bool { self.classes.is_empty() }
    pub fn iter(&self) -> impl Iterator<Item = &Class> { self.classes.iter() }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cs: Vec<&str> = self.classes.iter().map(|c| c.as_ref()).collect();
        write!(f, "{{{}}}", cs.join(", "))
    }
}
impl fmt::Display for Sort { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{:?}", self) } }

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Typ {
    Type { name: Arc<str>, args: Vec<Typ> },
    TFree { name: Arc<str>, sort: Sort },
    TVar  { name: Arc<str>, index: usize, sort: Sort },
}

impl Typ {
    pub fn base(name: impl Into<Arc<str>>) -> Self { Typ::Type { name: name.into(), args: vec![] } }
    pub fn apply(name: impl Into<Arc<str>>, args: Vec<Typ>) -> Self { Typ::Type { name: name.into(), args } }
    pub fn free(name: impl Into<Arc<str>>, sort: Sort) -> Self { Typ::TFree { name: name.into(), sort } }
    pub fn var(name: impl Into<Arc<str>>, index: usize, sort: Sort) -> Self { Typ::TVar { name: name.into(), index, sort } }
    pub fn arrow(from: Typ, to: Typ) -> Self { Typ::apply("fun", vec![from, to]) }
    pub fn arrows(from: Vec<Typ>, to: Typ) -> Self { from.into_iter().rfold(to, |acc, t| Typ::arrow(t, acc)) }
    pub fn dummy() -> Self { Typ::base("dummy") }
    pub fn is_type(&self) -> bool { matches!(self, Typ::Type { .. }) }
    pub fn is_tfree(&self) -> bool { matches!(self, Typ::TFree { .. }) }
    pub fn is_tvar(&self) -> bool { matches!(self, Typ::TVar { .. }) }
    pub fn dest_fun(&self) -> Option<(&Typ, &Typ)> {
        match self { Typ::Type { name, args } if name.as_ref() == "fun" && args.len() == 2 => Some((&args[0], &args[1])), _ => None }
    }
    pub fn is_dummy(&self) -> bool { matches!(self, Typ::Type { name, args } if name.as_ref() == "dummy" && args.is_empty()) }
    pub fn maxidx(&self) -> usize {
        match self { Typ::TVar { index, .. } => *index, Typ::Type { args, .. } => args.iter().map(|t| t.maxidx()).max().unwrap_or(0), _ => 0 }
    }
}

impl fmt::Display for Typ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Typ::Type { name, args } if args.is_empty() => write!(f, "{name}"),
            Typ::Type { name, args } if name.as_ref() == "fun" && args.len() == 2 => write!(f, "({:?} => {:?})", args[0], args[1]),
            Typ::Type { name, .. } => write!(f, "{name}"),
            Typ::TFree { name, .. } => write!(f, "'{name}"),
            Typ::TVar { name, index, .. } => write!(f, "?'{name}.{index}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn test_sort() { let s = Sort::singleton("type"); assert!(s.has("type")); }
    #[test] fn test_types() { let b = Typ::base("bool"); assert!(b.is_type()); }
}
