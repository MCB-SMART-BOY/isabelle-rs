use std::{collections::BTreeMap, fmt};

use super::{KernelError, Name, identity::CanonicalEncoder};

/// A type-class sort for type variables.
///
/// For the initial implementation, a sort is a single class name (e.g., `type`).
/// Isabelle's full sort system (intersection/normalization of classes) can be
/// added later without changing the `TyKind` variant structure.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sort(Name);

impl Sort {
    pub fn typ() -> Self {
        Sort(Name::from("type"))
    }

    pub fn name(&self) -> &Name {
        &self.0
    }
}

#[cfg(test)]
impl Sort {
    pub fn arbitrary(name: &str) -> Self {
        Sort(Name::from(name))
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TyKind {
    Type { name: Name, args: Vec<Ty> },
    TypeVar { name: Name, index: usize, sort: Sort },
}

/// Strict kernel type.
///
/// There is deliberately no `dummy` constructor. The reserved name `dummy` is
/// rejected by public constructors so compatibility uncertainty cannot enter
/// the new TCB as a normal type.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ty(TyKind);

impl Ty {
    pub fn base(name: impl Into<Name>) -> Result<Self, KernelError> {
        Self::apply(name, vec![])
    }

    pub fn apply(name: impl Into<Name>, args: Vec<Ty>) -> Result<Self, KernelError> {
        let name = name.into();
        if name.as_str() == "dummy" {
            return Err(KernelError::ReservedDummyType);
        }
        if name.as_str().starts_with('\'') {
            return Err(KernelError::Invariant(
                format!("tick-prefixed names are reserved for type variables, got '{name}'").into(),
            ));
        }
        Ok(Ty(TyKind::Type { name, args }))
    }

    pub fn tvar(name: impl Into<Name>, index: usize, sort: Sort) -> Self {
        Ty(TyKind::TypeVar { name: name.into(), index, sort })
    }

    pub fn is_tvar(&self) -> bool {
        matches!(&self.0, TyKind::TypeVar { .. })
    }

    pub fn is_concrete_type(&self) -> bool {
        match &self.0 {
            TyKind::TypeVar { .. } => false,
            TyKind::Type { args, .. } => args.iter().all(Self::is_concrete_type),
        }
    }

    pub fn tvar_name(&self) -> Option<&Name> {
        match &self.0 {
            TyKind::TypeVar { name, .. } => Some(name),
            _ => None,
        }
    }

    /// Call `f` for every type variable leaf in this type.
    pub fn for_each_type_var(&self, f: &mut impl FnMut(&Name, usize, &Sort)) {
        match &self.0 {
            TyKind::TypeVar { name, index, sort } => f(name, *index, sort),
            TyKind::Type { args, .. } => {
                for arg in args {
                    arg.for_each_type_var(f);
                }
            },
        }
    }

    pub fn has_type_vars(&self) -> bool {
        let mut found = false;
        self.for_each_type_var(&mut |_, _, _| found = true);
        found
    }

    /// Apply a type-variable substitution. Only TypeVar leaves are replaced.
    pub(crate) fn subst_type_vars(
        &self,
        inst: &crate::logic::TypeInstantiation,
    ) -> Result<Ty, KernelError> {
        match &self.0 {
            TyKind::TypeVar { name, index, sort } => {
                if sort != &Sort::typ() {
                    return Err(KernelError::Invariant(
                        format!("unsupported sort `{sort:?}` in type variable `{name}`").into(),
                    ));
                }
                let id = crate::logic::TypeVarId::new(name.clone(), *index as u32);
                if let Some(replacement) = inst.get(&id) {
                    return Ok(replacement.clone());
                }
                Ok(self.clone())
            },
            TyKind::Type { name, args } => {
                let new_args: Vec<Ty> =
                    args.iter().map(|a| a.subst_type_vars(inst)).collect::<Result<_, _>>()?;
                Ok(Ty(TyKind::Type { name: name.clone(), args: new_args }))
            },
        }
    }
    pub(crate) fn is_monomorphic_instance_of(
        &self,
        instance: &Ty,
    ) -> Option<super::logic::TypeInstantiation> {
        let mut bindings: BTreeMap<super::logic::TypeVarId, Ty> = BTreeMap::new();
        if !Self::match_scheme(self, instance, &mut bindings) {
            return None;
        }
        if !bindings.values().all(|t| t.is_concrete_type()) {
            return None;
        }
        Some(super::logic::TypeInstantiation::try_new(bindings).ok()?)
    }
    fn match_scheme(
        scheme: &Ty,
        instance: &Ty,
        bindings: &mut BTreeMap<super::logic::TypeVarId, Ty>,
    ) -> bool {
        match (&scheme.0, &instance.0) {
            (TyKind::TypeVar { name, index, sort }, _) => {
                if sort != &Sort::typ() {
                    return false;
                }
                let id = super::logic::TypeVarId::new(name.clone(), *index as u32);
                if let Some(existing) = bindings.get(&id) {
                    return existing == instance;
                }
                bindings.insert(id, instance.clone());
                true
            },
            (TyKind::Type { name: sn, args: sa }, TyKind::Type { name: in_, args: ia }) => {
                sn == in_
                    && sa.len() == ia.len()
                    && sa.iter().zip(ia.iter()).all(|(s, i)| Self::match_scheme(s, i, bindings))
            },
            _ => false,
        }
    }

    pub fn prop() -> Self {
        Ty(TyKind::Type { name: Name::from("prop"), args: vec![] })
    }

    pub fn arrow(from: Ty, to: Ty) -> Self {
        Ty(TyKind::Type { name: Name::from("fun"), args: vec![from, to] })
    }

    pub fn dest_arrow(&self) -> Option<(&Ty, &Ty)> {
        match &self.0 {
            TyKind::Type { name, args } if name.as_str() == "fun" && args.len() == 2 => {
                Some((&args[0], &args[1]))
            },
            _ => None,
        }
    }

    pub fn is_prop(&self) -> bool {
        self == &Ty::prop()
    }
    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        match &self.0 {
            TyKind::TypeVar { name, index, sort } => {
                encoder.write_u8(1); // type variable tag
                encoder.write_name(name);
                encoder.write_u64(*index as u64);
                encoder.write_name(&sort.0);
            },
            TyKind::Type { name, args } => {
                encoder.write_u8(0); // type application, type schema v1
                encoder.write_name(name);
                encoder.write_u64(args.len() as u64);
                for arg in args {
                    arg.write_canonical(encoder);
                }
            },
        }
    }

    /// Reference encoder accessor: deconstruct a type application.
    /// Returns `None` for type variables. NOT for production encoding paths —
    /// use `write_canonical` for that.
    #[cfg(test)]
    pub(crate) fn as_type_app(&self) -> Option<(&Name, &[Ty])> {
        match &self.0 {
            TyKind::Type { name, args } => Some((name, args)),
            _ => None,
        }
    }

    /// Reference encoder accessor: deconstruct a type variable.
    /// Returns `None` for type applications. NOT for production encoding paths —
    /// use `write_canonical` for that.
    #[cfg(test)]
    pub(crate) fn as_type_var(&self) -> Option<(&Name, usize, &Sort)> {
        match &self.0 {
            TyKind::TypeVar { name, index, sort } => Some((name, *index, sort)),
            _ => None,
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            TyKind::TypeVar { name, index, .. } if *index == 0 => write!(f, "'{name}"),
            TyKind::TypeVar { name, index, .. } => write!(f, "'{name}.{index}"),
            TyKind::Type { name, args } if args.is_empty() => write!(f, "{name}"),
            TyKind::Type { name, args } if name.as_str() == "fun" && args.len() == 2 => {
                write!(f, "({:?} => {:?})", args[0], args[1])
            },
            TyKind::Type { name, args } => f.debug_tuple(name.as_str()).field(args).finish(),
        }
    }
}

#[cfg(test)]
mod polytype_tests {
    use super::*;

    #[test]
    fn monomorphic_instance_rejects_inconsistent_binding() {
        let s = Ty::arrow(
            Ty::tvar("'a", 0, Sort::typ()),
            Ty::arrow(Ty::tvar("'a", 0, Sort::typ()), Ty::base("bool").unwrap()),
        );
        let i = Ty::arrow(
            Ty::base("bool").unwrap(),
            Ty::arrow(Ty::base("nat").unwrap(), Ty::base("bool").unwrap()),
        );
        assert!(s.is_monomorphic_instance_of(&i).is_none());
    }

    #[test]
    fn monomorphic_instance_distinguishes_same_name_different_index() {
        let s = Ty::arrow(
            Ty::tvar("'a", 0, Sort::typ()),
            Ty::arrow(Ty::tvar("'a", 1, Sort::typ()), Ty::base("bool").unwrap()),
        );
        let i = Ty::arrow(
            Ty::base("bool").unwrap(),
            Ty::arrow(Ty::base("nat").unwrap(), Ty::base("bool").unwrap()),
        );
        assert!(s.is_monomorphic_instance_of(&i).is_some());
    }

    #[test]
    fn monomorphic_instance_rejects_non_concrete_replacement() {
        let s = Ty::arrow(Ty::tvar("'a", 0, Sort::typ()), Ty::base("bool").unwrap());
        let i = Ty::arrow(Ty::tvar("'b", 0, Sort::typ()), Ty::base("bool").unwrap());
        assert!(s.is_monomorphic_instance_of(&i).is_none());
    }

    #[test]
    fn monomorphic_instance_accepts_exact_match() {
        let id_ty = Ty::arrow(Ty::base("bool").unwrap(), Ty::base("bool").unwrap());
        let s = Ty::arrow(
            Ty::tvar("'a", 0, Sort::typ()),
            Ty::arrow(Ty::tvar("'a", 0, Sort::typ()), Ty::base("bool").unwrap()),
        );
        let i = Ty::arrow(id_ty.clone(), Ty::arrow(id_ty, Ty::base("bool").unwrap()));
        assert!(s.is_monomorphic_instance_of(&i).is_some());
    }

    #[test]
    fn is_concrete_type_rejects_nested_type_var() {
        // fun('b, bool) should NOT be concrete because 'b is a TypeVar inside
        let nested =
            Ty::apply("fun", vec![Ty::tvar("'b", 0, Sort::typ()), Ty::base("bool").unwrap()])
                .unwrap();
        assert!(!nested.is_concrete_type());
        // fun(bool, bool) IS concrete
        let concrete =
            Ty::apply("fun", vec![Ty::base("bool").unwrap(), Ty::base("bool").unwrap()]).unwrap();
        assert!(concrete.is_concrete_type());
        // plain bool IS concrete
        assert!(Ty::base("bool").unwrap().is_concrete_type());
        // plain 'a is NOT concrete
        assert!(!Ty::tvar("'a", 0, Sort::typ()).is_concrete_type());
    }
}
