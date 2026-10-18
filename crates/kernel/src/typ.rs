use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use super::{KernelError, Name, identity::CanonicalEncoder};

/// A nonempty generalization must use an index above the complete input bound.
/// Proof-only operands can have a different bound; callers check the theorem or
/// certified object once before mapping each of its component types and terms.
pub(crate) fn check_generalize_index(
    is_empty: bool,
    index: usize,
    max_index: Option<usize>,
) -> Result<(), KernelError> {
    if is_empty {
        return Ok(());
    }
    if let Some(max_index) = max_index
        && index <= max_index
    {
        return Err(KernelError::GeneralizeIndexNotFresh { index, max_index });
    }
    Ok(())
}

/// A canonical intersection of fully-qualified type classes.
///
/// The empty sort is distinct from every singleton, including `HOL.type`.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sort(Box<[Name]>);

impl Sort {
    pub fn new(mut classes: Vec<Name>) -> Self {
        classes.sort_unstable();
        classes.dedup();
        Self(classes.into_boxed_slice())
    }

    pub fn empty() -> Self {
        Self(Box::new([]))
    }

    pub fn hol_type() -> Self {
        Self::new(vec![Name::from("HOL.type")])
    }

    pub fn classes(&self) -> &[Name] {
        &self.0
    }

    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_u64(self.0.len() as u64);
        for class in &self.0 {
            encoder.write_name(class);
        }
    }
}

#[cfg(test)]
impl Sort {
    pub fn arbitrary(name: &str) -> Self {
        Self::new(vec![Name::from(name)])
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(&self.0).finish()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TyKind {
    Type { name: Name, args: Vec<Ty> },
    TFree { name: Name, sort: Sort },
    TVar { name: Name, index: usize, sort: Sort },
}
fn type_constructor_rank(ty: &TyKind) -> u8 {
    match ty {
        TyKind::TVar { .. } => 0,
        TyKind::TFree { .. } => 1,
        TyKind::Type { .. } => 2,
    }
}

/// Strict kernel type.
///
/// There is deliberately no `dummy` constructor. The reserved name `dummy` is
/// rejected by public constructors so compatibility uncertainty cannot enter
/// the new TCB as a normal type.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ty(TyKind);

/// One shared identity table for all annotations in a term or substitution range.
#[derive(Default)]
pub(crate) struct TypeIdentityMap<'a>(BTreeMap<(&'a Name, Option<usize>), &'a Sort>);

impl<'a> TypeIdentityMap<'a> {
    pub(crate) fn validate(&mut self, ty: &'a Ty) -> Result<(), KernelError> {
        let mut result = Ok(());
        ty.for_each_type_atom(&mut |name, index, sort| {
            if result.is_err() {
                return;
            }
            match self.0.entry((name, index)) {
                std::collections::btree_map::Entry::Occupied(entry) if *entry.get() != sort => {
                    result = Err(KernelError::TypeIdentityMismatch {
                        name: name.clone(),
                        index,
                        expected: (*entry.get()).clone(),
                        actual: sort.clone(),
                    });
                },
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(sort);
                },
                _ => {},
            }
        });
        result
    }

    pub(crate) fn validate_term(&mut self, term: &'a crate::Term) -> Result<(), KernelError> {
        let mut result = Ok(());
        term.for_each_type_annotation(&mut |ty| {
            if result.is_ok() {
                result = self.validate(ty);
            }
        });
        result
    }
}

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
            return Err(KernelError::Invariant(format!(
                "tick-prefixed names are reserved for type variables, got '{name}'"
            )));
        }
        Ok(Ty(TyKind::Type { name, args }))
    }

    pub fn tfree(name: impl Into<Name>, sort: Sort) -> Self {
        Ty(TyKind::TFree { name: name.into(), sort })
    }

    pub fn tvar(name: impl Into<Name>, index: usize, sort: Sort) -> Self {
        Ty(TyKind::TVar { name: name.into(), index, sort })
    }
    /// Isabelle's `Term_Ord.typ_ord`, which differs from Rust's derived `Ord`:
    /// schematic types precede fixed types, then constructors; schematic
    /// indices precede names.
    pub(crate) fn cmp_term_ord(&self, other: &Self) -> Ordering {
        match (&self.0, &other.0) {
            (
                TyKind::TVar { name: x, index: i, sort: s },
                TyKind::TVar { name: y, index: j, sort: t },
            ) => i.cmp(j).then_with(|| x.cmp(y)).then_with(|| s.cmp(t)),
            (TyKind::TFree { name: x, sort: s }, TyKind::TFree { name: y, sort: t }) => {
                x.cmp(y).then_with(|| s.cmp(t))
            },
            (TyKind::Type { name: x, args: xs }, TyKind::Type { name: y, args: ys }) => {
                x.cmp(y).then_with(|| {
                    xs.iter()
                        .zip(ys)
                        .map(|(a, b)| a.cmp_term_ord(b))
                        .find(|order| *order != Ordering::Equal)
                        .unwrap_or_else(|| xs.len().cmp(&ys.len()))
                })
            },
            (left, right) => type_constructor_rank(left).cmp(&type_constructor_rank(right)),
        }
    }

    pub fn is_tvar(&self) -> bool {
        matches!(&self.0, TyKind::TVar { .. })
    }

    pub fn is_concrete_type(&self) -> bool {
        match &self.0 {
            TyKind::TFree { .. } | TyKind::TVar { .. } => false,
            TyKind::Type { args, .. } => args.iter().all(Self::is_concrete_type),
        }
    }

    pub(crate) fn dest_type(&self) -> Option<(&Name, &[Ty])> {
        match &self.0 {
            TyKind::Type { name, args } => Some((name, args)),
            TyKind::TFree { .. } | TyKind::TVar { .. } => None,
        }
    }

    pub(crate) fn atomic_sort(&self) -> Option<&Sort> {
        match &self.0 {
            TyKind::TFree { sort, .. } | TyKind::TVar { sort, .. } => Some(sort),
            TyKind::Type { .. } => None,
        }
    }
    /// Simultaneously substitute exact atomic identities; the range is never
    /// traversed again, so a source/local sort cannot be silently reinterpreted.
    pub(crate) fn rewrite_atomic_types(
        &self,
        replacements: &BTreeMap<Ty, Ty>,
    ) -> Result<Ty, KernelError> {
        if let Some(replacement) = replacements.get(self) {
            return Ok(replacement.clone());
        }
        match &self.0 {
            TyKind::TFree { .. } | TyKind::TVar { .. } => Ok(self.clone()),
            TyKind::Type { name, args } => Ty::apply(
                name.clone(),
                args.iter()
                    .map(|arg| arg.rewrite_atomic_types(replacements))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        }
    }
    /// Generalize selected fixed type names with one shared schematic index.
    /// The caller checks freshness for the whole certified object beforehand.
    pub(crate) fn generalize_type(
        &self,
        names: &BTreeSet<Name>,
        index: usize,
    ) -> Result<Ty, KernelError> {
        if names.is_empty() {
            return Ok(self.clone());
        }
        match &self.0 {
            TyKind::TFree { name, sort } if names.contains(name) => {
                let result = Ty::tvar(name.clone(), index, sort.clone());
                result.validate_type_variable()?;
                Ok(result)
            },
            TyKind::TFree { .. } | TyKind::TVar { .. } => Ok(self.clone()),
            TyKind::Type { name, args } => Ok(Ty(TyKind::Type {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|arg| arg.generalize_type(names, index))
                    .collect::<Result<_, _>>()?,
            })),
        }
    }

    pub(crate) fn atomic_name(&self) -> Option<&Name> {
        match &self.0 {
            TyKind::TFree { name, .. } | TyKind::TVar { name, .. } => Some(name),
            TyKind::Type { .. } => None,
        }
    }

    pub(crate) fn validate_type_variable(&self) -> Result<(), KernelError> {
        let TyKind::TVar { name, index, .. } = &self.0 else {
            return Ok(());
        };
        u32::try_from(*index).map_err(|_| KernelError::TypeVariableIndexOutOfRange {
            name: name.clone(),
            index: *index,
        })?;
        Ok(())
    }

    pub fn tvar_name(&self) -> Option<&Name> {
        match &self.0 {
            TyKind::TVar { name, .. } => Some(name),
            _ => None,
        }
    }

    /// Visit schematic type-variable leaves; fixed parameters remain distinct.
    pub fn for_each_type_var(&self, f: &mut impl FnMut(&Name, usize, &Sort)) {
        match &self.0 {
            TyKind::TVar { name, index, sort } => f(name, *index, sort),
            TyKind::TFree { .. } => {},
            TyKind::Type { args, .. } => {
                for arg in args {
                    arg.for_each_type_var(f);
                }
            },
        }
    }

    /// Visit fixed and schematic atomic types without conflating their identities.
    pub(crate) fn for_each_type_atom<'a>(
        &'a self,
        f: &mut impl FnMut(&'a Name, Option<usize>, &'a Sort),
    ) {
        match &self.0 {
            TyKind::TFree { name, sort } => f(name, None, sort),
            TyKind::TVar { name, index, sort } => f(name, Some(*index), sort),
            TyKind::Type { args, .. } => {
                for arg in args {
                    arg.for_each_type_atom(f);
                }
            },
        }
    }

    /// Fixed atoms are raw syntax until a proof context authorizes each occurrence.
    pub(crate) fn for_each_type_free(&self, f: &mut impl FnMut(&Name, &Sort)) {
        match &self.0 {
            TyKind::TFree { name, sort } => f(name, sort),
            TyKind::TVar { .. } => {},
            TyKind::Type { args, .. } => {
                for arg in args {
                    arg.for_each_type_free(f);
                }
            },
        }
    }

    pub(crate) fn first_type_free(&self) -> Option<(&Name, &Sort)> {
        match &self.0 {
            TyKind::TFree { name, sort } => Some((name, sort)),
            TyKind::TVar { .. } => None,
            TyKind::Type { args, .. } => args.iter().find_map(Self::first_type_free),
        }
    }

    pub fn has_type_vars(&self) -> bool {
        let mut found = false;
        self.for_each_type_var(&mut |_, _, _| found = true);
        found
    }

    /// Apply an exact-key, finite one-shot substitution to schematic TVars.
    pub(crate) fn subst_type_vars(
        &self,
        inst: &crate::logic::TypeInstantiation,
    ) -> Result<Ty, KernelError> {
        match &self.0 {
            TyKind::TVar { name, index, sort } => {
                let index = u32::try_from(*index).map_err(|_| {
                    KernelError::TypeVariableIndexOutOfRange { name: name.clone(), index: *index }
                })?;
                let id = crate::logic::TypeVarId::new(name.clone(), index, sort.clone());
                Ok(inst.get(&id).cloned().unwrap_or_else(|| self.clone()))
            },
            TyKind::TFree { .. } => Ok(self.clone()),
            TyKind::Type { name, args } => {
                let args =
                    args.iter().map(|arg| arg.subst_type_vars(inst)).collect::<Result<_, _>>()?;
                Ok(Ty(TyKind::Type { name: name.clone(), args }))
            },
        }
    }
    pub(crate) fn match_instance(&self, instance: &Ty) -> Option<super::logic::TypeInstantiation> {
        let mut bindings: BTreeMap<super::logic::TypeVarId, Ty> = BTreeMap::new();
        if !Self::match_scheme(self, instance, &mut bindings) {
            return None;
        }
        super::logic::TypeInstantiation::try_new(bindings).ok()
    }

    fn match_scheme(
        scheme: &Ty,
        instance: &Ty,
        bindings: &mut BTreeMap<super::logic::TypeVarId, Ty>,
    ) -> bool {
        match (&scheme.0, &instance.0) {
            (TyKind::TVar { name, index, sort }, _) => {
                let Ok(index) = u32::try_from(*index) else {
                    return false;
                };
                let id = super::logic::TypeVarId::new(name.clone(), index, sort.clone());
                if let Some(existing) = bindings.get(&id) {
                    return existing == instance;
                }
                bindings.insert(id, instance.clone());
                true
            },
            (TyKind::TFree { name: left, sort: ls }, TyKind::TFree { name: right, sort: rs }) => {
                left == right && ls == rs
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
            TyKind::TVar { name, index, sort } => {
                encoder.write_u8(1);
                encoder.write_name(name);
                encoder.write_u64(*index as u64);
                sort.write_canonical(encoder);
            },
            TyKind::TFree { name, sort } => {
                encoder.write_u8(2);
                encoder.write_name(name);
                sort.write_canonical(encoder);
            },
            TyKind::Type { name, args } => {
                encoder.write_u8(0);
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
            TyKind::TVar { name, index, sort } => Some((name, *index, sort)),
            _ => None,
        }
    }

    #[cfg(test)]
    pub(crate) fn as_type_free(&self) -> Option<(&Name, &Sort)> {
        match &self.0 {
            TyKind::TFree { name, sort } => Some((name, sort)),
            _ => None,
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            TyKind::TVar { name, index, .. } if *index == 0 => write!(f, "'{name}"),
            TyKind::TVar { name, index, .. } => write!(f, "'{name}.{index}"),
            TyKind::TFree { name, sort } => write!(f, "'{name}::{sort:?}"),
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
    fn canonical_sort_deduplicates_classes_without_erasing_empty_sort() {
        let sorted = Sort::new(vec!["z".into(), "a".into(), "z".into()]);
        assert_eq!(sorted.classes(), &[Name::from("a"), Name::from("z")]);
        assert_ne!(Sort::empty(), Sort::hol_type());
        assert_ne!(Sort::new(vec![Name::from("Other.type")]), Sort::hol_type());
    }

    #[test]
    fn fixed_type_parameter_never_matches_schematic_identity() {
        let sort = Sort::hol_type();
        let fixed = Ty::tfree("a", sort.clone());
        let schematic = Ty::tvar("a", 0, sort);
        assert_ne!(fixed, schematic);
        assert!(!fixed.has_type_vars());
        assert!(schematic.has_type_vars());
        assert!(fixed.match_instance(&schematic).is_none());
    }

    #[test]
    fn certify_type_variable_unsupported_sort_rejects() {
        let invalid = Ty::tvar("a", 0, Sort::arbitrary("order"));
        assert!(matches!(
            crate::Signature::new().validate_type(&invalid),
            Err(KernelError::UnsupportedTypeSort { .. })
        ));
    }

    #[test]
    fn monomorphic_instance_rejects_inconsistent_binding() {
        let s = Ty::arrow(
            Ty::tvar("'a", 0, Sort::hol_type()),
            Ty::arrow(Ty::tvar("'a", 0, Sort::hol_type()), Ty::base("bool").unwrap()),
        );
        let i = Ty::arrow(
            Ty::base("bool").unwrap(),
            Ty::arrow(Ty::base("nat").unwrap(), Ty::base("bool").unwrap()),
        );
        assert!(s.match_instance(&i).is_none());
    }

    #[test]
    fn monomorphic_instance_distinguishes_same_name_different_index() {
        let s = Ty::arrow(
            Ty::tvar("'a", 0, Sort::hol_type()),
            Ty::arrow(Ty::tvar("'a", 1, Sort::hol_type()), Ty::base("bool").unwrap()),
        );
        let i = Ty::arrow(
            Ty::base("bool").unwrap(),
            Ty::arrow(Ty::base("nat").unwrap(), Ty::base("bool").unwrap()),
        );
        assert!(s.match_instance(&i).is_some());
    }

    #[test]
    fn monomorphic_instance_accepts_exact_match() {
        let id_ty = Ty::arrow(Ty::base("bool").unwrap(), Ty::base("bool").unwrap());
        let s = Ty::arrow(
            Ty::tvar("'a", 0, Sort::hol_type()),
            Ty::arrow(Ty::tvar("'a", 0, Sort::hol_type()), Ty::base("bool").unwrap()),
        );
        let i = Ty::arrow(id_ty.clone(), Ty::arrow(id_ty, Ty::base("bool").unwrap()));
        assert!(s.match_instance(&i).is_some());
    }

    #[test]
    fn is_concrete_type_rejects_nested_type_var() {
        // fun('b, bool) should NOT be concrete because 'b is a TypeVar inside
        let nested =
            Ty::apply("fun", vec![Ty::tvar("'b", 0, Sort::hol_type()), Ty::base("bool").unwrap()])
                .unwrap();
        assert!(!nested.is_concrete_type());
        // fun(bool, bool) IS concrete
        let concrete =
            Ty::apply("fun", vec![Ty::base("bool").unwrap(), Ty::base("bool").unwrap()]).unwrap();
        assert!(concrete.is_concrete_type());
        // plain bool IS concrete
        assert!(Ty::base("bool").unwrap().is_concrete_type());
        // plain 'a is NOT concrete
        assert!(!Ty::tvar("'a", 0, Sort::hol_type()).is_concrete_type());
    }
    #[test]
    fn generalize_type_selected_name_preserves_sort_and_unselected_atoms() {
        let sort = Sort::empty();
        let fixed = Ty::tfree("a_", sort.clone());
        let unrelated = Ty::tfree("b", sort.clone());
        let existing = Ty::tvar("c", 3, sort.clone());
        let source =
            Ty::apply("pair", vec![fixed.clone(), unrelated.clone(), existing.clone()]).unwrap();
        let selected = BTreeSet::from([Name::from("a_")]);
        let expected =
            Ty::apply("pair", vec![Ty::tvar("a_", 7, sort), unrelated, existing]).unwrap();
        assert_eq!(source.generalize_type(&selected, 7), Ok(expected));
        assert_eq!(source.generalize_type(&BTreeSet::new(), usize::MAX), Ok(source));
    }

    #[test]
    fn generalize_type_selected_index_out_of_range_rejects() {
        let Ok(index) = usize::try_from(u64::from(u32::MAX) + 1) else {
            return;
        };
        let source = Ty::tfree("a", Sort::empty());
        assert_eq!(
            source.generalize_type(&BTreeSet::from([Name::from("a")]), index),
            Err(KernelError::TypeVariableIndexOutOfRange { name: "a".into(), index }),
        );
    }

    #[test]
    fn check_generalize_index_nonempty_selection_requires_freshness() {
        assert_eq!(check_generalize_index(true, 0, Some(usize::MAX)), Ok(()));
        assert_eq!(
            check_generalize_index(false, 3, Some(3)),
            Err(KernelError::GeneralizeIndexNotFresh { index: 3, max_index: 3 }),
        );
        assert_eq!(check_generalize_index(false, 0, None), Ok(()));
    }
}
