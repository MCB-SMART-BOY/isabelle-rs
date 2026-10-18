//! Internal class graph and type-sort prechecks. No operation in this module
//! authorizes a class fact, an arity fact, or a theorem: callers must replay
//! the corresponding certificates before installing an updated algebra.

use std::collections::{BTreeMap, BTreeSet};

use thiserror::Error;

use crate::{Name, Sort, Ty, identity::CanonicalEncoder};

/// Invalid algebra input (user-fixable), or incompatible declarations during a merge.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub(crate) enum SortAlgebraError {
    /// A class name was already declared.
    #[error("class {0} is already declared")]
    DuplicateClass(Name),
    /// A class named in a sort or relation has not been declared.
    #[error("class {0} is not declared")]
    UndeclaredClass(Name),
    /// A new subclass relation would introduce a cycle.
    #[error("class relation {sub} <= {sup} would form a cycle")]
    CyclicRelation { sub: Name, sup: Name },
    /// Merged declarations give one class incompatible direct parent lists.
    #[error("class {0} has conflicting declarations")]
    ConflictingClass(Name),
    /// The owner-provided constructor arity disagrees with a previous insertion.
    #[error("type constructor {name} has arity {actual}, expected {expected}")]
    ConstructorArity { name: Name, expected: usize, actual: usize },
    /// The number of argument sorts does not equal the registered constructor arity.
    #[error("type constructor {name} received {actual} argument sorts, expected {expected}")]
    ArityArguments { name: Name, expected: usize, actual: usize },
    /// The constructor application itself has an invalid argument count.
    #[error("type constructor {name} has {actual} arguments, expected {expected}")]
    TypeArguments { name: Name, expected: usize, actual: usize },
    /// Two comparable result classes impose incompatible argument domains.
    #[error("incompatible arities for type constructor {name}, classes {left} and {right}")]
    ConflictingArity { name: Name, left: Name, right: Name },
}

/// Canonical graph data, distinct from the authorization proofs for its edges.
///
/// `declarations` stores direct superclass lists, `relations` stores separately
/// introduced class relations, and `arities` stores declared (not inherited)
/// domains. Each update is transactional: errors leave the source unmodified.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ClassAlgebra {
    declarations: BTreeMap<Name, BTreeSet<Name>>,
    relations: BTreeSet<(Name, Name)>,
    constructors: BTreeMap<Name, usize>,
    arities: BTreeMap<Name, BTreeMap<Name, Vec<Sort>>>,
}

impl ClassAlgebra {
    pub(crate) fn empty() -> Self {
        Self::default()
    }

    /// Add a fresh class with already-declared direct parents.
    pub(crate) fn declare_class(
        &self,
        name: Name,
        parents: &[Name],
    ) -> Result<Self, SortAlgebraError> {
        if self.declarations.contains_key(&name) {
            return Err(SortAlgebraError::DuplicateClass(name));
        }
        let mut direct = BTreeSet::new();
        for parent in parents {
            self.check_class(parent)?;
            direct.insert(parent.clone());
        }
        let mut next = self.clone();
        next.declarations.insert(name, direct);
        next.check_arities()?;
        Ok(next)
    }

    /// Add a proper relation; transitive and duplicate relations are harmless.
    pub(crate) fn add_relation(&self, sub: &Name, sup: &Name) -> Result<Self, SortAlgebraError> {
        self.check_new_relation(sub, sup)?;
        let mut next = self.clone();
        next.relations.insert((sub.clone(), sup.clone()));
        next.check_arities()?;
        Ok(next)
    }

    /// Insert an arity whose constructor arity has already been checked by the
    /// owner against the signature; comparable domains retain the weaker one.
    pub(crate) fn add_arity(
        &self,
        tycon: &Name,
        arity: usize,
        arg_sorts: &[Sort],
        result: &Name,
    ) -> Result<Self, SortAlgebraError> {
        self.check_class(result)?;
        for sort in arg_sorts {
            self.validate_sort(sort)?;
        }
        if arity != arg_sorts.len() {
            return Err(SortAlgebraError::ArityArguments {
                name: tycon.clone(),
                expected: arity,
                actual: arg_sorts.len(),
            });
        }
        let mut next = self.clone();
        next.register_constructor(tycon, arity)?;
        next.insert_arity(tycon, result, arg_sorts)?;
        next.check_arities()?;
        Ok(next)
    }

    pub(crate) fn has_certificate_edges(&self) -> bool {
        !self.relations.is_empty() || !self.arities.is_empty()
    }

    pub(crate) fn has_class(&self, class: &Name) -> bool {
        self.declarations.contains_key(class)
    }
    pub(crate) fn declared_classes(&self) -> impl Iterator<Item = &Name> {
        self.declarations.keys()
    }

    pub(crate) fn validate_sort(&self, sort: &Sort) -> Result<(), SortAlgebraError> {
        for class in sort.classes() {
            self.check_class(class)?;
        }
        Ok(())
    }

    pub(crate) fn is_class_le(&self, sub: &Name, sup: &Name) -> Result<bool, SortAlgebraError> {
        self.check_class(sub)?;
        self.check_class(sup)?;
        Ok(self.class_reaches(sub, sup))
    }

    pub(crate) fn is_sort_le(&self, sub: &Sort, sup: &Sort) -> Result<bool, SortAlgebraError> {
        self.validate_sort(sub)?;
        self.validate_sort(sup)?;
        Ok(self.sort_reaches(sub, sup))
    }

    /// A boolean precheck, not an `OFCLASS` or class-constraint proof.
    /// Even an unknown constructor has empty sort, as in Pure `of_sort`;
    /// the owner must separately certify that its type exists in the signature.
    pub(crate) fn has_type_sort(&self, ty: &Ty, required: &Sort) -> Result<bool, SortAlgebraError> {
        self.validate_sort(required)?;
        if let Some(atom) = ty.atomic_sort() {
            self.validate_sort(atom)?;
            return Ok(self.sort_reaches(atom, required));
        }
        let Some((name, args)) = ty.dest_type() else {
            return Ok(false);
        };
        if let Some(expected) = self.constructors.get(name)
            && *expected != args.len()
        {
            return Err(SortAlgebraError::TypeArguments {
                name: name.clone(),
                expected: *expected,
                actual: args.len(),
            });
        }
        if required.classes().is_empty() {
            return Ok(true);
        }
        let Some(domains) = self.completed_arities(name)? else {
            return Ok(false);
        };
        let mut domain = vec![Sort::empty(); args.len()];
        for class in required.classes() {
            let Some(next) = domains.get(class) else {
                return Ok(false);
            };
            for (current, additional) in domain.iter_mut().zip(next) {
                *current = self.inter_sort(current, additional);
            }
        }
        for (arg, sort) in args.iter().zip(&domain) {
            if !self.has_type_sort(arg, sort)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Combine declarations first, then recheck cycles and inherited arities.
    pub(crate) fn merge(&self, other: &Self) -> Result<Self, SortAlgebraError> {
        let mut next = self.clone();
        for (class, parents) in &other.declarations {
            if let Some(existing) = next.declarations.get(class) {
                if existing != parents {
                    return Err(SortAlgebraError::ConflictingClass(class.clone()));
                }
            } else {
                next.declarations.insert(class.clone(), parents.clone());
            }
        }
        next.relations.extend(other.relations.iter().cloned());
        next.check_graph()?;
        for (name, arity) in &other.constructors {
            next.register_constructor(name, *arity)?;
        }
        for (name, entries) in &other.arities {
            for (class, sorts) in entries {
                next.insert_arity(name, class, sorts)?;
            }
        }
        next.check_arities()?;
        Ok(next)
    }

    /// Stable direct declarations and checked edges for the signature identity.
    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_u64(self.declarations.len() as u64);
        for (class, parents) in &self.declarations {
            encoder.write_name(class);
            encoder.write_u64(parents.len() as u64);
            for parent in parents {
                encoder.write_name(parent);
            }
        }
        encoder.write_u64(self.relations.len() as u64);
        for (sub, sup) in &self.relations {
            encoder.write_name(sub);
            encoder.write_name(sup);
        }
        encoder.write_u64(self.constructors.len() as u64);
        for (name, arity) in &self.constructors {
            encoder.write_name(name);
            encoder.write_u64(*arity as u64);
        }
        encoder.write_u64(self.arities.len() as u64);
        for (name, entries) in &self.arities {
            encoder.write_name(name);
            encoder.write_u64(entries.len() as u64);
            for (class, domain) in entries {
                encoder.write_name(class);
                encoder.write_u64(domain.len() as u64);
                for sort in domain {
                    sort.write_canonical(encoder);
                }
            }
        }
    }

    fn check_class(&self, class: &Name) -> Result<(), SortAlgebraError> {
        if self.declarations.contains_key(class) {
            Ok(())
        } else {
            Err(SortAlgebraError::UndeclaredClass(class.clone()))
        }
    }

    fn check_new_relation(&self, sub: &Name, sup: &Name) -> Result<(), SortAlgebraError> {
        self.check_class(sub)?;
        self.check_class(sup)?;
        if sub == sup || self.class_reaches(sup, sub) {
            return Err(SortAlgebraError::CyclicRelation { sub: sub.clone(), sup: sup.clone() });
        }
        Ok(())
    }

    fn class_reaches(&self, sub: &Name, sup: &Name) -> bool {
        let mut visited = BTreeSet::new();
        let mut pending = vec![sub];
        while let Some(class) = pending.pop() {
            if class == sup {
                return true;
            }
            if visited.insert(class) {
                if let Some(parents) = self.declarations.get(class) {
                    pending.extend(parents);
                }
                pending.extend(
                    self.relations.iter().filter_map(|(low, high)| (low == class).then_some(high)),
                );
            }
        }
        false
    }

    fn sort_reaches(&self, sub: &Sort, sup: &Sort) -> bool {
        sup.classes()
            .iter()
            .all(|target| sub.classes().iter().any(|source| self.class_reaches(source, target)))
    }

    fn inter_sort(&self, left: &Sort, right: &Sort) -> Sort {
        Sort::new(
            left.classes()
                .iter()
                .chain(right.classes())
                .filter(|class| {
                    !left
                        .classes()
                        .iter()
                        .chain(right.classes())
                        .any(|other| other != *class && self.class_reaches(other, class))
                })
                .cloned()
                .collect(),
        )
    }

    fn register_constructor(&mut self, name: &Name, arity: usize) -> Result<(), SortAlgebraError> {
        if let Some(expected) = self.constructors.insert(name.clone(), arity)
            && expected != arity
        {
            return Err(SortAlgebraError::ConstructorArity {
                name: name.clone(),
                expected,
                actual: arity,
            });
        }
        Ok(())
    }

    fn insert_arity(
        &mut self,
        name: &Name,
        class: &Name,
        sorts: &[Sort],
    ) -> Result<(), SortAlgebraError> {
        if let Some(existing) = self.arities.get(name).and_then(|entries| entries.get(class)) {
            if self.sorts_reach(sorts, existing) {
                return Ok(());
            }
            if !self.sorts_reach(existing, sorts) {
                return Err(SortAlgebraError::ConflictingArity {
                    name: name.clone(),
                    left: class.clone(),
                    right: class.clone(),
                });
            }
        }
        self.arities.entry(name.clone()).or_default().insert(class.clone(), sorts.to_vec());
        Ok(())
    }

    fn sorts_reach(&self, left: &[Sort], right: &[Sort]) -> bool {
        left.len() == right.len() && left.iter().zip(right).all(|(a, b)| self.sort_reaches(a, b))
    }

    fn check_graph(&self) -> Result<(), SortAlgebraError> {
        for (class, parents) in &self.declarations {
            for parent in parents {
                self.check_class(parent)?;
                if class == parent || self.class_reaches(parent, class) {
                    return Err(SortAlgebraError::CyclicRelation {
                        sub: class.clone(),
                        sup: parent.clone(),
                    });
                }
            }
        }
        for (sub, sup) in &self.relations {
            self.check_new_relation(sub, sup)?;
        }
        Ok(())
    }

    fn check_arities(&self) -> Result<(), SortAlgebraError> {
        for name in self.constructors.keys() {
            self.completed_arities(name)?;
        }
        Ok(())
    }

    fn completed_arities(
        &self,
        name: &Name,
    ) -> Result<Option<BTreeMap<Name, Vec<Sort>>>, SortAlgebraError> {
        let Some(raw) = self.arities.get(name) else {
            return Ok(None);
        };
        let mut completed: BTreeMap<Name, Vec<Sort>> = BTreeMap::new();
        for (class, sorts) in raw {
            self.check_class(class)?;
            for sup in self.declarations.keys().filter(|sup| self.class_reaches(class, sup)) {
                match completed.get(sup) {
                    Some(existing) if self.sorts_reach(sorts, existing) => continue,
                    Some(existing) if !self.sorts_reach(existing, sorts) => {
                        return Err(SortAlgebraError::ConflictingArity {
                            name: name.clone(),
                            left: class.clone(),
                            right: sup.clone(),
                        });
                    },
                    _ => {},
                }
                completed.insert(sup.clone(), sorts.clone());
            }
        }
        // A stronger requirement for a superclass than for its subclass is
        // not coregular, even when inherited entries are individually comparable.
        for (sub, sub_domain) in &completed {
            for (sup, sup_domain) in &completed {
                if self.class_reaches(sub, sup) && !self.sorts_reach(sub_domain, sup_domain) {
                    return Err(SortAlgebraError::ConflictingArity {
                        name: name.clone(),
                        left: sub.clone(),
                        right: sup.clone(),
                    });
                }
            }
        }
        Ok(Some(completed))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn class(name: &str) -> Name {
        Name::from(name)
    }

    fn sort(name: &str) -> Sort {
        Sort::new(vec![class(name)])
    }

    fn base() -> ClassAlgebra {
        ClassAlgebra::empty().declare_class(class("HOL.type"), &[]).unwrap()
    }

    fn digest(algebra: &ClassAlgebra) -> [u8; 32] {
        let mut encoder = CanonicalEncoder::new(b"sort-algebra-test");
        algebra.write_canonical(&mut encoder);
        encoder.finish()
    }

    #[test]
    fn class_algebra_empty_sort_remains_distinct_from_hol_type() {
        let algebra = base();
        assert!(algebra.is_sort_le(&sort("HOL.type"), &Sort::empty()).unwrap());
        assert!(!algebra.is_sort_le(&Sort::empty(), &sort("HOL.type")).unwrap());
        assert!(algebra.has_type_sort(&Ty::base("unknown").unwrap(), &Sort::empty()).unwrap());
        assert!(!algebra.has_type_sort(&Ty::base("unknown").unwrap(), &sort("HOL.type")).unwrap());
    }

    #[test]
    fn class_algebra_invalid_parents_and_cycles_are_rejected() {
        let base = base();
        assert_eq!(
            base.declare_class(class("A"), &[class("missing")]),
            Err(SortAlgebraError::UndeclaredClass(class("missing")))
        );
        let child = base.declare_class(class("A"), &[class("HOL.type")]).unwrap();
        assert!(matches!(
            child.add_relation(&class("HOL.type"), &class("A")),
            Err(SortAlgebraError::CyclicRelation { .. })
        ));
        assert_eq!(
            child.declare_class(class("A"), &[]),
            Err(SortAlgebraError::DuplicateClass(class("A")))
        );
        assert_eq!(
            child.validate_sort(&sort("missing")),
            Err(SortAlgebraError::UndeclaredClass(class("missing")))
        );
    }

    #[test]
    fn class_algebra_inherited_domain_checks_type_arguments() {
        let algebra = base().declare_class(class("small"), &[class("HOL.type")]).unwrap();
        let algebra =
            algebra.add_arity(&class("box"), 1, &[sort("HOL.type")], &class("small")).unwrap();
        let good = Ty::apply("box", vec![Ty::tfree("a", sort("small"))]).unwrap();
        let bad = Ty::apply("box", vec![Ty::tfree("a", Sort::empty())]).unwrap();
        assert!(algebra.has_type_sort(&good, &sort("HOL.type")).unwrap());
        assert!(!algebra.has_type_sort(&bad, &sort("small")).unwrap());
        assert_eq!(
            algebra.has_type_sort(&Ty::base("box").unwrap(), &sort("small")),
            Err(SortAlgebraError::TypeArguments { name: class("box"), expected: 1, actual: 0 })
        );
        assert_eq!(
            algebra.add_arity(&class("box"), 2, &[Sort::empty(), Sort::empty()], &class("small")),
            Err(SortAlgebraError::ConstructorArity { name: class("box"), expected: 1, actual: 2 })
        );
    }

    #[test]
    fn class_algebra_relation_and_merge_preserve_weaker_inherited_domain() {
        let root =
            base().declare_class(class("A"), &[]).unwrap().declare_class(class("B"), &[]).unwrap();
        let left = root.add_arity(&class("box"), 1, &[Sort::empty()], &class("A")).unwrap();
        let right = root.add_arity(&class("box"), 1, &[sort("HOL.type")], &class("B")).unwrap();
        let relation = left.add_relation(&class("A"), &class("B")).unwrap();
        let joined = relation.merge(&right).unwrap();
        let combined = left.merge(&right).unwrap().add_relation(&class("A"), &class("B")).unwrap();
        let argument = Ty::apply("box", vec![Ty::tfree("a", Sort::empty())]).unwrap();
        assert!(joined.has_type_sort(&argument, &sort("B")).unwrap());
        assert!(combined.has_type_sort(&argument, &sort("B")).unwrap());
    }

    #[test]
    fn class_algebra_branch_merge_rejects_cycle() {
        let root =
            base().declare_class(class("A"), &[]).unwrap().declare_class(class("B"), &[]).unwrap();
        let left = root.add_relation(&class("A"), &class("B")).unwrap();
        let right = root.add_relation(&class("B"), &class("A")).unwrap();
        assert!(matches!(left.merge(&right), Err(SortAlgebraError::CyclicRelation { .. })));
    }

    #[test]
    fn class_algebra_compatible_merge_is_order_independent() {
        let root = base().declare_class(class("A"), &[class("HOL.type")]).unwrap();
        let strong = root.add_arity(&class("box"), 1, &[sort("HOL.type")], &class("A")).unwrap();
        let weak = root.add_arity(&class("box"), 1, &[Sort::empty()], &class("A")).unwrap();
        let both = strong.merge(&weak).unwrap();
        assert_eq!(digest(&both), digest(&weak.merge(&strong).unwrap()));
        assert_eq!(digest(&both), digest(&weak));
        let arg = Ty::tfree("a", Sort::empty());
        assert!(both.has_type_sort(&Ty::apply("box", vec![arg]).unwrap(), &sort("A")).unwrap());
    }

    #[test]
    fn class_algebra_repeated_parent_is_idempotent() {
        let root = base();
        let once = root.declare_class(class("A"), &[class("HOL.type")]).unwrap();
        let repeated =
            root.declare_class(class("A"), &[class("HOL.type"), class("HOL.type")]).unwrap();
        assert_eq!(digest(&once), digest(&repeated));
        assert!(repeated.is_class_le(&class("A"), &class("HOL.type")).unwrap());
    }

    #[test]
    fn class_algebra_comparable_arities_accept_empty_sort_in_both_orders() {
        let root = base().declare_class(class("A"), &[]).unwrap();
        for (first, second) in
            [(Sort::empty(), sort("HOL.type")), (sort("HOL.type"), Sort::empty())]
        {
            let algebra = root
                .add_arity(&class("box"), 1, &[first], &class("A"))
                .unwrap()
                .add_arity(&class("box"), 1, &[second], &class("A"))
                .unwrap();
            let argument = Ty::apply("box", vec![Ty::tfree("a", Sort::empty())]).unwrap();
            assert!(algebra.has_type_sort(&argument, &sort("A")).unwrap());
        }
    }

    #[test]
    fn class_algebra_incomparable_arity_domains_reject_without_mutation() {
        let root =
            base().declare_class(class("A"), &[]).unwrap().declare_class(class("B"), &[]).unwrap();
        let left = root.add_arity(&class("box"), 1, &[sort("A")], &class("HOL.type")).unwrap();
        let before = digest(&left);
        assert!(matches!(
            left.add_arity(&class("box"), 1, &[sort("B")], &class("HOL.type")),
            Err(SortAlgebraError::ConflictingArity { .. })
        ));
        assert_eq!(before, digest(&left));
    }
}
