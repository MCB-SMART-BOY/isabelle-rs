//! Goal-directed class evidence. The class graph is a precheck, not proof authority.
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    ClosedThm, DependencySet, Derivation, KernelError, KernelRules, KernelThm, Name, ProofContext,
    RawTerm, Sort, TheoryId, TrustedTheory, Ty, identity::CanonicalEncoder,
};

/// Candidate syntax only: neither constructing nor cloning this tree establishes OFCLASS.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OfClassCandidate {
    AnnotatedAtomLeaf,
    ExportPremiseLeaf { slot: usize },
    ClassWeaken { lower: Name, premise: Box<Self> },
    TypeConstructor { arguments: Vec<Vec<Self>> },
    SemanticArity { arguments: Vec<Vec<Self>> },
}

impl OfClassCandidate {
    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        match self {
            Self::AnnotatedAtomLeaf => encoder.write_u8(0),
            Self::ExportPremiseLeaf { slot } => {
                encoder.write_u8(1);
                encoder.write_u64(*slot as u64);
            },
            Self::ClassWeaken { lower, premise } => {
                encoder.write_u8(2);
                encoder.write_name(lower);
                premise.write_canonical(encoder);
            },
            Self::TypeConstructor { arguments } | Self::SemanticArity { arguments } => {
                encoder.write_u8(if matches!(self, Self::TypeConstructor { .. }) { 3 } else { 4 });
                encoder.write_u64(arguments.len() as u64);
                for arg in arguments {
                    encoder.write_u64(arg.len() as u64);
                    for proof in arg {
                        proof.write_canonical(encoder);
                    }
                }
            },
        }
    }
}

/// A proof checked against a particular immutable owner and an exact goal.
/// Its fields cannot be assembled by callers or recovered from a digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedOfClassProof {
    owner: TheoryId,
    ty: Ty,
    class: Name,
    candidate: OfClassCandidate,
    dependencies: DependencySet,
}

impl ClosedOfClassProof {
    pub fn ty(&self) -> &Ty {
        &self.ty
    }
    pub fn class(&self) -> &Name {
        &self.class
    }
    pub fn owner(&self) -> TheoryId {
        self.owner
    }
    pub(crate) fn dependencies(&self) -> &DependencySet {
        &self.dependencies
    }

    /// Recheck all nodes, including referenced certificates, in the current owner.
    pub(crate) fn replay(&self, owner: &TrustedTheory) -> Result<(), KernelError> {
        let source = owner.find_owner(self.owner).ok_or(KernelError::UnknownClassEvidence)?;
        check_candidate(source, &self.ty, &self.class, &self.candidate, &[], false)?;
        let mut dependencies = DependencySet::empty();
        collect_dependencies(
            source,
            &self.ty,
            &self.class,
            &self.candidate,
            &[],
            &mut BTreeSet::new(),
            &mut dependencies,
        )?;
        if dependencies != self.dependencies {
            return Err(KernelError::UnknownClassEvidence);
        }
        Ok(())
    }
}

/// A judgment under private export premises. It cannot materialize a theorem:
/// the bound checker must certify the corresponding physical binder path.
pub(crate) struct ScopedOfClassEvidence {
    used_slots: BTreeSet<usize>,
    dependencies: DependencySet,
}

impl ScopedOfClassEvidence {
    pub(crate) fn slots(&self) -> &BTreeSet<usize> {
        &self.used_slots
    }
    pub(crate) fn dependencies(&self) -> &DependencySet {
        &self.dependencies
    }
}

/// Checked arity provenance. Fresh nonempty constructors have a canonical
/// product-of-parameters carrier (unit for arity zero); each parameter must be
/// inhabited via HOL.type. No arbitrary predicate or caller-supplied theorem is
/// accepted as a model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticArityCert {
    FunctionTypeArityCert,
    ItselfArityCert,
    FreshNonemptyTyconCert { tycon: Name, arity: usize },
}

impl SemanticArityCert {
    pub(crate) fn tycon(&self) -> Name {
        match self {
            Self::FunctionTypeArityCert => Name::from("fun"),
            Self::ItselfArityCert => Name::from("itself"),
            Self::FreshNonemptyTyconCert { tycon, .. } => tycon.clone(),
        }
    }

    pub(crate) fn arity(&self) -> usize {
        match self {
            Self::FunctionTypeArityCert => 2,
            Self::ItselfArityCert => 1,
            Self::FreshNonemptyTyconCert { arity, .. } => *arity,
        }
    }

    pub(crate) fn check_in_parent(&self, parent: &TrustedTheory) -> Result<(), KernelError> {
        let name = self.tycon();
        crate::Signature::validate_constructor_arity(&name, self.arity())?;
        if parent.signature().type_constructor_arity(&name) != Some(self.arity()) {
            return Err(KernelError::UnknownClassEvidence);
        }
        if !parent.signature().has_class(&Name::from("HOL.type")) {
            return Err(KernelError::UnknownClassEvidence);
        }
        match self {
            Self::FreshNonemptyTyconCert { tycon, arity } => {
                if matches!(tycon.as_str(), "fun" | "itself" | "prop")
                    || !parent.has_fresh_nonempty_declaration(tycon, *arity)
                {
                    return Err(KernelError::UnknownClassEvidence);
                }
                Ok(())
            },
            _ => Ok(()),
        }
    }
}

/// A persistent checked arity, installed only after its proof has been replayed
/// in the parent that does not yet contain this candidate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArityCert {
    pub(crate) parent: TheoryId,
    pub(crate) tycon: Name,
    pub(crate) arg_sorts: Vec<Sort>,
    pub(crate) result: Name,
    pub(crate) proof: OfClassCandidate,
    pub(crate) semantic: Option<SemanticArityCert>,
}

impl ArityCert {
    pub fn tycon(&self) -> &Name {
        &self.tycon
    }
    pub fn arg_sorts(&self) -> &[Sort] {
        &self.arg_sorts
    }
    pub fn result(&self) -> &Name {
        &self.result
    }
    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        self.parent.write_canonical(encoder);
        encoder.write_name(&self.tycon);
        encoder.write_u64(self.arg_sorts.len() as u64);
        for sort in &self.arg_sorts {
            sort.write_canonical(encoder);
        }
        encoder.write_name(&self.result);
        self.proof.write_canonical(encoder);
        match &self.semantic {
            None => encoder.write_u8(0),
            Some(SemanticArityCert::FunctionTypeArityCert) => encoder.write_u8(1),
            Some(SemanticArityCert::ItselfArityCert) => encoder.write_u8(2),
            Some(SemanticArityCert::FreshNonemptyTyconCert { tycon, arity }) => {
                encoder.write_u8(3);
                encoder.write_name(tycon);
                encoder.write_u64(*arity as u64);
            },
        }
    }

    pub(crate) fn check_in_parent(&self, parent: &TrustedTheory) -> Result<(), KernelError> {
        crate::Signature::validate_constructor_arity(&self.tycon, self.arg_sorts.len())?;
        if self.parent != parent.id()
            || !parent.signature().has_class(&self.result)
            || parent.signature().type_constructor_arity(&self.tycon) != Some(self.arg_sorts.len())
        {
            return Err(KernelError::UnknownClassEvidence);
        }
        // An installed arity is an immutable proof certificate, not an
        // idempotent graph edge. Reject repeat registration before replaying
        // it or publishing a redundant owner.
        if parent.find_arity_certificate(&self.tycon, &self.result).is_some() {
            return Err(KernelError::DuplicateDeclaration { name: self.tycon.clone() });
        }
        for sort in &self.arg_sorts {
            parent.signature().validate_sort(sort)?;
        }
        if let Some(model) = &self.semantic {
            model.check_in_parent(parent)?;
            if model.tycon() != self.tycon
                || self.result != Name::from("HOL.type")
                || self.arg_sorts.iter().any(|sort| *sort != Sort::hol_type())
            {
                return Err(KernelError::UnknownClassEvidence);
            }
        }
        let arguments: Vec<_> = self
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| {
                Ty::tvar(Name::from(format!("arity_arg_{index}")), 0, sort.clone())
            })
            .collect();
        let ty = Ty::apply(self.tycon.clone(), arguments)?;
        check_candidate(parent, &ty, &self.result, &self.proof, &[], self.semantic.is_some())
    }
}

/// A class relation replayed as the exact schematic implication from an
/// annotated subclass atom; it is not authorized by a graph reachability query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassRelCert {
    pub(crate) parent: TheoryId,
    pub(crate) lower: Name,
    pub(crate) upper: Name,
    pub(crate) proof: OfClassCandidate,
}

impl ClassRelCert {
    pub fn lower(&self) -> &Name {
        &self.lower
    }
    pub fn upper(&self) -> &Name {
        &self.upper
    }
    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_name(&self.lower);
        encoder.write_name(&self.upper);
        self.parent.write_canonical(encoder);
        self.proof.write_canonical(encoder);
    }

    pub(crate) fn check_in_parent(&self, parent: &TrustedTheory) -> Result<(), KernelError> {
        if self.parent != parent.id()
            || self.lower == self.upper
            || !parent.signature().has_class(&self.lower)
            || !parent.signature().has_class(&self.upper)
        {
            return Err(KernelError::UnknownClassEvidence);
        }
        // The precheck graph may deduplicate an edge, but its owner proof is
        // installed exactly once. Previously accepted ancestors remain valid.
        if parent.find_class_relation(&self.lower, &self.upper).is_some() {
            return Err(KernelError::DuplicateDeclaration { name: self.lower.clone() });
        }
        let atom = Ty::tvar("classrel_arg", 0, Sort::new(vec![self.lower.clone()]));
        check_candidate(parent, &atom, &self.upper, &self.proof, &[], false)
    }
}

/// The scope belongs to one plan and is private to its checker. In ordinary
/// closed proofs it is empty; it is never real theorem H.
pub(crate) fn check_candidate(
    owner: &TrustedTheory,
    ty: &Ty,
    class: &Name,
    candidate: &OfClassCandidate,
    premises: &[(Ty, Name)],
    is_initial_semantic_root: bool,
) -> Result<(), KernelError> {
    owner.signature().validate_type(ty)?;
    if !owner.signature().has_class(class) {
        return Err(KernelError::UnknownClassEvidence);
    }
    match candidate {
        OfClassCandidate::AnnotatedAtomLeaf => {
            if ty.atomic_sort().is_some_and(|sort| sort.classes().contains(class)) {
                Ok(())
            } else {
                Err(KernelError::UnknownClassEvidence)
            }
        },
        OfClassCandidate::ExportPremiseLeaf { slot } => {
            if premises.get(*slot) == Some(&(ty.clone(), class.clone())) {
                Ok(())
            } else {
                Err(KernelError::UnknownClassEvidence)
            }
        },
        OfClassCandidate::ClassWeaken { lower, premise } => {
            let cert =
                owner.find_class_relation(lower, class).ok_or(KernelError::UnknownClassEvidence)?;
            cert.check_in_parent(
                owner.find_owner(cert.parent).ok_or(KernelError::UnknownClassEvidence)?,
            )?;
            check_candidate(owner, ty, lower, premise, premises, false)
        },
        OfClassCandidate::TypeConstructor { arguments } => {
            check_constructor(owner, ty, class, arguments, premises, None)
        },
        OfClassCandidate::SemanticArity { arguments } => {
            if !is_initial_semantic_root {
                return Err(KernelError::UnknownClassEvidence);
            }
            let (name, _) = ty.dest_type().ok_or(KernelError::UnknownClassEvidence)?;
            let model = match name.as_str() {
                "fun" => SemanticArityCert::FunctionTypeArityCert,
                "itself" => SemanticArityCert::ItselfArityCert,
                _ => SemanticArityCert::FreshNonemptyTyconCert {
                    tycon: name.clone(),
                    arity: arguments.len(),
                },
            };
            model.check_in_parent(owner)?;
            check_constructor(owner, ty, class, arguments, premises, Some(&model))
        },
    }
}

fn check_constructor(
    owner: &TrustedTheory,
    ty: &Ty,
    class: &Name,
    arguments: &[Vec<OfClassCandidate>],
    premises: &[(Ty, Name)],
    semantic: Option<&SemanticArityCert>,
) -> Result<(), KernelError> {
    let (name, args) = ty.dest_type().ok_or(KernelError::UnknownClassEvidence)?;
    let sorts = match semantic {
        Some(model) if &model.tycon() == name && class == &Name::from("HOL.type") => {
            vec![Sort::hol_type(); model.arity()]
        },
        Some(_) => return Err(KernelError::UnknownClassEvidence),
        None => {
            let cert = owner
                .find_arity_certificate(name, class)
                .ok_or(KernelError::UnknownClassEvidence)?;
            let parent = owner.find_owner(cert.parent).ok_or(KernelError::UnknownClassEvidence)?;
            cert.check_in_parent(parent)?;
            cert.arg_sorts.clone()
        },
    };
    if args.len() != sorts.len() || arguments.len() != args.len() {
        return Err(KernelError::UnknownClassEvidence);
    }
    for ((arg, sort), evidence) in args.iter().zip(&sorts).zip(arguments) {
        if evidence.len() != sort.classes().len() {
            return Err(KernelError::UnknownClassEvidence);
        }
        for (required, proof) in sort.classes().iter().zip(evidence) {
            check_candidate(owner, arg, required, proof, premises, false)?;
        }
    }
    Ok(())
}

/// Check a closed class judgment; only the kernel can create the result.
pub fn prove_of_class(
    owner: &TrustedTheory,
    ty: Ty,
    class: Name,
    candidate: OfClassCandidate,
) -> Result<ClosedOfClassProof, KernelError> {
    check_candidate(owner, &ty, &class, &candidate, &[], false)?;
    let mut dependencies = DependencySet::empty();
    collect_dependencies(
        owner,
        &ty,
        &class,
        &candidate,
        &[],
        &mut BTreeSet::new(),
        &mut dependencies,
    )?;
    Ok(ClosedOfClassProof { owner: owner.id(), ty, class, candidate, dependencies })
}

fn collect_dependencies(
    owner: &TrustedTheory,
    ty: &Ty,
    class: &Name,
    proof: &OfClassCandidate,
    premises: &[(Ty, Name)],
    used_slots: &mut BTreeSet<usize>,
    dependencies: &mut DependencySet,
) -> Result<(), KernelError> {
    match proof {
        OfClassCandidate::AnnotatedAtomLeaf => Ok(()),
        OfClassCandidate::ExportPremiseLeaf { slot } => {
            if premises.get(*slot) != Some(&(ty.clone(), class.clone())) {
                return Err(KernelError::UnknownClassEvidence);
            }
            used_slots.insert(*slot);
            Ok(())
        },
        OfClassCandidate::ClassWeaken { lower, premise } => {
            dependencies.insert_class(
                owner
                    .find_class_relation_installation(lower, class)
                    .ok_or(KernelError::UnknownClassEvidence)?,
            );
            collect_dependencies(owner, ty, lower, premise, premises, used_slots, dependencies)
        },
        OfClassCandidate::TypeConstructor { arguments } => {
            let (name, args) = ty.dest_type().ok_or(KernelError::UnknownClassEvidence)?;
            let cert = owner
                .find_arity_certificate(name, class)
                .ok_or(KernelError::UnknownClassEvidence)?;
            dependencies.insert_class(
                owner
                    .find_arity_installation(name, class)
                    .ok_or(KernelError::UnknownClassEvidence)?,
            );
            for ((arg, sort), evidence) in args.iter().zip(&cert.arg_sorts).zip(arguments) {
                for (required, subproof) in sort.classes().iter().zip(evidence) {
                    collect_dependencies(
                        owner,
                        arg,
                        required,
                        subproof,
                        premises,
                        used_slots,
                        dependencies,
                    )?;
                }
            }
            Ok(())
        },
        OfClassCandidate::SemanticArity { .. } => Err(KernelError::UnknownClassEvidence),
    }
}

/// Search is only a proof generator: success is independently replayed by the
/// goal-driven checker. It never treats `ClassAlgebra::has_type_sort` as proof.
pub(crate) fn derive_of_class(
    owner: &TrustedTheory,
    ty: &Ty,
    class: &Name,
) -> Result<ClosedOfClassProof, KernelError> {
    let candidate = derive_candidate(owner, ty, class, &[])?;
    prove_of_class(owner, ty.clone(), class.clone(), candidate)
}

pub(crate) fn derive_scoped_of_class(
    owner: &TrustedTheory,
    ty: &Ty,
    class: &Name,
    premises: &[(Ty, Name)],
) -> Result<ScopedOfClassEvidence, KernelError> {
    let candidate = derive_candidate(owner, ty, class, premises)?;
    check_candidate(owner, ty, class, &candidate, premises, false)?;
    let mut used_slots = BTreeSet::new();
    let mut dependencies = DependencySet::empty();
    collect_dependencies(
        owner,
        ty,
        class,
        &candidate,
        premises,
        &mut used_slots,
        &mut dependencies,
    )?;
    Ok(ScopedOfClassEvidence { used_slots, dependencies })
}

/// Replay the declared sort obligations of the actual scheme substitution,
/// including concrete instances whose types contain no annotated atoms.
pub(crate) fn certify_const_scheme_evidence(
    owner: &TrustedTheory,
    name: &Name,
    actual: &Ty,
    premises: &[(Ty, Name)],
) -> Result<ScopedOfClassEvidence, KernelError> {
    let instance = owner.signature().certify_const_instance(name, actual)?;
    let mut evidence =
        ScopedOfClassEvidence { used_slots: BTreeSet::new(), dependencies: DependencySet::empty() };
    for (parameter, ty) in instance.iter() {
        for class in parameter.sort.classes() {
            let checked = derive_scoped_of_class(owner, ty, class, premises)?;
            evidence.used_slots.extend(checked.used_slots);
            evidence.dependencies.extend(&checked.dependencies);
        }
    }
    Ok(evidence)
}

/// Recertify an individual constant occurrence against its actual source type
/// and exact erased type. Each original sort constraint needs scoped evidence;
/// this function alone cannot create a theorem or establish binder scope.
pub(crate) fn certify_sort_erased_const(
    owner: &TrustedTheory,
    name: &Name,
    source: &Ty,
    erased: &Ty,
    replacements: &BTreeMap<Ty, Ty>,
    premises: &[(Ty, Name)],
) -> Result<ScopedOfClassEvidence, KernelError> {
    let mut evidence = certify_const_scheme_evidence(owner, name, source, premises)?;
    // A monomorphic schematic annotation is an exact signature type, not an
    // implicit polymorphic scheme. Erasing it would grant new constant instances.
    if matches!(owner.signature().get_const(name), Some(crate::ConstScheme::Monomorphic(_)))
        && source != erased
    {
        return Err(KernelError::TypeMismatch { expected: source.clone(), actual: erased.clone() });
    }
    let expected = source.rewrite_atomic_types(replacements)?;
    if &expected != erased {
        return Err(KernelError::TypeMismatch { expected, actual: erased.clone() });
    }
    let mut atoms = BTreeSet::new();
    source.for_each_type_atom(&mut |name, index, sort| {
        atoms.insert(match index {
            Some(index) => Ty::tvar(name.clone(), index, sort.clone()),
            None => Ty::tfree(name.clone(), sort.clone()),
        });
    });
    for atom in atoms {
        let target = atom.rewrite_atomic_types(replacements)?;
        for class in atom.atomic_sort().ok_or(KernelError::UnknownClassEvidence)?.classes() {
            let checked = derive_scoped_of_class(owner, &target, class, premises)?;
            evidence.used_slots.extend(checked.used_slots);
            evidence.dependencies.extend(&checked.dependencies);
        }
    }
    Ok(evidence)
}

fn derive_candidate(
    owner: &TrustedTheory,
    ty: &Ty,
    class: &Name,
    premises: &[(Ty, Name)],
) -> Result<OfClassCandidate, KernelError> {
    if ty.atomic_sort().is_some_and(|sort| sort.classes().contains(class)) {
        return Ok(OfClassCandidate::AnnotatedAtomLeaf);
    }
    if let Some(slot) =
        premises.iter().position(|(expected, required)| expected == ty && required == class)
    {
        return Ok(OfClassCandidate::ExportPremiseLeaf { slot });
    }
    if let Some(sort) = ty.atomic_sort() {
        for lower in sort.classes() {
            if owner.find_class_relation(lower, class).is_some() {
                return Ok(OfClassCandidate::ClassWeaken {
                    lower: lower.clone(),
                    premise: Box::new(OfClassCandidate::AnnotatedAtomLeaf),
                });
            }
        }
        for lower in owner.signature().declared_classes() {
            if owner.find_class_relation(lower, class).is_none() {
                continue;
            }
            if let Ok(premise) = derive_candidate(owner, ty, lower, premises) {
                return Ok(OfClassCandidate::ClassWeaken {
                    lower: lower.clone(),
                    premise: Box::new(premise),
                });
            }
        }
        return Err(KernelError::UnknownClassEvidence);
    }
    let (name, args) = ty.dest_type().ok_or(KernelError::UnknownClassEvidence)?;
    if let Some(cert) = owner.find_arity_certificate(name, class) {
        let arguments = args
            .iter()
            .zip(&cert.arg_sorts)
            .map(|(arg, sort)| {
                sort.classes()
                    .iter()
                    .map(|required| derive_candidate(owner, arg, required, premises))
                    .collect::<Result<Vec<_>, KernelError>>()
            })
            .collect::<Result<Vec<_>, KernelError>>();
        // Candidate search must try a weaker certified result if the direct
        // arity's arguments are unavailable under this exact export scope.
        if let Ok(arguments) = arguments {
            return Ok(OfClassCandidate::TypeConstructor { arguments });
        }
    }
    for lower in owner.signature().declared_classes() {
        if owner.find_class_relation(lower, class).is_none() {
            continue;
        }
        if let Ok(premise) = derive_candidate(owner, ty, lower, premises) {
            return Ok(OfClassCandidate::ClassWeaken {
                lower: lower.clone(),
                premise: Box::new(premise),
            });
        }
    }
    Err(KernelError::UnknownClassEvidence)
}

pub(crate) fn find_class_witness(
    owner: &TrustedTheory,
    required: &Sort,
    present: &BTreeSet<Ty>,
) -> Option<Ty> {
    if let Some(atom) = present
        .iter()
        .filter(|ty| {
            required.classes().iter().all(|class| derive_of_class(owner, ty, class).is_ok())
        })
        .min_by(|left, right| left.cmp_term_ord(right))
    {
        return Some(atom.clone());
    }
    find_ground_witness(owner, required, &mut Vec::new())
}

fn find_ground_witness(owner: &TrustedTheory, required: &Sort, path: &mut Vec<Sort>) -> Option<Ty> {
    if required.classes().is_empty() {
        return Some(Ty::prop());
    }
    for (name, arity) in owner.signature().type_constructors() {
        if let Some(result) = ground_constructor(owner, required, name, *arity, path) {
            return Some(result);
        }
    }
    None
}
fn find_class_arity<'a>(
    owner: &'a TrustedTheory,
    tycon: &Name,
    class: &Name,
) -> Option<&'a ArityCert> {
    owner.find_arity_certificate(tycon, class).or_else(|| {
        owner.signature().declared_classes().find_map(|lower| {
            owner
                .find_class_relation(lower, class)
                .and_then(|_| owner.find_arity_certificate(tycon, lower))
        })
    })
}

fn ground_constructor(
    owner: &TrustedTheory,
    required: &Sort,
    tycon: &Name,
    arity: usize,
    path: &mut Vec<Sort>,
) -> Option<Ty> {
    let mut domains = vec![Vec::new(); arity];
    for class in required.classes() {
        let cert = find_class_arity(owner, tycon, class)?;
        if cert.arg_sorts.len() != arity {
            return None;
        }
        for (domain, sort) in domains.iter_mut().zip(&cert.arg_sorts) {
            domain.extend_from_slice(sort.classes());
        }
    }
    let domains: Vec<_> = domains.into_iter().map(Sort::new).collect();
    if domains.iter().any(|domain| {
        owner.signature().is_sort_le(domain, required)
            || path.iter().any(|ancestor| owner.signature().is_sort_le(domain, ancestor))
    }) {
        return None;
    }
    path.push(required.clone());
    let args = domains
        .iter()
        .map(|domain| find_ground_witness(owner, domain, path))
        .collect::<Option<Vec<_>>>();
    path.truncate(path.len() - 1);
    let args = args?;
    let ty = Ty::apply(tycon.clone(), args).ok()?;
    required.classes().iter().all(|class| derive_of_class(owner, &ty, class).is_ok()).then_some(ty)
}

pub(crate) fn replay_solve_constraints(
    owner: &TrustedTheory,
    premise: &KernelThm,
    proofs: &[ClosedOfClassProof],
) -> Result<KernelThm, KernelError> {
    if premise.context() != owner.stamp() {
        return Err(KernelError::MixedContext {
            expected: Box::new(owner.stamp()),
            actual: Box::new(premise.context()),
        });
    }
    for proof in proofs {
        proof.replay(owner)?;
    }
    let payload = premise.payload().discharge_constraints(proofs)?;
    Ok(KernelThm::new_with_payload(
        premise.hyps().to_vec(),
        premise.prop().clone(),
        payload,
        Derivation::SolveConstraints {
            premise: Box::new(premise.clone()),
            proofs: proofs.to_vec(),
        },
    ))
}

pub(crate) fn replay_of_class(
    owner: &TrustedTheory,
    proof: &ClosedOfClassProof,
) -> Result<ClosedThm, KernelError> {
    proof.replay(owner)?;
    let tag_type = Ty::apply("itself", vec![proof.ty().clone()])?;
    let class_constant = Name::from(format!("{}_class", proof.class()));
    let proposition = RawTerm::app(
        RawTerm::const_(class_constant, Ty::arrow(tag_type.clone(), Ty::prop())),
        RawTerm::const_("Pure.type", tag_type),
    );
    let context = ProofContext::new(owner.snapshot().clone());
    let proposition = context.certify_prop(proposition)?;
    KernelThm::new(vec![], proposition, Derivation::OfClass { proof: proof.clone() }).try_close()
}

impl KernelRules {
    /// Materialize only a closed, owner-checked OFCLASS judgment. Neither a
    /// class graph edge nor a caller-supplied proposition creates this theorem.
    pub fn of_class(
        owner: &TrustedTheory,
        proof: &ClosedOfClassProof,
    ) -> Result<ClosedThm, KernelError> {
        replay_of_class(owner, proof)
    }

    /// Discharge every existing `(T,S)` in order. Proof search produces
    /// candidates only; replay checks each candidate against its exact owner.
    pub fn solve_constraints(
        owner: &TrustedTheory,
        theorem: &KernelThm,
    ) -> Result<KernelThm, KernelError> {
        let context = ProofContext::new(owner.snapshot().clone());
        let mut dependencies = crate::DependencySet::empty();
        crate::invariant::replay_source_in(owner, &context, theorem, &mut dependencies)?;
        let proofs = theorem
            .payload()
            .sort_obligations()
            .iter()
            .flat_map(|(ty, sort)| sort.classes().iter().map(move |class| (ty, class)))
            .map(|(ty, class)| derive_of_class(owner, ty, class))
            .collect::<Result<Vec<_>, KernelError>>()?;
        replay_solve_constraints(owner, theorem, &proofs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EmptyClassDeclCert, Signature};

    #[test]
    fn semantic_arity_tampered_proof_rejects_certificate_replay() {
        let root = TrustedTheory::root(
            "TamperedArity",
            Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
        );
        let declared = root.declare_fresh_nonempty_tycon("W", 0).unwrap();
        let installed = declared
            .install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
                tycon: "W".into(),
                arity: 0,
            })
            .unwrap();
        let mut cert = installed
            .find_arity_certificate(&Name::from("W"), &Name::from("HOL.type"))
            .unwrap()
            .clone();
        cert.proof = OfClassCandidate::AnnotatedAtomLeaf;
        assert!(matches!(cert.check_in_parent(&declared), Err(KernelError::UnknownClassEvidence),));
    }
}
