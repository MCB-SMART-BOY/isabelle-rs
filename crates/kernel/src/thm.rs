use std::collections::BTreeSet;

use super::{
    CProp, ContextStamp, Derivation, KernelError, Sort, Term, TheoryId, obligations::ProofPayload,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelThm {
    context: ContextStamp,
    hyps: Vec<CProp>,
    prop: CProp,
    derivation: Derivation,
    payload: ProofPayload,
    max_index: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenThm(KernelThm);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedThm(KernelThm);

impl KernelThm {
    pub(crate) fn new(hyps: Vec<CProp>, prop: CProp, derivation: Derivation) -> Self {
        let payload = ProofPayload::for_derivation(&hyps, &prop, &derivation);
        Self::new_with_payload(hyps, prop, payload, derivation)
    }

    pub(crate) fn new_with_payload(
        hyps: Vec<CProp>,
        prop: CProp,
        payload: ProofPayload,
        derivation: Derivation,
    ) -> Self {
        let context = prop.context();
        let mut max_index = payload.max_var_index();
        ProofPayload::include_term_index(prop.term(), &mut max_index);
        for hyp in &hyps {
            ProofPayload::include_term_index(hyp.term(), &mut max_index);
        }
        if let Derivation::AdjustMaxIndex { requested, .. } = &derivation {
            max_index = max_index.max(*requested);
            return Self { context, hyps, prop, payload, derivation, max_index };
        }
        if matches!(derivation, Derivation::Generalize { .. }) {
            return Self { context, hyps, prop, payload, derivation, max_index };
        }
        derivation.for_each_premise(&mut |premise| {
            max_index = max_index.max(premise.max_var_index());
        });
        if let Derivation::TheoremRef { theorem } = &derivation {
            max_index = max_index.max(theorem.as_kernel().max_var_index());
        }
        derivation.for_each_certified_term(&mut |operand| {
            max_index = max_index.max(operand.max_var_index());
        });
        Self { context, hyps, prop, payload, derivation, max_index }
    }

    pub fn hyps(&self) -> &[CProp] {
        &self.hyps
    }

    pub fn prop(&self) -> &CProp {
        &self.prop
    }
    /// Exact sort hypotheses retained by checked derivation and export.
    /// This projection never grants theorem authority.
    pub fn shyps(&self) -> &BTreeSet<Sort> {
        self.payload.shyps()
    }

    pub fn derivation(&self) -> &Derivation {
        &self.derivation
    }
    pub(crate) fn payload(&self) -> &ProofPayload {
        &self.payload
    }

    pub fn context(&self) -> ContextStamp {
        self.context
    }

    /// Theory snapshot in which this theorem was proved.
    pub fn proved_in(&self) -> TheoryId {
        self.context.theory()
    }

    pub fn is_open(&self) -> bool {
        !self.hyps.is_empty()
    }

    /// Checked schematic index bound, including indices no longer present
    /// after an inference. `None` is Isabelle's `~1`.
    pub fn max_var_index(&self) -> Option<usize> {
        self.max_index
    }

    pub(crate) fn observed_max_var_index(&self) -> Option<usize> {
        let mut observed = self.payload.max_var_index();
        ProofPayload::include_term_index(self.prop.term(), &mut observed);
        for hyp in &self.hyps {
            ProofPayload::include_term_index(hyp.term(), &mut observed);
        }
        observed
    }

    pub fn try_close(self) -> Result<ClosedThm, KernelError> {
        if self.context.has_local_type_scope() {
            return Err(KernelError::LocalTypeScopeEscape { context: Box::new(self.context) });
        }
        if !self.hyps.is_empty() {
            return Err(KernelError::Invariant("open theorem cannot become ClosedThm".into()));
        }
        if self.max_index < self.observed_max_var_index() {
            return Err(KernelError::Invariant(
                "theorem max index is smaller than an actual payload index".into(),
            ));
        }
        self.payload.validate_closed(&self.prop, &self.hyps)?;
        Ok(ClosedThm(self))
    }
}

impl OpenThm {
    pub(crate) fn new(inner: KernelThm) -> Self {
        debug_assert!(inner.is_open());
        OpenThm(inner)
    }

    pub fn as_kernel(&self) -> &KernelThm {
        &self.0
    }

    pub fn context(&self) -> ContextStamp {
        self.0.context()
    }

    pub fn into_kernel(self) -> KernelThm {
        self.0
    }
}

impl ClosedThm {
    pub(crate) fn new(inner: KernelThm) -> Self {
        debug_assert!(!inner.is_open());
        ClosedThm(inner)
    }

    #[cfg(test)]
    pub(crate) fn from_kernel_unchecked_for_test(inner: KernelThm) -> Self {
        ClosedThm(inner)
    }

    pub fn as_kernel(&self) -> &KernelThm {
        &self.0
    }

    pub fn context(&self) -> ContextStamp {
        self.0.context()
    }

    pub fn into_kernel(self) -> KernelThm {
        self.0
    }
}

pub(crate) fn union_hyps(left: &[CProp], right: &[CProp]) -> Vec<CProp> {
    let mut out = left.to_vec();
    for hyp in right {
        if !out.iter().any(|existing| existing.term().alpha_eq(hyp.term())) {
            out.push(hyp.clone());
        }
    }
    out
}

pub(crate) fn remove_hyp(hyps: &[CProp], assumption: &CProp) -> Vec<CProp> {
    hyps.iter().filter(|hyp| !hyp.term().alpha_eq(assumption.term())).cloned().collect()
}

pub(crate) fn prop_from_term(term: Term, context: ContextStamp) -> CProp {
    CProp::from_checked_term(term, context)
}

#[cfg(test)]
mod tests {
    use crate::{
        CProp, Derivation, InstEntry, KernelError, KernelRules, KernelThm, ProofContext, RawTerm,
        Signature, Term, TheorySnapshot, Ty, invariant::check_kernel_thm,
    };
    use std::collections::BTreeSet;

    #[test]
    fn replay_rejects_payload_forgery_even_when_proposition_matches() {
        use crate::{Sort, TrustedTheory, TypeInstantiation, TypeVarId, accept_closed_theorem};
        use std::collections::BTreeMap;

        let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let owner = TrustedTheory::root("PayloadForgery", signature);
        let context = ProofContext::new(owner.snapshot().clone());
        let alpha = Ty::tvar("a", 0, Sort::empty());
        let source =
            KernelRules::reflexive(context.certify_term(RawTerm::var("x", 0, alpha)).unwrap());
        let type_inst = TypeInstantiation::try_new(BTreeMap::from([(
            TypeVarId::new("a", 0, Sort::empty()),
            Ty::prop(),
        )]))
        .unwrap();
        let constant = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
        let subst = InstEntry::new("x", 0, Ty::prop(), constant);
        let genuine =
            KernelRules::instantiate(&context, source.as_kernel(), &type_inst, &[subst]).unwrap();
        let fake_payload = crate::obligations::ProofPayload::from_statement(genuine.prop(), &[]);
        let forged = KernelThm::new_with_payload(
            vec![],
            genuine.prop().clone(),
            fake_payload,
            genuine.derivation().clone(),
        );
        let candidate = forged.try_close().unwrap();
        assert!(matches!(
            accept_closed_theorem(&owner, "fake", candidate),
            Err(KernelError::AcceptanceReplayMismatch)
        ));
    }

    #[test]
    fn max_index_instantiation_retains_then_adjusts_checked_upper_bound() {
        let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let owner = crate::TrustedTheory::root("MaxIndex", signature);
        let context = ProofContext::new(owner.snapshot().clone());
        let source =
            KernelRules::reflexive(context.certify_term(RawTerm::var("x", 5, Ty::prop())).unwrap());
        let replacement = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
        let substituted = KernelRules::instantiate(
            &context,
            source.as_kernel(),
            &crate::TypeInstantiation::empty(),
            &[InstEntry::new("x", 5, Ty::prop(), replacement)],
        )
        .unwrap();
        assert_eq!(substituted.observed_max_var_index(), None);
        assert_eq!(substituted.max_var_index(), Some(5));
        let adjusted = KernelRules::adjust_max_index(&substituted, None);
        assert_eq!(adjusted.max_var_index(), None);
        check_kernel_thm(&adjusted).unwrap();
        crate::accept_closed_theorem(&owner, "adjusted", adjusted.try_close().unwrap()).unwrap();
    }

    #[test]
    fn max_index_tampered_metadata_is_rejected_by_replay() {
        let context = ctx_with_props(&["P"]);
        let source =
            KernelRules::reflexive(context.certify_term(RawTerm::var("x", 4, Ty::prop())).unwrap());
        let mut below_actual = source.as_kernel().clone();
        below_actual.max_index = Some(3);
        assert!(matches!(below_actual.try_close(), Err(KernelError::Invariant(_))));

        let mut forged = source.into_kernel();
        forged.max_index = Some(8);
        assert!(matches!(check_kernel_thm(&forged), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn transfer_committed_ancestor_replays_in_target_owner() {
        let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let ancestor = crate::TrustedTheory::root("Ancestor", signature);
        let context = ProofContext::new(ancestor.snapshot().clone());
        let source =
            KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap());
        let target = ancestor.begin_child("Target");
        let transported = KernelRules::transfer(&target, source.as_kernel()).unwrap();
        assert_eq!(transported.context(), target.stamp());
        assert_eq!(transported.prop().term(), source.as_kernel().prop().term());
        let (_, accepted) =
            crate::accept_closed_theorem(&target, "transported", transported.try_close().unwrap())
                .unwrap();
        assert_eq!(accepted.proved_in(), target.id());
    }

    #[test]
    fn transfer_sibling_and_altered_source_are_rejected() {
        let signature = Signature::new()
            .extend_const("P", Ty::prop())
            .unwrap()
            .extend_const("Q", Ty::prop())
            .unwrap();
        let root = crate::TrustedTheory::root("Root", signature);
        let sibling = root.begin_child("Sibling");
        let source_owner = root.begin_child("Source");
        let context = ProofContext::new(source_owner.snapshot().clone());
        let source =
            KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap());
        assert!(matches!(
            KernelRules::transfer(&sibling, source.as_kernel()),
            Err(KernelError::UnknownTheoremDependency),
        ));
        let mut altered = source.into_kernel();
        altered.prop = context
            .certify_prop(RawTerm::eq(
                RawTerm::const_("Q", Ty::prop()),
                RawTerm::const_("Q", Ty::prop()),
            ))
            .unwrap();
        let destination = source_owner.begin_child("Destination");
        assert!(matches!(
            KernelRules::transfer(&destination, &altered),
            Err(KernelError::AcceptanceReplayMismatch),
        ));
    }

    #[test]
    fn tampered_theorem_fails_invariant() {
        let ctx = ctx_with_props(&["A", "B"]);
        let a = ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
        let b = ctx.certify_prop(RawTerm::const_("B", Ty::prop())).unwrap();
        let bad = KernelThm::new(vec![], a, Derivation::Assume { prop: b });

        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn hypothesis_type_only_schematic_variable_replay_rejects() {
        let alpha = Ty::tvar("'a", 0, crate::Sort::hol_type());
        let signature = Signature::new()
            .install_empty_class(crate::EmptyClassDeclCert::hol_type())
            .unwrap()
            .extend_const("c", alpha.clone())
            .unwrap();
        let context = ProofContext::new(TheorySnapshot::root("T", signature));
        let constant = RawTerm::const_("c", alpha);
        let proposition = context.certify_prop(RawTerm::eq(constant.clone(), constant)).unwrap();
        assert_eq!(KernelRules::assume(proposition.clone()), Err(KernelError::SchematicHypothesis));
        let forged = KernelThm::new(
            vec![proposition.clone()],
            proposition.clone(),
            Derivation::Assume { prop: proposition },
        );
        assert_eq!(check_kernel_thm(&forged), Err(KernelError::SchematicHypothesis));
    }

    #[test]
    fn hypothesis_term_schematic_variable_replay_rejects() {
        let context = ctx_with_props(&[]);
        let proposition = context.certify_prop(RawTerm::var("P", 0, Ty::prop())).unwrap();
        assert_eq!(KernelRules::assume(proposition.clone()), Err(KernelError::SchematicHypothesis));
        let forged = KernelThm::new(
            vec![proposition.clone()],
            proposition.clone(),
            Derivation::Assume { prop: proposition },
        );
        assert_eq!(check_kernel_thm(&forged), Err(KernelError::SchematicHypothesis));
    }

    fn ty(name: &str) -> Ty {
        Ty::base(name).unwrap()
    }

    fn ctx_with_nat_consts(names: &[&str]) -> ProofContext {
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        for name in names {
            sig = sig.extend_const(*name, ty("nat")).unwrap();
        }
        ProofContext::new(TheorySnapshot::root("Test", sig))
    }

    fn ctx_with_props(names: &[&str]) -> ProofContext {
        let mut sig = Signature::new();
        for name in names {
            sig = sig.extend_const(*name, Ty::prop()).unwrap();
        }
        ProofContext::new(TheorySnapshot::root("Test", sig))
    }

    #[test]
    fn beta_conversion_tampered_prop_fails_invariant() {
        // Tamper: valid beta_conversion derivation but swapped proposition.
        let ctx = ctx_with_nat_consts(&["a"]);
        let redex = ctx
            .certify_term(RawTerm::app(
                RawTerm::abs("x", ty("nat"), RawTerm::bound(0)),
                RawTerm::const_("a", ty("nat")),
            ))
            .unwrap();
        let thm = KernelRules::beta_conversion(redex).unwrap();

        let wrong_prop = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::const_("a", ty("nat")),
                RawTerm::const_("a", ty("nat")),
            ))
            .unwrap();

        let bad = KernelThm::new(
            thm.as_kernel().hyps().to_vec(),
            wrong_prop,
            thm.as_kernel().derivation().clone(),
        );
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn beta_conversion_tampered_hyps_fails_invariant() {
        // Tamper: valid beta_conversion derivation but spurious hypothesis added.
        let ctx = ctx_with_nat_consts(&["a"]);
        let redex = ctx
            .certify_term(RawTerm::app(
                RawTerm::abs("x", ty("nat"), RawTerm::bound(0)),
                RawTerm::const_("a", ty("nat")),
            ))
            .unwrap();
        let thm = KernelRules::beta_conversion(redex).unwrap();

        let ctx_prop = ctx_with_props(&["B"]);
        let fake_hyp = ctx_prop.certify_prop(RawTerm::const_("B", Ty::prop())).unwrap();
        let bad = KernelThm::new(
            vec![fake_hyp],
            thm.as_kernel().prop().clone(),
            thm.as_kernel().derivation().clone(),
        );
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn forall_elim_tampered_prop_fails_invariant() {
        // Tamper: valid forall_elim derivation but wrong (non-instantiated) proposition.
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        let mut ctx = ProofContext::new(TheorySnapshot::root("Test", sig));
        ctx.declare_free("x", ty("nat"));

        let eq_prop = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::free("x", ty("nat")),
                RawTerm::const_("a", ty("nat")),
            ))
            .unwrap();
        let assumed = KernelRules::assume(eq_prop.clone()).unwrap().into_kernel();
        let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
        let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
        let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();

        let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
        let inst = KernelRules::forall_elim(&forall_thm, &a_term).unwrap();

        // Swap in the unreduced forall proposition as if no substitution happened.
        let bad = KernelThm::new(
            inst.hyps().to_vec(),
            forall_thm.prop().clone(), // wrong — still the forall, not the instantiated body
            inst.derivation().clone(),
        );
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn combination_tampered_prop_fails_invariant() {
        // Tamper: valid combination derivation but swapped application order
        // (g a == f b instead of f a == g b).
        let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("f", fn_ty.clone()).unwrap();
        sig = sig.extend_const("g", fn_ty.clone()).unwrap();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        sig = sig.extend_const("b", ty("nat")).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));

        let f_eq_g = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::const_("f", fn_ty.clone()),
                RawTerm::const_("g", fn_ty.clone()),
            ))
            .unwrap();
        let a_eq_b = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::const_("a", ty("nat")),
                RawTerm::const_("b", ty("nat")),
            ))
            .unwrap();

        let th_f = KernelRules::assume(f_eq_g).unwrap().into_kernel();
        let th_x = KernelRules::assume(a_eq_b).unwrap().into_kernel();
        let valid = KernelRules::combination(&th_f, &th_x).unwrap();

        // Tamper: swap f↔g and a↔b in the result (g a == f b instead of f a == g b).
        let bad_prop = crate::CProp::from_checked_term(
            crate::Term::mk_eq(
                crate::Term::App {
                    func: Box::new(crate::Term::Const { name: "g".into(), ty: fn_ty.clone() }),
                    arg: Box::new(crate::Term::Const { name: "a".into(), ty: ty("nat") }),
                    ty: ty("nat"),
                },
                crate::Term::App {
                    func: Box::new(crate::Term::Const { name: "f".into(), ty: fn_ty }),
                    arg: Box::new(crate::Term::Const { name: "b".into(), ty: ty("nat") }),
                    ty: ty("nat"),
                },
            )
            .unwrap(),
            valid.context(),
        );

        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn abstraction_tampered_prop_fails_invariant() {
        // Tamper: change the binder name in the result from x to y.
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        let mut ctx = ProofContext::new(TheorySnapshot::root("Test", sig));
        ctx.declare_free("x", ty("nat"));

        let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
        let refl = KernelRules::reflexive(a_term).into_kernel();
        let valid = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();
        // valid: |- (λx:nat. a) == (λx:nat. a)

        // Tamper: replace the result with (λy:nat. a) == (λy:nat. a) — different binder name.
        let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
        let bad_lhs = crate::Term::Abs {
            name: "y".into(),
            param_ty: ty("nat"),
            body: Box::new(crate::Term::Const { name: "a".into(), ty: ty("nat") }),
            ty: fn_ty.clone(),
        };
        let bad_rhs = crate::Term::Abs {
            name: "y".into(),
            param_ty: ty("nat"),
            body: Box::new(crate::Term::Const { name: "a".into(), ty: ty("nat") }),
            ty: fn_ty.clone(),
        };
        let bad_prop = crate::CProp::from_checked_term(
            crate::Term::mk_eq(bad_lhs, bad_rhs).unwrap(),
            valid.context(),
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn equal_intr_tampered_prop_fails_invariant() {
        // Tamper: valid equal_intr but swapped result (B == A instead of A == B).
        let mut sig = Signature::new();
        sig = sig.extend_const("A", Ty::prop()).unwrap();
        sig = sig.extend_const("B", Ty::prop()).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));

        let a_imp_b = ctx
            .certify_prop(RawTerm::imp(
                RawTerm::const_("A", Ty::prop()),
                RawTerm::const_("B", Ty::prop()),
            ))
            .unwrap();
        let b_imp_a = ctx
            .certify_prop(RawTerm::imp(
                RawTerm::const_("B", Ty::prop()),
                RawTerm::const_("A", Ty::prop()),
            ))
            .unwrap();

        let left = KernelRules::assume(a_imp_b).unwrap().into_kernel();
        let right = KernelRules::assume(b_imp_a).unwrap().into_kernel();
        let valid = KernelRules::equal_intr(&left, &right).unwrap();

        // Tamper: swap A and B in result (B == A instead of A == B).
        let bad_prop = crate::CProp::from_checked_term(
            crate::Term::mk_eq(
                crate::Term::Const { name: "B".into(), ty: Ty::prop() },
                crate::Term::Const { name: "A".into(), ty: Ty::prop() },
            )
            .unwrap(),
            valid.context(),
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn equal_elim_tampered_prop_fails_invariant() {
        // Tamper: valid equal_elim but wrong result (A instead of B).
        let mut sig = Signature::new();
        sig = sig.extend_const("A", Ty::prop()).unwrap();
        sig = sig.extend_const("B", Ty::prop()).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));

        let a_eq_b = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::const_("A", Ty::prop()),
                RawTerm::const_("B", Ty::prop()),
            ))
            .unwrap();
        let a_prop = ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();

        let eq_thm = KernelRules::assume(a_eq_b).unwrap().into_kernel();
        let minor = KernelRules::assume(a_prop).unwrap().into_kernel();
        let valid = KernelRules::equal_elim(&eq_thm, &minor).unwrap();

        // Tamper: return A instead of B.
        let bad_prop = crate::CProp::from_checked_term(
            crate::Term::Const { name: "A".into(), ty: Ty::prop() },
            valid.context(),
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn generalize_tampered_prop_fails_invariant() {
        // Tamper: valid generalize but wrong Var index in result.
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("a", Ty::base("nat").unwrap()).unwrap();
        let mut ctx = ProofContext::new(TheorySnapshot::root("Test", sig));
        ctx.declare_free("x", Ty::base("nat").unwrap());

        let _x_eq_x = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::free("x", Ty::base("nat").unwrap()),
                RawTerm::free("x", Ty::base("nat").unwrap()),
            ))
            .unwrap();
        let thm = KernelRules::reflexive(
            ctx.certify_term(RawTerm::free("x", Ty::base("nat").unwrap())).unwrap(),
        )
        .into_kernel();
        let valid =
            KernelRules::generalize(&thm, &BTreeSet::new(), &BTreeSet::from(["x".into()]), 0)
                .unwrap();

        // Tamper: use Var("x", 999, nat) instead of Var("x", 0, nat).
        let bad_prop = crate::CProp::from_checked_term(
            crate::Term::mk_eq(
                crate::Term::Var { name: "x".into(), index: 999, ty: Ty::base("nat").unwrap() },
                crate::Term::Var { name: "x".into(), index: 999, ty: Ty::base("nat").unwrap() },
            )
            .unwrap(),
            valid.context(),
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn generalize_replay_overflow_rejects_recorded_derivation() {
        let mut context = ProofContext::new(TheorySnapshot::root("Test", Signature::new()));
        context.declare_free("x_", Ty::prop());
        let term = context.certify_term(RawTerm::free("x_", Ty::prop())).unwrap();
        let premise = KernelRules::reflexive(term).into_kernel();
        let forged = KernelThm::new(
            Vec::new(),
            premise.prop().clone(),
            Derivation::Generalize {
                type_names: BTreeSet::new(),
                term_names: BTreeSet::from(["x_".into()]),
                source_frees: vec![("x_".into(), Ty::prop())],
                index: usize::MAX,
                premise: Box::new(premise),
            },
        );

        assert_eq!(
            check_kernel_thm(&forged),
            Err(KernelError::GeneralizeIndexOverflow { index: usize::MAX, offset: 1 })
        );
    }

    #[test]
    fn instantiate_rejects_bound_in_replacement_inline() {
        // Defense-in-depth: CTerm::new is kernel-internal and can create a CTerm
        // with Bound, but KernelRules::instantiate must still reject it via
        // contains_bound check.
        let mut sig = Signature::new().extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));

        let variable = ctx.certify_term(RawTerm::var("x", 0, ty("nat"))).unwrap();
        let thm = KernelRules::reflexive(variable).into_kernel();

        // Construct a CTerm containing Bound(0) — not possible through public
        // certification (ctx.certify_term rejects Bound), but an internal
        // kernel mistake could still produce one.
        let bad_cterm =
            crate::CTerm::new(crate::Term::Bound { index: 0, ty: ty("nat") }, ctx.stamp());
        let entry = InstEntry::new("x", 0, ty("nat"), bad_cterm);
        let err =
            KernelRules::instantiate(&ctx, &thm, &crate::TypeInstantiation::empty(), &[entry])
                .unwrap_err();
        assert!(matches!(err, KernelError::BoundInSubstitution));
    }

    #[test]
    fn instantiate_tampered_prop_fails_invariant() {
        // Tamper: valid instantiate but wrong replacement in result.
        let mut sig = Signature::new().extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        sig = sig.extend_const("b", ty("nat")).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));

        // Schematic variables are legal in conclusions of closed rules, not in H.
        let variable = ctx.certify_term(RawTerm::var("x", 0, ty("nat"))).unwrap();
        let thm = KernelRules::reflexive(variable).into_kernel();

        // Instantiate: Var("x", 0, nat) := b
        let b_cterm = ctx.certify_term(RawTerm::const_("b", ty("nat"))).unwrap();
        let entry = InstEntry::new("x", 0, ty("nat"), b_cterm);
        let valid =
            KernelRules::instantiate(&ctx, &thm, &crate::TypeInstantiation::empty(), &[entry])
                .unwrap();
        // Valid: b == b. Tamper: return a == a instead.
        let bad_prop = CProp::from_checked_term(
            Term::mk_eq(
                Term::Const { name: "a".into(), ty: ty("nat") },
                Term::Const { name: "a".into(), ty: ty("nat") },
            )
            .unwrap(),
            valid.context(),
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn resolution_replay_rejects_mixed_context_before_subgoal_matching() {
        let left_ctx = ctx_with_props(&["A"]);
        let right_ctx = ctx_with_props(&["A", "B"]);
        let left_a = left_ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
        let right_a = right_ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
        let rule = KernelRules::assume(left_a.clone()).unwrap().into_kernel();
        let goal_state = KernelRules::assume(right_a).unwrap().into_kernel();
        let tampered = KernelThm::new(
            vec![],
            left_a,
            Derivation::Resolve1Match {
                rule: Box::new(rule),
                goal_state: Box::new(goal_state),
                selected_subgoal_index: 0,
                subst: vec![],
            },
        );

        let error = check_kernel_thm(&tampered).unwrap_err();
        assert!(matches!(error, KernelError::MixedContext { .. }));
    }

    #[test]
    fn resolution_replay_rejects_mixed_substitution_context_before_shape_matching() {
        let parent = TheorySnapshot::root("Root", {
            let mut sig = Signature::new();
            sig = sig.extend_const("A", Ty::prop()).unwrap();
            sig
        });
        let left_ctx = ProofContext::new(parent.begin_child("Left"));
        let right_ctx = ProofContext::new(parent.begin_child("Right"));
        let left_a = left_ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
        let rule = KernelRules::assume(left_a.clone()).unwrap().into_kernel();
        let goal_state = KernelRules::assume(left_a.clone()).unwrap().into_kernel();
        let wrong_context_replacement =
            right_ctx.certify_term(RawTerm::const_("A", Ty::prop())).unwrap();
        let tampered = KernelThm::new(
            vec![],
            left_a,
            Derivation::Resolve1Match {
                rule: Box::new(rule),
                goal_state: Box::new(goal_state),
                selected_subgoal_index: 0,
                subst: vec![InstEntry::new("P", 0, Ty::prop(), wrong_context_replacement)],
            },
        );

        let error = check_kernel_thm(&tampered).unwrap_err();
        assert!(matches!(error, KernelError::MixedContext { .. }));
    }

    #[test]
    fn replay_rejects_mixed_premises_before_recursive_validation() {
        let left_ctx = ctx_with_props(&["A"]);
        let right_ctx = ctx_with_props(&["A", "B"]);
        let left_a = left_ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
        let right_a = right_ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
        let invalid_left =
            KernelThm::new(vec![], left_a.clone(), Derivation::Assume { prop: left_a.clone() });
        let valid_right = KernelRules::assume(right_a).unwrap().into_kernel();
        let tampered = KernelThm::new(
            vec![],
            left_a,
            Derivation::Transitive { left: Box::new(invalid_left), right: Box::new(valid_right) },
        );

        let error = check_kernel_thm(&tampered).unwrap_err();
        assert!(matches!(error, KernelError::MixedContext { .. }));
    }

    #[test]
    fn replay_rejects_mixed_instantiate_context_before_premise_validation() {
        let parent = TheorySnapshot::root("Root", {
            let mut sig = Signature::new();
            sig = sig.extend_const("A", Ty::prop()).unwrap();
            sig
        });
        let left_ctx = ProofContext::new(parent.begin_child("Left"));
        let right_ctx = ProofContext::new(parent.begin_child("Right"));
        let left_a = left_ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
        let invalid_premise =
            KernelThm::new(vec![], left_a.clone(), Derivation::Assume { prop: left_a.clone() });
        let wrong_context_replacement =
            right_ctx.certify_term(RawTerm::const_("A", Ty::prop())).unwrap();
        let tampered = KernelThm::new(
            vec![],
            left_a,
            Derivation::Instantiate {
                type_inst: crate::TypeInstantiation::empty(),
                subst: vec![InstEntry::new("P", 0, Ty::prop(), wrong_context_replacement)],
                premise: Box::new(invalid_premise),
            },
        );

        let error = check_kernel_thm(&tampered).unwrap_err();
        assert!(matches!(error, KernelError::MixedContext { .. }));
    }
}
