use super::{CProp, ContextStamp, Derivation, KernelError, Term, TheoryId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelThm {
    context: ContextStamp,
    hyps: Vec<CProp>,
    prop: CProp,
    derivation: Derivation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenThm(KernelThm);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedThm(KernelThm);

impl KernelThm {
    pub(crate) fn new(hyps: Vec<CProp>, prop: CProp, derivation: Derivation) -> Self {
        let context = prop.context();
        KernelThm { context, hyps, prop, derivation }
    }

    pub fn hyps(&self) -> &[CProp] {
        &self.hyps
    }

    pub fn prop(&self) -> &CProp {
        &self.prop
    }

    pub fn derivation(&self) -> &Derivation {
        &self.derivation
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

    /// Highest `Var` index across all hypotheses and the proposition.
    pub fn max_var_index(&self) -> Option<usize> {
        let mut max: Option<usize> = self.prop.term().max_var_index();
        for hyp in &self.hyps {
            if let Some(m) = hyp.term().max_var_index() {
                max = Some(max.map_or(m, |prev| prev.max(m)));
            }
        }
        max
    }

    pub fn try_close(self) -> Result<ClosedThm, KernelError> {
        if self.hyps.is_empty() {
            Ok(ClosedThm(self))
        } else {
            Err(KernelError::Invariant("open theorem cannot become ClosedThm".into()))
        }
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

pub(crate) fn remove_hyp(hyps: &[CProp], assumption: &CProp) -> Option<Vec<CProp>> {
    let mut removed = false;
    let mut out = Vec::with_capacity(hyps.len());
    for hyp in hyps {
        if !removed && hyp.term().alpha_eq(assumption.term()) {
            removed = true;
        } else {
            out.push(hyp.clone());
        }
    }
    removed.then_some(out)
}

pub(crate) fn prop_from_term(term: Term, context: ContextStamp) -> CProp {
    CProp::from_checked_term(term, context)
}

#[cfg(test)]
mod tests {
    use crate::{
        CProp, Derivation, InstEntry, KernelError, KernelRules, KernelThm, Name, ProofContext,
        RawTerm, Signature, Term, TheorySnapshot, Ty, invariant::check_kernel_thm,
    };

    #[test]
    fn tampered_theorem_fails_invariant() {
        let ctx = ctx_with_props(&["A", "B"]);
        let a = ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
        let b = ctx.certify_prop(RawTerm::const_("B", Ty::prop())).unwrap();
        let bad = KernelThm::new(vec![], a, Derivation::Assume { prop: b });

        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    fn ty(name: &str) -> Ty {
        Ty::base(name).unwrap()
    }

    fn ctx_with_nat_consts(names: &[&str]) -> ProofContext {
        let mut sig = Signature::new();
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
        sig = sig.extend_const("a", ty("nat")).unwrap();
        let mut ctx = ProofContext::new(TheorySnapshot::root("Test", sig));
        ctx.declare_free("x", ty("nat"));

        let eq_prop = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::free("x", ty("nat")),
                RawTerm::const_("a", ty("nat")),
            ))
            .unwrap();
        let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
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

        let th_f = KernelRules::assume(f_eq_g).into_kernel();
        let th_x = KernelRules::assume(a_eq_b).into_kernel();
        let valid = KernelRules::combination(&th_f, &th_x).unwrap();

        // Tamper: swap f↔g and a↔b in the result (g a == f b instead of f a == g b).
        let bad_prop = crate::CProp::from_checked_term(
            crate::Term::mk_eq(
                crate::Term::App {
                    func: Box::new(crate::Term::Const {
                        name: "g".into(),
                        ty: fn_ty.clone(),
                    }),
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

        let left = KernelRules::assume(a_imp_b).into_kernel();
        let right = KernelRules::assume(b_imp_a).into_kernel();
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

        let eq_thm = KernelRules::assume(a_eq_b).into_kernel();
        let minor = KernelRules::assume(a_prop).into_kernel();
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
        sig = sig.extend_const("a", Ty::base("nat").unwrap()).unwrap();
        let mut ctx = ProofContext::new(TheorySnapshot::root("Test", sig));
        ctx.declare_free("x", Ty::base("nat").unwrap());

        let x_eq_x = ctx
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
            KernelRules::generalize(&thm, &[("x".into(), Ty::base("nat").unwrap())]).unwrap();

        // Tamper: use Var("x", 999, nat) instead of Var("x", 0, nat).
        let bad_prop = crate::CProp::from_checked_term(
            crate::Term::mk_eq(
                crate::Term::Var {
                    name: "x".into(),
                    index: 999,
                    ty: Ty::base("nat").unwrap(),
                },
                crate::Term::Var {
                    name: "x".into(),
                    index: 999,
                    ty: Ty::base("nat").unwrap(),
                },
            )
            .unwrap(),
            valid.context(),
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn instantiate_rejects_bound_in_replacement_inline() {
        // Defense-in-depth: CTerm::new is kernel-internal and can create a CTerm
        // with Bound, but KernelRules::instantiate must still reject it via
        // contains_bound check.
        let mut sig = Signature::new();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));

        let raw_prop =
            RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
        let cprop = ctx.certify_prop(raw_prop).unwrap();
        let thm = KernelRules::assume(cprop).into_kernel();

        // Construct a CTerm containing Bound(0) — not possible through public
        // certification (ctx.certify_term rejects Bound), but an internal
        // kernel mistake could still produce one.
        let bad_cterm = crate::CTerm::new(
            crate::Term::Bound { index: 0, ty: ty("nat") },
            ctx.stamp(),
        );
        let entry = InstEntry::new("x", 0, ty("nat"), bad_cterm);
        let err = KernelRules::instantiate(&thm, &[entry]).unwrap_err();
        assert!(matches!(err, KernelError::BoundInSubstitution));
    }

    #[test]
    fn instantiate_tampered_prop_fails_invariant() {
        // Tamper: valid instantiate but wrong replacement in result.
        let mut sig = Signature::new();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        sig = sig.extend_const("b", ty("nat")).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));

        // Build: Var("x", 0, nat) == a |- Var("x", 0, nat) == a
        let raw_prop =
            RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
        let cprop = ctx.certify_prop(raw_prop).unwrap();
        let thm = KernelRules::assume(cprop).into_kernel();

        // Instantiate: Var("x", 0, nat) := b
        let b_cterm = ctx.certify_term(RawTerm::const_("b", ty("nat"))).unwrap();
        let entry = InstEntry::new("x", 0, ty("nat"), b_cterm);
        let valid = KernelRules::instantiate(&thm, &[entry]).unwrap();
        // valid: b == a |- b == a

        // Tamper: return a == a (Var still present — substitution not applied).
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
        let rule = KernelRules::assume(left_a.clone()).into_kernel();
        let goal_state = KernelRules::assume(right_a).into_kernel();
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
        let rule = KernelRules::assume(left_a.clone()).into_kernel();
        let goal_state = KernelRules::assume(left_a.clone()).into_kernel();
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
        let valid_right = KernelRules::assume(right_a).into_kernel();
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
                subst: vec![InstEntry::new("P", 0, Ty::prop(), wrong_context_replacement)],
                premise: Box::new(invalid_premise),
            },
        );

        let error = check_kernel_thm(&tampered).unwrap_err();
        assert!(matches!(error, KernelError::MixedContext { .. }));
    }
}
