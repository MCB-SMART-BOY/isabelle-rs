use super::{CProp, Derivation, KernelError, Term};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelThm {
    hyps: Vec<CProp>,
    prop: CProp,
    derivation: Derivation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenThm(KernelThm);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedThm(KernelThm);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustedTheorem(ClosedThm);

impl KernelThm {
    pub(in crate::kernel) fn new(hyps: Vec<CProp>, prop: CProp, derivation: Derivation) -> Self {
        KernelThm { hyps, prop, derivation }
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
    pub(in crate::kernel) fn new(inner: KernelThm) -> Self {
        debug_assert!(inner.is_open());
        OpenThm(inner)
    }

    pub fn as_kernel(&self) -> &KernelThm {
        &self.0
    }

    pub fn into_kernel(self) -> KernelThm {
        self.0
    }
}

impl ClosedThm {
    pub(in crate::kernel) fn new(inner: KernelThm) -> Self {
        debug_assert!(!inner.is_open());
        ClosedThm(inner)
    }

    pub fn as_kernel(&self) -> &KernelThm {
        &self.0
    }

    pub fn into_kernel(self) -> KernelThm {
        self.0
    }

    pub fn trust(self) -> Result<TrustedTheorem, KernelError> {
        super::invariant::check_kernel_thm(self.as_kernel())?;
        Ok(TrustedTheorem(self))
    }
}

impl TrustedTheorem {
    pub fn as_closed(&self) -> &ClosedThm {
        &self.0
    }

    pub fn prop(&self) -> &CProp {
        self.0.as_kernel().prop()
    }
}

pub(in crate::kernel) fn union_hyps(left: &[CProp], right: &[CProp]) -> Vec<CProp> {
    let mut out = left.to_vec();
    for hyp in right {
        if !out.iter().any(|existing| existing.term().alpha_eq(hyp.term())) {
            out.push(hyp.clone());
        }
    }
    out
}

pub(in crate::kernel) fn remove_hyp(hyps: &[CProp], assumption: &CProp) -> Option<Vec<CProp>> {
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

pub(in crate::kernel) fn prop_from_term(term: Term) -> CProp {
    CProp::from_checked_term(term)
}

#[cfg(test)]
mod tests {
    use crate::kernel::{
        CProp, CTerm, Derivation, InstEntry, KernelError, KernelRules, KernelThm, ProofContext,
        RawTerm, Signature, Term, Ty, invariant::check_kernel_thm,
    };

    #[test]
    fn tampered_theorem_fails_invariant() {
        let prop = Ty::prop();
        let bad = KernelThm::new(
            vec![],
            crate::kernel::CProp::from_checked_term(crate::kernel::Term::Const {
                name: "A".into(),
                ty: prop.clone(),
            }),
            Derivation::Assume {
                prop: crate::kernel::CProp::from_checked_term(crate::kernel::Term::Const {
                    name: "B".into(),
                    ty: prop,
                }),
            },
        );

        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    fn ty(name: &str) -> Ty {
        Ty::base(name).unwrap()
    }

    fn ctx_with_nat_consts(names: &[&str]) -> ProofContext {
        let mut sig = Signature::new();
        for name in names {
            sig.declare_const(*name, ty("nat"));
        }
        ProofContext::new(sig)
    }

    fn ctx_with_props(names: &[&str]) -> ProofContext {
        let mut sig = Signature::new();
        for name in names {
            sig.declare_const(*name, Ty::prop());
        }
        ProofContext::new(sig)
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
        sig.declare_const("a", ty("nat"));
        let mut ctx = ProofContext::new(sig);
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
        sig.declare_const("f", fn_ty.clone());
        sig.declare_const("g", fn_ty.clone());
        sig.declare_const("a", ty("nat"));
        sig.declare_const("b", ty("nat"));
        let ctx = ProofContext::new(sig);

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
        let bad_prop = crate::kernel::CProp::from_checked_term(
            crate::kernel::Term::mk_eq(
                crate::kernel::Term::App {
                    func: Box::new(crate::kernel::Term::Const {
                        name: "g".into(),
                        ty: fn_ty.clone(),
                    }),
                    arg: Box::new(crate::kernel::Term::Const { name: "a".into(), ty: ty("nat") }),
                    ty: ty("nat"),
                },
                crate::kernel::Term::App {
                    func: Box::new(crate::kernel::Term::Const { name: "f".into(), ty: fn_ty }),
                    arg: Box::new(crate::kernel::Term::Const { name: "b".into(), ty: ty("nat") }),
                    ty: ty("nat"),
                },
            )
            .unwrap(),
        );

        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn abstraction_tampered_prop_fails_invariant() {
        // Tamper: change the binder name in the result from x to y.
        let mut sig = Signature::new();
        sig.declare_const("a", ty("nat"));
        let mut ctx = ProofContext::new(sig);
        ctx.declare_free("x", ty("nat"));

        let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
        let refl = KernelRules::reflexive(a_term).into_kernel();
        let valid = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();
        // valid: |- (λx:nat. a) == (λx:nat. a)

        // Tamper: replace the result with (λy:nat. a) == (λy:nat. a) — different binder name.
        let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
        let bad_lhs = crate::kernel::Term::Abs {
            name: "y".into(),
            param_ty: ty("nat"),
            body: Box::new(crate::kernel::Term::Const { name: "a".into(), ty: ty("nat") }),
            ty: fn_ty.clone(),
        };
        let bad_rhs = crate::kernel::Term::Abs {
            name: "y".into(),
            param_ty: ty("nat"),
            body: Box::new(crate::kernel::Term::Const { name: "a".into(), ty: ty("nat") }),
            ty: fn_ty.clone(),
        };
        let bad_prop = crate::kernel::CProp::from_checked_term(
            crate::kernel::Term::mk_eq(bad_lhs, bad_rhs).unwrap(),
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn equal_intr_tampered_prop_fails_invariant() {
        // Tamper: valid equal_intr but swapped result (B == A instead of A == B).
        let mut sig = Signature::new();
        sig.declare_const("A", Ty::prop());
        sig.declare_const("B", Ty::prop());
        let ctx = ProofContext::new(sig);

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
        let bad_prop = crate::kernel::CProp::from_checked_term(
            crate::kernel::Term::mk_eq(
                crate::kernel::Term::Const { name: "B".into(), ty: Ty::prop() },
                crate::kernel::Term::Const { name: "A".into(), ty: Ty::prop() },
            )
            .unwrap(),
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn equal_elim_tampered_prop_fails_invariant() {
        // Tamper: valid equal_elim but wrong result (A instead of B).
        let mut sig = Signature::new();
        sig.declare_const("A", Ty::prop());
        sig.declare_const("B", Ty::prop());
        let ctx = ProofContext::new(sig);

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
        let bad_prop = crate::kernel::CProp::from_checked_term(crate::kernel::Term::Const {
            name: "A".into(),
            ty: Ty::prop(),
        });
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }

    #[test]
    fn generalize_tampered_prop_fails_invariant() {
        // Tamper: valid generalize but wrong Var index in result.
        let mut sig = Signature::new();
        sig.declare_const("a", Ty::base("nat").unwrap());
        let mut ctx = ProofContext::new(sig);
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
        let bad_prop = crate::kernel::CProp::from_checked_term(
            crate::kernel::Term::mk_eq(
                crate::kernel::Term::Var {
                    name: "x".into(),
                    index: 999,
                    ty: Ty::base("nat").unwrap(),
                },
                crate::kernel::Term::Var {
                    name: "x".into(),
                    index: 999,
                    ty: Ty::base("nat").unwrap(),
                },
            )
            .unwrap(),
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
        sig.declare_const("a", ty("nat"));
        let ctx = ProofContext::new(sig);

        let raw_prop =
            RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
        let cprop = ctx.certify_prop(raw_prop).unwrap();
        let thm = KernelRules::assume(cprop).into_kernel();

        // Construct a CTerm containing Bound(0) — not possible through public
        // certification (ctx.certify_term rejects Bound), but an internal
        // kernel mistake could still produce one.
        let bad_cterm =
            crate::kernel::CTerm::new(crate::kernel::Term::Bound { index: 0, ty: ty("nat") });
        let entry = InstEntry::new("x", 0, ty("nat"), bad_cterm);
        let err = KernelRules::instantiate(&thm, &[entry]).unwrap_err();
        assert!(matches!(err, KernelError::BoundInSubstitution));
    }

    #[test]
    fn instantiate_tampered_prop_fails_invariant() {
        // Tamper: valid instantiate but wrong replacement in result.
        let mut sig = Signature::new();
        sig.declare_const("a", ty("nat"));
        sig.declare_const("b", ty("nat"));
        let ctx = ProofContext::new(sig);

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
        );
        let bad = KernelThm::new(valid.hyps().to_vec(), bad_prop, valid.derivation().clone());
        assert!(matches!(check_kernel_thm(&bad), Err(KernelError::Invariant(_))));
    }
}
