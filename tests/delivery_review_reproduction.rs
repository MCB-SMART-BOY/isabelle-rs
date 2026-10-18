use std::collections::BTreeSet;

use isabelle_rs::kernel::{
    KernelError, KernelRules, ProofContext, RawTerm, Signature, TheorySnapshot, Ty,
};
use isabelle_rs::ml::{DenyHost, Value, Vm};

#[test]
fn generalize_index_range_overflow_returns_error() {
    let mut context = ProofContext::new(TheorySnapshot::root("IndexLimit", Signature::new()));
    context.declare_free("x_", Ty::prop());
    let term = context
        .certify_term(RawTerm::eq(
            RawTerm::var("P", usize::MAX - 1, Ty::prop()),
            RawTerm::free("x_", Ty::prop()),
        ))
        .unwrap();
    let theorem = KernelRules::reflexive(term);
    let result = KernelRules::generalize(
        theorem.as_kernel(),
        &BTreeSet::new(),
        &BTreeSet::from(["ghost".into(), "x_".into()]),
        usize::MAX,
    );
    assert_eq!(
        result.unwrap_err(),
        KernelError::GeneralizeIndexOverflow { index: usize::MAX, offset: 1 }
    );
}

#[test]
fn ml_local_rebinding_exports_body_binding() {
    let mut vm = Vm::new(DenyHost);
    vm.evaluate(
        "local-rebinding.sml",
        "val x = 1; local val hidden = 0 in val x = 2 end; val answer = x;",
    )
    .unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(2));
}
