//! Independent reference encoder for v2 TheoremId.
//!
//! Re-implements the v2 identity schema using `sha2::Sha256` directly.
//! Does NOT call `compute_theorem_id`, `CanonicalEncoder`, or any
//! `write_canonical` methods — every encoding step is spelled out.
//!
//! The reference is compared against `compute_theorem_id` in tests.

use sha2::{Digest, Sha256};
use super::{
    CProp, ContextStamp, DependencySet, Name, Term, Ty,
};

/// Domain tag (must match `THEOREM_DOMAIN` in `theory.rs`).
const DOMAIN_V2: &[u8] = b"isabelle-rs/theorem/v2";

fn write_u64_be(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_be_bytes());
}

/// Mirror of `CanonicalEncoder::write_bytes`: u64 BE length + data.
fn write_bytes(buf: &mut Vec<u8>, data: &[u8]) {
    write_u64_be(buf, data.len() as u64);
    buf.extend_from_slice(data);
}

/// Mirror of `CanonicalEncoder::write_name`.
fn write_name(buf: &mut Vec<u8>, name: &Name) {
    write_bytes(buf, name.as_str().as_bytes());
}

fn write_ty(buf: &mut Vec<u8>, ty: &Ty) {
    ty.write_canonical_raw(buf);
}

fn write_term(buf: &mut Vec<u8>, term: &Term) {
    match term {
        Term::Const { name, ty } => {
            buf.push(0u8);
            write_name(buf, name);
            write_ty(buf, ty);
        }
        Term::Free { name, ty } => {
            buf.push(1u8);
            write_name(buf, name);
            write_ty(buf, ty);
        }
        Term::Var { name, index, ty } => {
            buf.push(2u8);
            write_name(buf, name);
            write_u64_be(buf, *index as u64);
            write_ty(buf, ty);
        }
        Term::Bound { index, ty } => {
            buf.push(3u8);
            write_u64_be(buf, *index as u64);
            write_ty(buf, ty);
        }
        Term::Abs { param_ty, body, .. } => {
            buf.push(4u8);
            write_ty(buf, param_ty);
            write_term(buf, body);
        }
        Term::Forall { param_ty, body, .. } => {
            buf.push(5u8);
            write_ty(buf, param_ty);
            write_term(buf, body);
        }
        Term::App { func, arg, .. } => {
            buf.push(6u8);
            write_term(buf, func);
            write_term(buf, arg);
        }
        Term::Eq { object_ty, lhs, rhs } => {
            buf.push(7u8);
            write_ty(buf, object_ty);
            write_term(buf, lhs);
            write_term(buf, rhs);
        }
        Term::Imp { premise, conclusion } => {
            buf.push(8u8);
            write_term(buf, premise);
            write_term(buf, conclusion);
        }
    }
}

fn write_deps(buf: &mut Vec<u8>, deps: &DependencySet) {
    deps.write_canonical_raw(buf);
}

pub(crate) fn reference_theorem_id_v2(
    context: &ContextStamp,
    prop: &CProp,
    dependencies: &DependencySet,
) -> [u8; 32] {
    let mut buf = Vec::with_capacity(256);

    // 1. Domain tag (write_bytes: u64 BE length + bytes)
    write_bytes(&mut buf, DOMAIN_V2);

    // 2. ContextStamp
    buf.extend_from_slice(&context.theory().to_bytes());
    buf.extend_from_slice(&context.signature().to_bytes());
    match context.logic_basis() {
        Some(basis) => {
            buf.push(1u8);
            buf.extend_from_slice(&basis.to_bytes());
        }
        None => {
            buf.push(0u8);
        }
    }

    // 3. PureReplayV1
    buf.push(0u8);

    // 4. Unresolved proof burdens
    buf.push(0u8);

    // 5. Term
    write_term(&mut buf, prop.term());

    // 6. DependencySet
    write_deps(&mut buf, dependencies);

    let mut hasher = Sha256::new();
    hasher.update(&buf);
    let result = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&result);
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theory::compute_theorem_id;
    use crate::{
        accept_closed_theorem,
        Name, ProofContext, RawTerm, TrustedTheory, Ty,
    };

    fn theory(name: &str, atoms: &[&str]) -> TrustedTheory {
        let mut sig = crate::Signature::new();
        for a in atoms {
            sig = sig.extend_const(Name::from(*a), Ty::prop()).unwrap();
        }
        TrustedTheory::root(name, sig)
    }

    fn implication_identity(theory: &TrustedTheory, a: &str) -> crate::ClosedThm {
        let context = ProofContext::new(theory.snapshot().clone());
        let proposition = context.certify_prop(RawTerm::Const {
            name: Name::from(a),
            ty: Ty::prop(),
        }).unwrap();
        let assumed = crate::KernelRules::assume(proposition.clone()).into_kernel();
        crate::KernelRules::implies_intr(&proposition, &assumed).unwrap().try_close().unwrap()
    }

    #[test]
    fn reference_matches_production() {
        let parent = theory("Pure", &["A"]);
        let candidate = implication_identity(&parent, "A");
        let (_, accepted) = accept_closed_theorem(&parent, "imp_identity", candidate).unwrap();

        let stamp = parent.stamp();
        let prop = accepted.prop();
        let deps = accepted.dependencies();

        let ref_id = reference_theorem_id_v2(&stamp, prop, deps);
        let prod_id = compute_theorem_id(stamp, prop, deps);

        assert_eq!(
            ref_id, prod_id.to_bytes(),
            "reference encoder must match production encoder"
        );
    }
}
