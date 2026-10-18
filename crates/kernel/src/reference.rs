//! Independent reference encoder for v8 TheoremId.
//!
//! Re-implements the v8 identity schema using `sha2::Sha256` directly.
//! Every encoding step is independent of `CanonicalEncoder` and all
//! `write_canonical` methods. Uses only `pub(crate)` accessor
//! methods on `Ty` and `DependencySet` to extract structural data.
//!
//! The reference is compared against production TheoremId output in tests.

use super::obligations::{ProofMode, ProofPayload};
use super::{CProp, ContextStamp, DependencyKind, DependencySet, Name, Term, Ty};
use sha2::{Digest, Sha256};

/// Domain tag (must match `THEOREM_DOMAIN` in `theory.rs`).
const DOMAIN_V8: &[u8] = b"isabelle-rs/theorem/v8";

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

fn write_sort(buf: &mut Vec<u8>, sort: &super::Sort) {
    write_u64_be(buf, sort.classes().len() as u64);
    for class in sort.classes() {
        write_name(buf, class);
    }
}

fn write_ty(buf: &mut Vec<u8>, ty: &Ty) {
    if let Some((name, index, sort)) = ty.as_type_var() {
        buf.push(1u8);
        write_name(buf, name);
        write_u64_be(buf, index as u64);
        write_sort(buf, sort);
    } else if let Some((name, sort)) = ty.as_type_free() {
        buf.push(2u8);
        write_name(buf, name);
        write_sort(buf, sort);
    } else if let Some((name, args)) = ty.as_type_app() {
        buf.push(0u8);
        write_name(buf, name);
        write_u64_be(buf, args.len() as u64);
        for arg in args {
            write_ty(buf, arg);
        }
    }
}

fn write_term(buf: &mut Vec<u8>, term: &Term) {
    match term {
        Term::Const { name, ty } => {
            buf.push(0u8);
            write_name(buf, name);
            write_ty(buf, ty);
        },
        Term::Free { name, ty } => {
            buf.push(1u8);
            write_name(buf, name);
            write_ty(buf, ty);
        },
        Term::Var { name, index, ty } => {
            buf.push(2u8);
            write_name(buf, name);
            write_u64_be(buf, *index as u64);
            write_ty(buf, ty);
        },
        Term::Bound { index, ty } => {
            buf.push(3u8);
            write_u64_be(buf, *index as u64);
            write_ty(buf, ty);
        },
        Term::Abs { param_ty, body, .. } => {
            buf.push(4u8);
            write_ty(buf, param_ty);
            write_term(buf, body);
        },
        Term::Forall { param_ty, body, .. } => {
            buf.push(5u8);
            write_ty(buf, param_ty);
            write_term(buf, body);
        },
        Term::App { func, arg, .. } => {
            buf.push(6u8);
            write_term(buf, func);
            write_term(buf, arg);
        },
        Term::Eq { object_ty, lhs, rhs } => {
            buf.push(7u8);
            write_ty(buf, object_ty);
            write_term(buf, lhs);
            write_term(buf, rhs);
        },
        Term::Imp { premise, conclusion } => {
            buf.push(8u8);
            write_term(buf, premise);
            write_term(buf, conclusion);
        },
    }
}
fn write_deps(buf: &mut Vec<u8>, deps: &DependencySet) {
    // Independent encoding — does NOT call any DependencySet::write_canonical* method.
    let entries = deps.as_sorted_entries();
    write_u64_be(buf, entries.len() as u64);
    for (kind, digest) in &entries {
        let tag = match kind {
            DependencyKind::Axiom => 0u8,
            DependencyKind::Definition => 1u8,
            DependencyKind::Theorem => 2u8,
            DependencyKind::Class => 3u8,
        };
        buf.push(tag);
        buf.extend_from_slice(digest);
    }
}

fn write_context(buf: &mut Vec<u8>, context: ContextStamp) {
    write_bytes(buf, b"isabelle-rs/context/v3");
    buf.extend_from_slice(&context.theory().to_bytes());
    buf.extend_from_slice(&context.signature().to_bytes());
    match context.logic_basis() {
        Some(basis) => {
            buf.push(1);
            buf.extend_from_slice(&basis.to_bytes());
        },
        None => buf.push(0),
    }
    match context.local_type_scope() {
        Some(scope) => {
            buf.push(1);
            write_u64_be(buf, scope);
        },
        None => buf.push(0),
    }
}

fn write_payload(buf: &mut Vec<u8>, payload: &ProofPayload) {
    write_u64_be(buf, payload.shyps().len() as u64);
    for sort in payload.shyps() {
        write_sort(buf, sort);
    }
    write_u64_be(buf, payload.sort_obligations().len() as u64);
    for (ty, sort) in payload.sort_obligations() {
        write_ty(buf, ty);
        write_sort(buf, sort);
    }
    write_u64_be(buf, payload.flex_pairs().len() as u64);
    for (left, right) in payload.flex_pairs() {
        write_context(buf, left.context());
        write_term(buf, left.term());
        write_context(buf, right.context());
        write_term(buf, right.term());
    }
    write_u64_be(buf, payload.pending().len() as u64);
    for pending in payload.pending() {
        write_u64_be(buf, pending.value());
    }
    match payload.mode() {
        ProofMode::Ordinary => buf.push(0),
        ProofMode::SortErased => buf.push(1),
    }
}

pub(crate) fn reference_theorem_id_v8(
    context: &ContextStamp,
    prop: &CProp,
    payload: &ProofPayload,
    max_index: Option<usize>,
    dependencies: &DependencySet,
) -> [u8; 32] {
    let mut buf = Vec::with_capacity(256);

    // 1. Domain tag (write_bytes: u64 BE length + bytes)
    write_bytes(&mut buf, DOMAIN_V8);

    // 2. ContextStamp
    write_context(&mut buf, *context);

    // 3. PureReplayV1
    buf.push(0u8);

    // 4. Complete proof payload
    write_payload(&mut buf, payload);
    match max_index {
        Some(index) => {
            buf.push(1);
            write_u64_be(&mut buf, index as u64);
        },
        None => buf.push(0),
    }

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
    use crate::{Name, ProofContext, RawTerm, TrustedTheory, Ty, accept_closed_theorem};

    fn theory(name: &str, atoms: &[&str]) -> TrustedTheory {
        let mut sig = crate::Signature::new();
        for a in atoms {
            sig = sig.extend_const(Name::from(*a), Ty::prop()).unwrap();
        }
        TrustedTheory::root(name, sig)
    }

    fn implication_identity(theory: &TrustedTheory, a: &str) -> crate::ClosedThm {
        let context = ProofContext::new(theory.snapshot().clone());
        let proposition =
            context.certify_prop(RawTerm::Const { name: Name::from(a), ty: Ty::prop() }).unwrap();
        let assumed = crate::KernelRules::assume(proposition.clone()).unwrap().into_kernel();
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

        let ref_id = reference_theorem_id_v8(
            &stamp,
            prop,
            accepted.as_kernel().payload(),
            accepted.as_kernel().max_var_index(),
            deps,
        );
        let prod_bytes = accepted.id().to_bytes();

        assert_eq!(ref_id, prod_bytes, "reference encoder must match production encoder");
    }

    #[test]
    fn theorem_index_bound_changes_canonical_identity() {
        let parent = theory("Pure", &["A"]);
        let ordinary = implication_identity(&parent, "A");
        let raised = crate::KernelRules::adjust_max_index(ordinary.as_kernel(), Some(7));
        let (_, original) = accept_closed_theorem(&parent, "original", ordinary).unwrap();
        let (_, adjusted) =
            accept_closed_theorem(&parent, "adjusted", raised.try_close().unwrap()).unwrap();
        assert_ne!(original.id(), adjusted.id());
        let encoded = reference_theorem_id_v8(
            &parent.stamp(),
            adjusted.prop(),
            adjusted.as_kernel().payload(),
            adjusted.as_kernel().max_var_index(),
            adjusted.dependencies(),
        );
        assert_eq!(encoded, adjusted.id().to_bytes());
    }

    #[test]
    fn reference_present_schema_sort_matches_accepted_identity() {
        let parent = theory("Pure", &[]);
        let context = ProofContext::new(parent.snapshot().clone());
        let ty = Ty::tvar("a", 0, crate::Sort::empty());
        let term = context.certify_term(RawTerm::var("x", 0, ty)).unwrap();
        let candidate = crate::KernelRules::reflexive(term);
        let (_, accepted) = accept_closed_theorem(&parent, "schema", candidate).unwrap();
        let reference = reference_theorem_id_v8(
            &parent.stamp(),
            accepted.prop(),
            accepted.as_kernel().payload(),
            accepted.as_kernel().max_var_index(),
            accepted.dependencies(),
        );
        assert_eq!(reference, accepted.id().to_bytes());
    }

    #[test]
    fn reference_checked_class_dependency_matches_production() {
        let signature = crate::Signature::new()
            .install_empty_class(crate::EmptyClassDeclCert::hol_type())
            .unwrap();
        let parent = TrustedTheory::root("HOL", signature)
            .install_semantic_arity(crate::SemanticArityCert::FunctionTypeArityCert)
            .unwrap();
        let alpha = Ty::tvar("a", 0, crate::Sort::hol_type());
        let function = Ty::arrow(alpha.clone(), alpha);
        let evidence = crate::prove_of_class(
            &parent,
            function,
            Name::from("HOL.type"),
            crate::OfClassCandidate::TypeConstructor {
                arguments: vec![vec![crate::OfClassCandidate::AnnotatedAtomLeaf]; 2],
            },
        )
        .unwrap();
        let closed = crate::KernelRules::of_class(&parent, &evidence).unwrap();
        let (_, accepted) = accept_closed_theorem(&parent, "fun_type", closed).unwrap();
        assert_eq!(accepted.dependencies().len(), 1);
        let reference = reference_theorem_id_v8(
            &parent.stamp(),
            accepted.prop(),
            accepted.as_kernel().payload(),
            accepted.as_kernel().max_var_index(),
            accepted.dependencies(),
        );
        assert_eq!(reference, accepted.id().to_bytes());
    }
}
