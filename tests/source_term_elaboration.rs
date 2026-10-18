use isabelle_rs::{
    hol::hol_basis::{hol_owner, hol_signature},
    isar::{
        elaborator::{ElaborationError, elaborate_proposition, elaborate_raw_term},
        source_ast::{SourceExpr, SourceId, SourceType},
        source_parser::{
            parse_source_proposition, parse_source_proposition_at, parse_source_type_at,
        },
    },
    kernel::{ProofContext, Signature, TheorySnapshot, Ty},
};

fn parse_raw(
    input: &str,
    ctx: &ProofContext,
) -> Result<isabelle_rs::kernel::RawTerm, ElaborationError> {
    let source = parse_source_proposition(input, SourceId::new("source_test"))
        .expect("complete source expression");
    elaborate_raw_term(&source.expression, ctx)
}

fn hol_context() -> ProofContext {
    ProofContext::new(TheorySnapshot::root("HOL", hol_signature().expect("HOL signature")))
}

fn actual_true_definition() -> (&'static str, usize) {
    let source = include_str!("../theories/HOL/HOL.thy");
    let declaration = source.find("definition True :: bool").expect("actual True definition");
    let quoted = declaration
        + source[declaration..].find("where \"").expect("True equation")
        + "where \"".len();
    let end = quoted + source[quoted..].find('"').expect("closing quote");
    (&source[quoted..end], quoted)
}

#[test]
fn source_type_curried_arrows_preserve_spans_and_complete_consumption() {
    for spelling in ["=>", "⇒", r"\<Rightarrow>"] {
        let input = format!("  ['a, 'a] {spelling} bool  ");
        let typ = parse_source_type_at(&input, 7).expect("curried equality declaration");
        let SourceType::Arrow { from, to, span } = typ else { panic!("curried arrow") };
        assert_eq!(&input[span.start - 7..span.end - 7], format!("['a, 'a] {spelling} bool"));
        assert!(
            matches!(*from, SourceType::Name { ref name, .. } if name.spelling.as_ref() == "'a")
        );
        let SourceType::Arrow { from, to, .. } = *to else { panic!("second arrow") };
        assert!(
            matches!(*from, SourceType::Name { ref name, .. } if name.spelling.as_ref() == "'a")
        );
        assert!(
            matches!(*to, SourceType::Name { ref name, .. } if name.spelling.as_ref() == "bool")
        );
    }
    for invalid in
        ["['a,] => bool", "['a, 'a] =>", "['a, 'a] => bool ?", "bool =>", "[bool]", "bool = bool"]
    {
        assert!(parse_source_type_at(invalid, 0).is_none(), "unexpected type: {invalid}");
    }
    assert!(parse_source_type_at("bool", usize::MAX).is_none());
}

#[test]
fn true_rhs_real_source_defines_checked_constant_and_alpha_renaming_preserves_result() {
    let (equation, offset) = actual_true_definition();
    let parsed = parse_source_proposition_at(equation, SourceId::new("HOL.thy"), offset)
        .expect("actual True definition parses completely");
    let SourceExpr::SyntaxApplication { arguments, .. } = parsed.expression else {
        panic!("Pure definition")
    };
    let rhs = &arguments[1];
    let theory = hol_owner("HOL").unwrap();
    let ctx = ProofContext::new(theory.snapshot().clone());
    let raw = elaborate_raw_term(rhs, &ctx).expect("actual True RHS elaborates");
    let certified = ctx.certify_term(raw.clone()).expect("HOL.eq instance checked");
    assert_eq!(certified.term().ty(), Ty::base("bool").unwrap());
    let (defined, token) = theory.define_const("HOL.True", raw).expect("real RHS defines True");
    assert_eq!(token.name().as_str(), "HOL.True_def");
    let renamed = parse_raw("((λ(y::bool). y) = (λz. z))", &ctx).unwrap();
    let (_, renamed_token) = theory.define_const("HOL.True", renamed).unwrap();
    assert!(token.prop().term().alpha_eq(renamed_token.prop().term()));
    let reversed = parse_raw("((λp. p) = (λq::bool. q))", &ctx).unwrap();
    let (_, reversed_token) = theory.define_const("HOL.True", reversed).unwrap();
    assert!(token.prop().term().alpha_eq(reversed_token.prop().term()));
    assert!(defined.get(&"HOL.True_def".into()).is_some());
}

#[test]
fn object_equality_rejects_untyped_conflicting_and_undeclared_inputs() {
    let ctx = hol_context();
    for input in [
        "(λx. x) = (λy. y)",
        "(λx::bool. x) = (λy::prop. y)",
        "(λx::bool. x) = (λy. unknown)",
        "(λx::bool. z) = (λy. y)",
    ] {
        assert!(parse_raw(input, &ctx).is_err(), "unexpected equality elaboration: {input}");
    }
    let absent = ProofContext::new(TheorySnapshot::root(
        "NoEq",
        Signature::new().extend_type_constructor("bool", 0).unwrap(),
    ));
    assert!(parse_raw("(λx::bool. x) = (λy. y)", &absent).is_err());
    let malformed = Signature::new()
        .extend_type_constructor("bool", 0)
        .unwrap()
        .extend_const("HOL.eq", Ty::arrow(Ty::base("bool").unwrap(), Ty::base("bool").unwrap()))
        .unwrap();
    let invalid = ProofContext::new(TheorySnapshot::root("BadEq", malformed));
    assert!(parse_raw("(λx::bool. x) = (λy. y)", &invalid).is_err());
    for input in
        ["(λx::bool. x) =", "(λx::bool. x) = (λy. y) = True", "(λx::bool. x) = (λy. y) trailing?"]
    {
        assert!(
            parse_source_proposition(input, SourceId::new("reject")).is_none(),
            "trailing input {input}"
        );
    }
}

#[test]
fn explicit_function_expectation_resolves_only_lambda_and_not_pure_forall() {
    let ctx = hol_context();
    let raw = parse_raw("(λy. y) :: bool => bool", &ctx).unwrap();
    let certified = ctx.certify_term(raw).unwrap();
    let bool_ty = Ty::base("bool").unwrap();
    assert_eq!(certified.term().ty(), Ty::arrow(bool_ty.clone(), bool_ty));
    assert!(parse_raw("(λx. x) :: bool", &ctx).is_err());
    assert!(parse_raw("(λx::prop. x) :: bool => bool", &ctx).is_err());
    let pure =
        parse_source_proposition("!!x. PROP x", SourceId::new("pure")).expect("Pure forall parses");
    assert!(matches!(
        elaborate_proposition(&pure, &ctx),
        Err(ElaborationError::MissingBinderType { .. })
    ));
}
