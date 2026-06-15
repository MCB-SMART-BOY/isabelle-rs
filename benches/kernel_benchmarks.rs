//! Criterion benchmarks for isabelle-rs kernel and proof engine.
//!
//! Run with: `cargo bench`
//!
//! ## Benchmarks
//!
//! 1. **Kernel operations** — reflexive, symmetric, assume, implies_intr/elim
//! 2. **Unification** — HO pattern unification
//! 3. **Type inference** — HM type inference on various terms
//! 4. **Proof checking** — proof term validation
//! 5. **Net operations** — discrimination net lookup

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use isabelle_rs::core::*;

// =========================================================================
// Kernel operation benchmarks
// =========================================================================

fn bench_kernel_reflexive(c: &mut Criterion) {
    let mut group = c.benchmark_group("kernel/reflexive");
    let types = vec![
        types::Typ::base("bool"),
        types::Typ::base("nat"),
        types::Typ::arrow(types::Typ::base("bool"), types::Typ::base("bool")),
    ];

    for (i, typ) in types.iter().enumerate() {
        let t = term::Term::const_("c", typ.clone());
        let ct = thm::CTerm::certify(t);
        group.bench_function(format!("reflexive_type_{i}"), |b| {
            b.iter(|| thm::ThmKernel::reflexive(black_box(ct.clone())))
        });
    }
    group.finish();
}

fn bench_kernel_assume(c: &mut Criterion) {
    let mut group = c.benchmark_group("kernel/assume");
    let t = term::Term::const_("A", types::Typ::base("prop"));
    let ct = thm::CTerm::certify(t);
    group.bench_function("assume", |b| {
        b.iter(|| thm::ThmKernel::assume(black_box(ct.clone())));
    });
    group.finish();
}

fn bench_kernel_implies_roundtrip(c: &mut Criterion) {
    let mut group = c.benchmark_group("kernel/implies_roundtrip");

    group.bench_function("intr_then_elim", |b| {
        let a = term::Term::const_("A", types::Typ::base("prop"));
        let ct_a = thm::CTerm::certify(a);
        let assume_a = thm::ThmKernel::assume(ct_a.clone());

        b.iter(|| {
            let imp = thm::ThmKernel::implies_intr(&ct_a, &assume_a).unwrap();
            let _elim = thm::ThmKernel::implies_elim(&imp, &assume_a).unwrap();
        });
    });
    group.finish();
}

// =========================================================================
// Unification benchmarks
// =========================================================================

fn bench_unification(c: &mut Criterion) {
    let mut group = c.benchmark_group("unification");

    // Simple unification: variable with term
    group.bench_function("simple_var_term", |b| {
        let x = term::Term::free("x", types::Typ::dummy());
        let t = term::Term::const_("c", types::Typ::base("bool"));
        let config = unify::UnifyConfig { search_bound: 20, max_unifiers: 1 };

        b.iter(|| {
            let env = envir::Envir::init();
            let _ = unify::unifiers(black_box(&env), &[(x.clone(), t.clone())], &config);
        });
    });

    // Deep term unification
    group.bench_function("deep_term", |b| {
        let config = unify::UnifyConfig { search_bound: 20, max_unifiers: 1 };
        // Build a moderately deep term
        let mut t = term::Term::free("x", types::Typ::dummy());
        for _ in 0..5 {
            t = term::Term::app(
                term::Term::abs("y", types::Typ::dummy(), t.clone()),
                term::Term::const_("c", types::Typ::base("bool")),
            );
        }

        b.iter(|| {
            let env = envir::Envir::init();
            let _ = unify::unifiers(black_box(&env), &[(t.clone(), t.clone())], &config);
        });
    });
    group.finish();
}

// =========================================================================
// Type inference benchmarks
// =========================================================================

fn bench_type_infer(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_infer");

    group.bench_function("simple_app", |b| {
        let f = term::Term::free(
            "f",
            types::Typ::arrow(types::Typ::free("'a", types::Sort::top()), types::Typ::base("bool")),
        );
        let x = term::Term::free("x", types::Typ::free("'a", types::Sort::top()));
        let app = term::Term::app(f, x);

        b.iter(|| {
            let mut infer = type_infer::TypeInfer::new();
            let _ = infer.infer(black_box(&app));
        });
    });

    group.bench_function("complex_lambda", |b| {
        // λf. λx. f (f x)
        let f = term::Term::bound(1);
        let inner_x = term::Term::bound(0);
        let app1 = term::Term::app(f.clone(), inner_x);
        let app2 = term::Term::app(f, app1);
        let abs1 = term::Term::abs("x", types::Typ::dummy(), app2);
        let abs2 = term::Term::abs("f", types::Typ::dummy(), abs1);

        b.iter(|| {
            let mut infer = type_infer::TypeInfer::new();
            let _ = infer.infer(black_box(&abs2));
        });
    });
    group.finish();
}

// =========================================================================
// Proof term benchmarks
// =========================================================================

fn bench_proof_checking(c: &mut Criterion) {
    let mut group = c.benchmark_group("proofterm");

    group.bench_function("check_axiom", |b| {
        let prop = term::Term::const_("A", types::Typ::base("prop"));
        let proof = proofterm::ProofTerm::PAxm { name: "test".into(), prop: prop.clone() };
        b.iter(|| {
            let _ = proofterm::check_proof(black_box(&proof), black_box(&prop));
        });
    });

    group.bench_function("check_app", |bench| {
        let a = term::Term::const_("A", types::Typ::base("prop"));
        let b_term = term::Term::const_("B", types::Typ::base("prop"));
        let imp = logic::Pure::mk_implies(a.clone(), b_term.clone());

        let proof_imp = proofterm::ProofTerm::PAxm { name: "impI".into(), prop: imp };
        let proof_a = proofterm::ProofTerm::PAxm { name: "assume".into(), prop: a };
        let app =
            proofterm::ProofTerm::PAppP { proof1: Box::new(proof_imp), proof2: Box::new(proof_a) };
        bench.iter(|| {
            let _ = proofterm::check_proof(black_box(&app), black_box(&b_term));
        });
    });
    group.finish();
}

// =========================================================================
// Context switching benchmarks
// =========================================================================

fn bench_context(c: &mut Criterion) {
    let mut group = c.benchmark_group("context");

    group.bench_function("enter_exit_proof", |b| {
        let thy = theory::Theory::pure();
        let ctx = context::Context::theory(thy);
        b.iter(|| {
            let ctx = black_box(ctx.clone());
            let ctx = ctx.enter_proof();
            let _ctx = ctx.exit_proof();
        });
    });

    group.bench_function("fix_assume", |b| {
        let thy = theory::Theory::pure();
        b.iter(|| {
            let mut ctx = context::Context::proof(std::sync::Arc::clone(&thy));
            ctx.fix("x", types::Typ::base("nat"));
            ctx.assume(term::Term::const_("P(x)", types::Typ::base("prop")));
        });
    });
    group.finish();
}

// =========================================================================
// Main
// =========================================================================

criterion_group!(
    benches,
    bench_kernel_reflexive,
    bench_kernel_assume,
    bench_kernel_implies_roundtrip,
    bench_unification,
    bench_type_infer,
    bench_proof_checking,
    bench_context,
);
criterion_main!(benches);
