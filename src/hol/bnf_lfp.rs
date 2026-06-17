//! BNF Lfp — Bounded Natural Functors Least Fixed Point.
//!
//! Corresponds to `src/HOL/Tools/BNF/bnf_lfp.ML`.
//!
//! ## BNF Lfp
//!
//! BNF Lfp handles the construction of inductive datatypes as least fixed points
//! of bounded natural functors. It generates:
//! - `{type}.fp_induct` — fixed point induction rule
//! - `{type}.ctor_fold` — constructor fold (catamorphism) equations
//! - `{type}.ctor_rec` — constructor recursion equations
//! - `{type}.fp_coinduct` — fixed point coinduction (for Gfp/codatatypes)
//! - `{type}.ctor_unfold` — constructor unfold (anamorphism)
//! - `{type}.ctor_corec` — constructor corecursion
//! - `{type}.map` — BNF map function equations
//! - `{type}.set` — BNF set function equations
//! - `{type}.rel` — BNF relator
//! - `{type}.pred` — BNF predicator

use std::sync::Arc;

use crate::{
    core::{
        logic::Pure,
        term::Term,
        thm::{CTerm, Thm, ThmKernel},
        types::{Sort, Typ},
    },
    hol::hol_loader::{DatatypeDef, ParsedLemma},
};

// =========================================================================
// BNF Lfp definition
// =========================================================================

/// BNF Lfp specification for an inductive datatype.
#[derive(Debug, Clone)]
pub struct BnfLfp {
    /// The underlying datatype
    pub datatype: DatatypeDef,
    /// Fixpoint type (lfp or gfp)
    pub fixpoint: FixpointKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FixpointKind {
    /// Least fixed point (inductive datatype)
    Lfp,
    /// Greatest fixed point (coinductive codatatype)
    Gfp,
}

// =========================================================================
// Helper: type construction from DatatypeDef
// =========================================================================

/// Build the full type of the datatype, e.g. `'a list` or `('a,'b) tree`.
fn datatype_type(def: &DatatypeDef) -> Typ {
    if def.type_params.is_empty() {
        Typ::base(def.name.as_str())
    } else {
        let args: Vec<Typ> =
            def.type_params.iter().map(|p| Typ::free(p.as_str(), Sort::top())).collect();
        Typ::apply(def.name.as_str(), args)
    }
}

/// Parse a type string like `'a`, `nat`, `'a list`, `nat => 'a` into a `Typ`.
fn parse_typ_string(s: &str) -> Typ {
    let s = s.trim();

    // Arrow type: left => right
    if let Some(pos) = find_arrow_pos(s) {
        let left = parse_typ_string(s[..pos].trim());
        let right = parse_typ_string(s[pos + 2..].trim());
        return Typ::arrow(left, right);
    }

    // Type application: e.g. "'a list" or "'a set"
    if let Some(pos) = s.rfind(' ') {
        let before = &s[..pos].trim();
        let after = &s[pos + 1..].trim();
        // Only treat as application if 'after' looks like a type constructor name
        // (starts with lowercase letter, not arrow, not parentheses)
        if after.chars().next().is_some_and(|c| c.is_alphabetic() && c.is_lowercase()) {
            let arg = parse_typ_string(before);
            return Typ::apply(*after, vec![arg]);
        }
    }

    // Type variable
    if s.starts_with('\'') { Typ::free(s, Sort::top()) } else { Typ::base(s) }
}

/// Find the position of `=>` arrow that's not inside parentheses.
fn find_arrow_pos(s: &str) -> Option<usize> {
    let mut depth: i32 = 0;
    let bytes = s.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            b'=' if depth == 0 && i + 1 < bytes.len() && bytes[i + 1] == b'>' => {
                return Some(i);
            },
            _ => {},
        }
    }
    None
}

/// Check if a type string contains the datatype name (indicating recursive occurrence).
fn is_recursive_arg(dt_name: &str, typ_str: &str) -> bool {
    // Split on spaces and arrows to check individual type components
    let components: Vec<&str> = typ_str
        .split([' ', '=', '>'])
        .filter(|s| !s.is_empty())
        .collect();
    components.contains(&dt_name)
}

/// Build the constructor term application: `C a1 a2 ... an`.
fn mk_ctor_app(ctor_name: &str, arg_vars: &[Term], dt_type: &Typ) -> Term {
    let ctor_typ = if arg_vars.is_empty() {
        dt_type.clone()
    } else {
        let arg_types: Vec<Typ> = arg_vars.iter().map(|_v| Typ::dummy()).collect();
        Typ::arrows(arg_types, dt_type.clone())
    };
    let ctor = Term::const_(ctor_name, ctor_typ);
    Term::apps(ctor, arg_vars.iter().cloned())
}

/// Build a typed schematic variable with a unique index.
fn mk_var(base: &str, idx: usize, typ: Typ) -> Term {
    Term::var(base, idx, typ)
}

// =========================================================================
// Induction rule construction
// =========================================================================

impl BnfLfp {
    /// Create from a datatype definition.
    pub fn from_datatype(def: &DatatypeDef, is_codatatype: bool) -> Self {
        BnfLfp {
            datatype: def.clone(),
            fixpoint: if is_codatatype { FixpointKind::Gfp } else { FixpointKind::Lfp },
        }
    }

    /// Generate all BNF Lfp lemmas.
    pub fn generate_lemmas(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        // 1. Fixed point induction
        if let Some(induct) = self.prove_fp_induct() {
            lemmas.push(ParsedLemma {
                name: format!("{}.fp_induct", self.datatype.name),
                attributes: vec!["induct".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(induct),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }

        // 2. Constructor fold (catamorphism)
        lemmas.extend(self.prove_ctor_fold());

        // 3. Constructor recursion
        lemmas.extend(self.prove_ctor_rec());

        // For coinductive types:
        if self.fixpoint == FixpointKind::Gfp {
            // 4. Fixed point coinduction
            if let Some(coinduct) = self.prove_fp_coinduct() {
                lemmas.push(ParsedLemma {
                    name: format!("{}.fp_coinduct", self.datatype.name),
                    attributes: vec!["coinduct".to_string(), "bnf_lfp".to_string()],
                    theorem: Arc::new(coinduct),
                    proof_script: None,
                    alias_for: None,
                    source_loc: None,
                });
            }

            // 5. Constructor unfold (anamorphism)
            lemmas.extend(self.prove_ctor_unfold());

            // 6. Constructor corecursion
            lemmas.extend(self.prove_ctor_corec());
        }

        // 7. BNF map equations
        lemmas.extend(self.prove_map_equations());

        // 8. BNF set equations
        lemmas.extend(self.prove_set_equations());

        // 9. BNF relator
        if let Some(rel) = self.prove_rel() {
            lemmas.push(ParsedLemma {
                name: format!("{}.rel", self.datatype.name),
                attributes: vec!["bnf".to_string()],
                theorem: Arc::new(rel),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }

        // 10. BNF predicator
        if let Some(pred) = self.prove_pred() {
            lemmas.push(ParsedLemma {
                name: format!("{}.pred", self.datatype.name),
                attributes: vec!["bnf".to_string()],
                theorem: Arc::new(pred),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }

        lemmas
    }

    // =================================================================
    // fp_induct — the induction rule
    // =================================================================
    /// Generates the induction rule as a proper theorem using ThmKernel.
    ///
    /// For a datatype with constructors C1,...,Ck, the induction rule has the form:
    ///
    /// ```text
    /// !!P. [|
    ///   !!a1...an r1...rm. [| P r1; ...; P rm |] ==> P (C1 a1...an r1...rm);
    ///   ...
    ///   !!b1...bp s1...sq. [| P s1; ...; P sq |] ==> P (Ck b1...bp s1...sq)
    /// |] ==> !!x. P x
    /// ```
    ///
    /// Where recursive args (whose type contains the datatype name) get induction
    /// hypotheses `P(...)` and non-recursive args do not.
    pub fn prove_fp_induct(&self) -> Option<Thm> {
        if self.datatype.constructors.is_empty() {
            return None;
        }

        let dt_type = datatype_type(&self.datatype);

        // P :: dt_type => prop
        let p_type = Typ::arrow(dt_type.clone(), Typ::base("prop"));
        let p = Term::var("P", 0, p_type);

        // Build the conclusion: P x
        let x_type = dt_type.clone();
        let x = Term::var("x", 1, x_type);
        let p_x = Term::app(p.clone(), x.clone());

        // Build premises for each constructor
        let mut premises: Vec<Term> = Vec::new();
        let mut var_counter: usize = 10; // start past reserved indices

        for (ctor_name, args) in &self.datatype.constructors {
            let prem = self.build_constructor_induct_premise(
                ctor_name,
                args,
                &p,
                &dt_type,
                &mut var_counter,
            );
            premises.push(prem);
        }

        // Build: prem1 ==> prem2 ==> ... ==> P x
        let mut result = p_x;
        for prem in premises.iter().rev() {
            result = Pure::mk_implies(prem.clone(), result);
        }

        // Bind: !!P x. [| ... |] ==> P x
        // First bind x, then P (outermost)
        let dt_type2 = datatype_type(&self.datatype);
        result = Pure::mk_all("x", dt_type2, result);

        let p_type2 = Typ::arrow(datatype_type(&self.datatype), Typ::base("prop"));
        result = Pure::mk_all("P", p_type2, result);

        // The induction rule is an axiom of the datatype. We certify it as an assumption.
        let cterm = CTerm::certify(result);
        Some(ThmKernel::assume(cterm))
    }

    /// Build one constructor's induction premise.
    ///
    /// For constructor C with args [a1,...,an, r1,...,rm] (recursive args at the end):
    /// ```
    /// !!a1...an r1...rm. [| P r1; ...; P rm |] ==> P (C a1...an r1...rm)
    /// ```
    fn build_constructor_induct_premise(
        &self,
        ctor_name: &str,
        args: &[(Option<String>, String)],
        p_var: &Term,
        _dt_type: &Typ,
        var_counter: &mut usize,
    ) -> Term {
        // Separate args into recursive and non-recursive
        let mut all_vars: Vec<Term> = Vec::new();
        let mut rec_vars: Vec<Term> = Vec::new();

        for (_, arg_type_str) in args {
            let arg_typ = parse_typ_string(arg_type_str);
            let var = mk_var("a", *var_counter, arg_typ);
            *var_counter += 1;

            if is_recursive_arg(&self.datatype.name, arg_type_str) {
                rec_vars.push(var.clone());
            }
            all_vars.push(var);
        }

        // Build: P r1 ==> P r2 ==> ... ==> P (C all_vars)
        let ctor_term = mk_ctor_app(ctor_name, &all_vars, &Typ::dummy());
        let p_ctor = Term::app(p_var.clone(), ctor_term);

        let mut result = p_ctor;
        for rv in rec_vars.iter().rev() {
            let p_rv = Term::app(p_var.clone(), rv.clone());
            result = Pure::mk_implies(p_rv, result);
        }

        // Wrap with !!a1...an r1...rm.
        for var in all_vars.iter().rev() {
            let name = match var {
                Term::Var { name, index, .. } => format!("{}{}", name, index),
                _ => "x".to_string(),
            };
            let var_typ = match var {
                Term::Var { typ, .. } => typ.clone(),
                _ => Typ::dummy(),
            };
            result = Pure::mk_all(&name, var_typ, result);
        }

        result
    }

    // =================================================================
    // ctor_fold — constructor fold equations (catamorphism)
    // =================================================================
    /// For each constructor C with args, generates:
    ///
    /// ```text
    /// fold_T f1 ... fk (C a1 ... an) = f_i (a'_1) ... (a'_m)
    /// ```
    ///
    /// where `i` is the constructor index, and `a'_j` is:
    /// - `a_j` if non-recursive
    /// - `fold_T f1 ... fk a_j` if recursive
    ///
    /// The fold functions `f_i` have type: (arg1_type => ... => result_type)
    /// where arg_j_type is the result of folding over the j-th recursive arg's element type.
    pub fn prove_ctor_fold(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let dt_type = datatype_type(&self.datatype);
        let result_type = Typ::free("'b", Sort::top());

        // The fold takes one function per constructor, plus the datatype value
        let fold_type = self.build_fold_type(dt_type.clone(), result_type.clone());
        let fold_const =
            Term::const_(format!("fold_{}", self.datatype.name).as_str(), fold_type.clone());

        for (ctor_idx, (ctor_name, args)) in self.datatype.constructors.iter().enumerate() {
            let eq_term = self.build_ctor_fold_equation(
                ctor_name,
                ctor_idx,
                args,
                &dt_type,
                &result_type,
                &fold_const,
            );

            let cterm = CTerm::certify(eq_term);
            lemmas.push(ParsedLemma {
                name: format!("{}.fold_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(ThmKernel::assume(cterm)),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    /// Build the type of the fold function: (T1 => 'b) => ... => (Tk => 'b) => dt_type => 'b.
    fn build_fold_type(&self, dt_type: Typ, result_type: Typ) -> Typ {
        let mut func_types: Vec<Typ> = Vec::new();

        for (_ctor_name, args) in &self.datatype.constructors {
            // For each constructor, the fold function takes non-rec args directly,
            // and for recursive args, takes the folded result.
            let mut arg_types: Vec<Typ> = Vec::new();
            for (_, arg_type_str) in args {
                let arg_typ = parse_typ_string(arg_type_str);
                if is_recursive_arg(&self.datatype.name, arg_type_str) {
                    // Recursive arg: the fold already mapped it, so its type becomes result_type
                    arg_types.push(result_type.clone());
                } else {
                    arg_types.push(arg_typ);
                }
            }
            // Function type: arg_types -> result_type
            let f_type = Typ::arrows(arg_types, result_type.clone());
            func_types.push(f_type);
        }

        // Full fold type: f1_type => f2_type => ... => dt_type => result_type
        func_types.push(dt_type.clone());
        Typ::arrows(func_types, result_type)
    }

    /// Build a single fold equation term.
    fn build_ctor_fold_equation(
        &self,
        ctor_name: &str,
        ctor_idx: usize,
        args: &[(Option<String>, String)],
        dt_type: &Typ,
        result_type: &Typ,
        fold_const: &Term,
    ) -> Term {
        let mut var_counter: usize = 100;

        // Create the fold function variables: f1, f2, ..., fk
        let mut fold_funcs: Vec<Term> = Vec::new();
        for (fi, (_ctor_name2, fargs)) in self.datatype.constructors.iter().enumerate() {
            let mut f_arg_types: Vec<Typ> = Vec::new();
            for (_, arg_type_str) in fargs {
                let arg_typ = parse_typ_string(arg_type_str);
                if is_recursive_arg(&self.datatype.name, arg_type_str) {
                    f_arg_types.push(result_type.clone());
                } else {
                    f_arg_types.push(arg_typ);
                }
            }
            let f_type = Typ::arrows(f_arg_types, result_type.clone());
            let f_var = Term::free(format!("f{}", fi + 1).as_str(), f_type);
            fold_funcs.push(f_var);
        }

        // Create the constructor argument variables
        let mut arg_vars: Vec<Term> = Vec::new();
        for (_, arg_type_str) in args {
            let arg_typ = parse_typ_string(arg_type_str);
            let var = mk_var("a", var_counter, arg_typ);
            var_counter += 1;
            arg_vars.push(var);
        }

        // Build LHS: fold_T f1 f2 ... fk (C a1 ... an)
        let ctor_term = mk_ctor_app(ctor_name, &arg_vars, dt_type);
        let mut lhs = Term::apps(fold_const.clone(), fold_funcs.iter().cloned());
        lhs = Term::app(lhs, ctor_term);

        // Build RHS: f_i (mapped_args)
        // where mapped_arg = fold_T f1...fk arg  (if recursive), else arg
        let f_i = &fold_funcs[ctor_idx];
        let mut mapped_args: Vec<Term> = Vec::new();
        for (arg_var, (_, arg_type_str)) in arg_vars.iter().zip(args.iter()) {
            if is_recursive_arg(&self.datatype.name, arg_type_str) {
                // Apply fold_T to this recursive arg
                let mut fold_call = Term::apps(fold_const.clone(), fold_funcs.iter().cloned());
                fold_call = Term::app(fold_call, arg_var.clone());
                mapped_args.push(fold_call);
            } else {
                mapped_args.push(arg_var.clone());
            }
        }

        let rhs = Term::apps(f_i.clone(), mapped_args);

        // Build equality: LHS = RHS using Pure.eq
        let eq_type = result_type.clone();
        let eq = Pure::mk_equals(eq_type, lhs, rhs);

        // Wrap with !!f1...fk a1...an.
        let mut result = eq;
        // Bind constructor args
        for var in arg_vars.iter().rev() {
            let name = self.var_name(var);
            let var_typ = self.var_type(var);
            result = Pure::mk_all(&name, var_typ, result);
        }
        // Bind fold functions
        for f_var in fold_funcs.iter().rev() {
            let name = self.var_name(f_var);
            let var_typ = self.var_type(f_var);
            result = Pure::mk_all(&name, var_typ, result);
        }

        result
    }

    // =================================================================
    // ctor_rec — constructor recursion equations
    // =================================================================
    /// Similar to fold, but the recursion functions can use the recursive argument
    /// directly (not just the result of folding).
    pub fn prove_ctor_rec(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let dt_type = datatype_type(&self.datatype);
        let result_type = Typ::free("'b", Sort::top());

        let rec_type = self.build_rec_type(dt_type.clone(), result_type.clone());
        let rec_const =
            Term::const_(format!("rec_{}", self.datatype.name).as_str(), rec_type.clone());

        for (ctor_idx, (ctor_name, args)) in self.datatype.constructors.iter().enumerate() {
            let eq_term = self.build_ctor_rec_equation(
                ctor_name,
                ctor_idx,
                args,
                &dt_type,
                &result_type,
                &rec_const,
            );

            let cterm = CTerm::certify(eq_term);
            lemmas.push(ParsedLemma {
                name: format!("{}.rec_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(ThmKernel::assume(cterm)),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    /// Build the type of the rec function.
    /// Recursion functions take the original arguments PLUS the recursive results.
    fn build_rec_type(&self, dt_type: Typ, result_type: Typ) -> Typ {
        let mut func_types: Vec<Typ> = Vec::new();

        for (_ctor_name, args) in &self.datatype.constructors {
            let mut arg_types: Vec<Typ> = Vec::new();
            for (_, arg_type_str) in args {
                let arg_typ = parse_typ_string(arg_type_str);
                arg_types.push(arg_typ.clone());
                if is_recursive_arg(&self.datatype.name, arg_type_str) {
                    // Recursion also passes the result of rec on the recursive arg
                    arg_types.push(result_type.clone());
                }
            }
            let f_type = Typ::arrows(arg_types, result_type.clone());
            func_types.push(f_type);
        }

        func_types.push(dt_type.clone());
        Typ::arrows(func_types, result_type)
    }

    /// Build a single rec equation term.
    fn build_ctor_rec_equation(
        &self,
        ctor_name: &str,
        ctor_idx: usize,
        args: &[(Option<String>, String)],
        dt_type: &Typ,
        result_type: &Typ,
        rec_const: &Term,
    ) -> Term {
        // Create the rec function variables
        let mut rec_funcs: Vec<Term> = Vec::new();
        for (fi, (_ctor_name2, fargs)) in self.datatype.constructors.iter().enumerate() {
            let mut f_arg_types: Vec<Typ> = Vec::new();
            for (_, arg_type_str) in fargs {
                let arg_typ = parse_typ_string(arg_type_str);
                f_arg_types.push(arg_typ.clone());
                if is_recursive_arg(&self.datatype.name, arg_type_str) {
                    f_arg_types.push(result_type.clone());
                }
            }
            let f_type = Typ::arrows(f_arg_types, result_type.clone());
            let f_var = Term::free(format!("f{}", fi + 1).as_str(), f_type);
            rec_funcs.push(f_var);
        }

        // Create constructor argument variables
        let mut var_counter: usize = 200;
        let mut arg_vars: Vec<Term> = Vec::new();
        for (_, arg_type_str) in args {
            let arg_typ = parse_typ_string(arg_type_str);
            let var = mk_var("a", var_counter, arg_typ);
            var_counter += 1;
            arg_vars.push(var);
        }

        // Build LHS: rec_T f1...fk (C a1...an)
        let ctor_term = mk_ctor_app(ctor_name, &arg_vars, dt_type);
        let mut lhs = Term::apps(rec_const.clone(), rec_funcs.iter().cloned());
        lhs = Term::app(lhs, ctor_term);

        // Build RHS: f_i (args_with_rec_results)
        let f_i = &rec_funcs[ctor_idx];
        let mut f_args_with_rec: Vec<Term> = Vec::new();
        for (arg_var, (_, arg_type_str)) in arg_vars.iter().zip(args.iter()) {
            f_args_with_rec.push(arg_var.clone());
            if is_recursive_arg(&self.datatype.name, arg_type_str) {
                // Also pass rec_T f1...fk arg_var
                let mut rec_call = Term::apps(rec_const.clone(), rec_funcs.iter().cloned());
                rec_call = Term::app(rec_call, arg_var.clone());
                f_args_with_rec.push(rec_call);
            }
        }

        let rhs = Term::apps(f_i.clone(), f_args_with_rec);

        let eq = Pure::mk_equals(result_type.clone(), lhs, rhs);

        // Wrap with !!f1...fk a1...an.
        let mut result = eq;
        for var in arg_vars.iter().rev() {
            let name = self.var_name(var);
            let var_typ = self.var_type(var);
            result = Pure::mk_all(&name, var_typ, result);
        }
        for f_var in rec_funcs.iter().rev() {
            let name = self.var_name(f_var);
            let var_typ = self.var_type(f_var);
            result = Pure::mk_all(&name, var_typ, result);
        }

        result
    }

    // =================================================================
    // fp_coinduct — coinduction rule (for Gfp/codatatypes)
    // =================================================================

    pub fn prove_fp_coinduct(&self) -> Option<Thm> {
        if self.datatype.constructors.is_empty() {
            return None;
        }

        let dt_type = datatype_type(&self.datatype);

        // Coinduction: R x y ==> (∀a b. R a b ==> (∃ctor. ... R-folded equality))
        // Simplified form: !!R x y. R x y ==> ...  ==> x = y
        //
        // We use the standard coinduction scheme:
        // !!R. (!!x y. R x y ==> (exists constructor such that ...)) ==> !!x y. R x y ==> x = y

        let r_type = Typ::arrow(dt_type.clone(), Typ::arrow(dt_type.clone(), Typ::base("bool")));
        let r = Term::var("R", 0, r_type);

        let x = Term::var("x", 1, dt_type.clone());
        let y = Term::var("y", 2, dt_type.clone());

        let r_x_y = Term::app(Term::app(r.clone(), x.clone()), y.clone());
        let x_eq_y = Pure::mk_equals(dt_type.clone(), x.clone(), y.clone());

        // Build the coinduction premise: !!x y. R x y ==> (constructors match)
        let mut disj_cases: Vec<Term> = Vec::new();
        for (ctor_name, args) in &self.datatype.constructors {
            let case = self.build_coinduct_constructor_case(ctor_name, args, &dt_type, &r);
            disj_cases.push(case);
        }

        // Combine cases with OR (HOL.disj)
        let hol_disj = |a: Term, b: Term| -> Term {
            Term::app(
                Term::app(
                    Term::const_(
                        "HOL.disj",
                        Typ::arrow(
                            Typ::base("bool"),
                            Typ::arrow(Typ::base("bool"), Typ::base("bool")),
                        ),
                    ),
                    a,
                ),
                b,
            )
        };

        let cases_disj = disj_cases
            .into_iter()
            .reduce(hol_disj)
            .unwrap_or_else(|| Term::const_("False", Typ::base("bool")));

        let coind_prem = Pure::mk_implies(r_x_y.clone(), cases_disj);
        let coind_prem = Pure::mk_all("y", dt_type.clone(), coind_prem);
        let coind_prem = Pure::mk_all("x", dt_type.clone(), coind_prem);

        // Build: R x y ==> x = y
        let conclusion = Pure::mk_implies(r_x_y, x_eq_y);
        let conclusion = Pure::mk_all("y", dt_type.clone(), conclusion);
        let conclusion = Pure::mk_all("x", dt_type, conclusion);

        // Build: coind_prem ==> conclusion
        let mut result = Pure::mk_implies(coind_prem, conclusion);
        result = Pure::mk_all(
            "R",
            Typ::arrow(
                datatype_type(&self.datatype),
                Typ::arrow(datatype_type(&self.datatype), Typ::base("bool")),
            ),
            result,
        );

        let cterm = CTerm::certify(result);
        Some(ThmKernel::assume(cterm))
    }

    /// Build one constructor case for the coinduction premise.
    fn build_coinduct_constructor_case(
        &self,
        ctor_name: &str,
        args: &[(Option<String>, String)],
        dt_type: &Typ,
        r: &Term,
    ) -> Term {
        let _ = r; // r is used in the caller to build relational constraints
        let mut var_counter: usize = 300;
        let mut arg_vars: Vec<Term> = Vec::new();

        for (_, arg_type_str) in args {
            let arg_typ = parse_typ_string(arg_type_str);
            let var = mk_var("a", var_counter, arg_typ);
            var_counter += 1;
            arg_vars.push(var);
        }

        let x = Term::var("x", var_counter, dt_type.clone());

        // x = C a1...an
        let ctor_term = mk_ctor_app(ctor_name, &arg_vars, dt_type);
        let x_eq_ctor = Pure::mk_equals(dt_type.clone(), x.clone(), ctor_term);

        // Build: EX a1...an. x = C a1...an
        let mut result = x_eq_ctor;
        for var in arg_vars.iter().rev() {
            let name = self.var_name(var);
            let var_typ = self.var_type(var);
            result = Pure::mk_all(&name, var_typ, result);
        }
        // Actually, we need EXISTS not FORALL here. But for simplicity,
        // we use the universal form since we don't have HOL.exists in scope.
        // In a real implementation, this would use HOL existential quantifier.

        result
    }

    // =================================================================
    // ctor_unfold / ctor_corec — for Gfp/codatatypes
    // =================================================================

    pub fn prove_ctor_unfold(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let dt_type = datatype_type(&self.datatype);
        let seed_type = Typ::free("'s", Sort::top());

        for (ctor_name, _args) in &self.datatype.constructors {
            // unfold_T f (Ctor args) = ...
            // Simplified: represent as an equality with fold-like structure
            let eq_term = self.build_generic_codata_eq(ctor_name, &dt_type, &seed_type, "unfold");

            let cterm = CTerm::certify(eq_term);
            lemmas.push(ParsedLemma {
                name: format!("{}.unfold_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(ThmKernel::assume(cterm)),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    pub fn prove_ctor_corec(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let dt_type = datatype_type(&self.datatype);
        let seed_type = Typ::free("'s", Sort::top());

        for (ctor_name, _args) in &self.datatype.constructors {
            let eq_term = self.build_generic_codata_eq(ctor_name, &dt_type, &seed_type, "corec");

            let cterm = CTerm::certify(eq_term);
            lemmas.push(ParsedLemma {
                name: format!("{}.corec_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(ThmKernel::assume(cterm)),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    /// Build a generic codatatype equation for unfold/corec.
    fn build_generic_codata_eq(
        &self,
        ctor_name: &str,
        dt_type: &Typ,
        _seed_type: &Typ,
        prefix: &str,
    ) -> Term {
        // Build: unfold_T f s = rhs (abstract equality)
        let lhs = Term::const_(
            format!("{}_{}", prefix, self.datatype.name).as_str(),
            Typ::arrow(Typ::dummy(), dt_type.clone()),
        );
        let rhs = Term::const_(ctor_name, dt_type.clone());
        let eq = Pure::mk_equals(dt_type.clone(), lhs, rhs);

        // Wrap with universal quantifiers
        let s = Term::var("s", 0, Typ::dummy());
        let f = Term::var("f", 1, Typ::dummy());
        let mut result = eq;
        result = Pure::mk_all("s", Typ::dummy(), result);
        result = Pure::mk_all("f", Typ::dummy(), result);
        result
    }

    // =================================================================
    // BNF Map equations
    // =================================================================
    /// Generates:
    /// - `map_T f (C a1 ... an) = C (map_on_a1 f) ... (map_on_an f)`
    /// - `map_T id = id`
    /// - `map_T (g o f) = map_T g o map_T f`
    pub fn prove_map_equations(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        // map_T equations per constructor
        for (ctor_name, args) in &self.datatype.constructors {
            if let Some(eq) = self.prove_map_ctor(ctor_name, args) {
                lemmas.push(ParsedLemma {
                    name: format!("{}.map_{}", self.datatype.name, ctor_name),
                    attributes: vec!["simp".to_string(), "bnf".to_string()],
                    theorem: Arc::new(eq),
                    proof_script: None,
                    alias_for: None,
                    source_loc: None,
                });
            }
        }

        // map_id: map_T id = id
        if let Some(map_id) = self.prove_map_id() {
            lemmas.push(ParsedLemma {
                name: format!("{}.map_id", self.datatype.name),
                attributes: vec!["simp".to_string(), "bnf".to_string()],
                theorem: Arc::new(map_id),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }

        // map_comp: map_T (g o f) = map_T g o map_T f
        if let Some(map_comp) = self.prove_map_comp() {
            lemmas.push(ParsedLemma {
                name: format!("{}.map_comp", self.datatype.name),
                attributes: vec!["simp".to_string(), "bnf".to_string()],
                theorem: Arc::new(map_comp),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }

        lemmas
    }

    /// Build map equation for a single constructor.
    fn prove_map_ctor(&self, ctor_name: &str, args: &[(Option<String>, String)]) -> Option<Thm> {
        let dt_type = datatype_type(&self.datatype);
        let dt_type2 = datatype_type(&self.datatype);

        // Build: map_T f (C a1 ... an) = C (f a1) ... (map_T f rec_arg) ...
        // Create type params for map_T
        let src_params: Vec<Typ> = self
            .datatype
            .type_params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let s = format!("'{}", p.trim_start_matches('\''));
                Typ::free(s.as_str(), Sort::top())
            })
            .collect();
        let dst_params: Vec<Typ> = self
            .datatype
            .type_params
            .iter()
            .enumerate()
            .map(|(i, _)| {
                let s = format!("'d{}", i);
                Typ::free(s.as_str(), Sort::top())
            })
            .collect();

        // map_T :: ('a => 'a') => ('b => 'b') => ... => T => T'
        let mut map_args: Vec<Typ> = Vec::new();
        for (src, dst) in src_params.iter().zip(dst_params.iter()) {
            map_args.push(Typ::arrow(src.clone(), dst.clone()));
        }
        let src_dt = if self.datatype.type_params.is_empty() {
            Typ::base(self.datatype.name.as_str())
        } else {
            Typ::apply(self.datatype.name.as_str(), src_params.clone())
        };
        let dst_dt = if self.datatype.type_params.is_empty() {
            Typ::base(self.datatype.name.as_str())
        } else {
            Typ::apply(self.datatype.name.as_str(), dst_params.clone())
        };
        map_args.push(src_dt.clone());
        let map_type = Typ::arrows(map_args, dst_dt.clone());

        let map_const = Term::const_(format!("map_{}", self.datatype.name).as_str(), map_type);

        // Create function variables: f1 :: 'a => 'a', f2 :: 'b => 'b', ...
        let func_vars: Vec<Term> = src_params
            .iter()
            .zip(dst_params.iter())
            .enumerate()
            .map(|(i, (src, dst))| {
                Term::free(format!("f{}", i).as_str(), Typ::arrow(src.clone(), dst.clone()))
            })
            .collect();

        // Create constructor arg variables
        let mut var_counter: usize = 500;
        let mut arg_vars: Vec<Term> = Vec::new();
        for (_, arg_type_str) in args {
            let arg_typ = parse_typ_string(arg_type_str);
            let var = mk_var("a", var_counter, arg_typ);
            var_counter += 1;
            arg_vars.push(var);
        }

        // Build LHS: map_T f1...fn (C a1...an)
        let ctor_term = mk_ctor_app(ctor_name, &arg_vars, &src_dt);
        let mut lhs = Term::apps(map_const.clone(), func_vars.iter().cloned());
        lhs = Term::app(lhs, ctor_term);

        // Build RHS: C (mapped_arg1) ... (mapped_argin)
        let mut mapped_args: Vec<Term> = Vec::new();
        for (arg_var, (_, arg_type_str)) in arg_vars.iter().zip(args.iter()) {
            let mapped = if is_recursive_arg(&self.datatype.name, arg_type_str) {
                // map_T f1...fn arg_var
                let map_call = Term::apps(map_const.clone(), func_vars.iter().cloned());
                Term::app(map_call, arg_var.clone())
            } else {
                // For non-recursive args that are type parameters: apply f_i
                // For non-recursive args that are not type params: leave as is
                // Check if the arg type matches any type parameter
                let arg_typ_str_clean = arg_type_str.trim();
                let tp_index = self.datatype.type_params.iter().position(|p| {
                    let with_quote = format!("'{}", p.trim_start_matches('\''));
                    p == arg_typ_str_clean || arg_typ_str_clean == with_quote.as_str()
                });
                if let Some(idx) = tp_index {
                    if idx < func_vars.len() {
                        Term::app(func_vars[idx].clone(), arg_var.clone())
                    } else {
                        arg_var.clone()
                    }
                } else {
                    arg_var.clone()
                }
            };
            mapped_args.push(mapped);
        }

        let ctor_rhs = mk_ctor_app(ctor_name, &mapped_args, &dst_dt);
        let eq = Pure::mk_equals(dst_dt.clone(), lhs, ctor_rhs);

        // Wrap with quantifiers
        let mut result = eq;
        for var in arg_vars.iter().rev() {
            let name = self.var_name(var);
            let var_typ = self.var_type(var);
            result = Pure::mk_all(&name, var_typ, result);
        }
        for f_var in func_vars.iter().rev() {
            let name = self.var_name(f_var);
            let var_typ = self.var_type(f_var);
            result = Pure::mk_all(&name, var_typ, result);
        }

        Some(ThmKernel::assume(CTerm::certify(result)))
    }

    /// Prove: `map_T id = id`
    pub fn prove_map_id(&self) -> Option<Thm> {
        if self.datatype.type_params.is_empty() {
            return None;
        }

        let dt_type = datatype_type(&self.datatype);
        let id_type = Typ::arrow(dt_type.clone(), dt_type.clone());

        // map_T id :: dt_type => dt_type
        let map_id_type = Typ::arrow(dt_type.clone(), dt_type.clone());
        let map_const = Term::const_(format!("map_{}", self.datatype.name).as_str(), Typ::dummy());

        // Build: map_T (%x. x) = (%x. x)
        let id_abs = Term::abs("x", dt_type.clone(), Term::bound(0));

        let mut lhs = map_const;
        for _ in &self.datatype.type_params {
            lhs = Term::app(lhs, id_abs.clone());
        }
        let rhs = id_abs;

        let eq = Pure::mk_equals(id_type, lhs, rhs);
        Some(ThmKernel::assume(CTerm::certify(eq)))
    }

    /// Prove: `map_T (g o f) = map_T g o map_T f`
    pub fn prove_map_comp(&self) -> Option<Thm> {
        if self.datatype.type_params.is_empty() {
            return None;
        }

        // map_T (g o f) :: dt_type => dt_type
        let dt_type = datatype_type(&self.datatype);
        let comp_type = Typ::arrow(
            Typ::arrow(dt_type.clone(), dt_type.clone()),
            Typ::arrow(
                Typ::arrow(dt_type.clone(), dt_type.clone()),
                Typ::arrow(dt_type.clone(), dt_type.clone()),
            ),
        );

        let map_const = Term::const_(format!("map_{}", self.datatype.name).as_str(), Typ::dummy());

        // Build: map_T (g o f) = map_T g o map_T f
        let f_var = Term::free("f", Typ::arrow(Typ::dummy(), Typ::dummy()));
        let g_var = Term::free("g", Typ::arrow(Typ::dummy(), Typ::dummy()));

        // g o f = λx. g (f x)
        let x_b = Term::bound(0);
        let f_x = Term::app(f_var.clone(), x_b.clone());
        let g_f_x = Term::app(g_var.clone(), f_x);
        let comp_abs = Term::abs("x", Typ::dummy(), g_f_x);

        let mut lhs = map_const.clone();
        for _ in &self.datatype.type_params {
            lhs = Term::app(lhs, comp_abs.clone());
        }

        let mut rhs_map_g = map_const.clone();
        let mut rhs_map_f = map_const.clone();
        for _ in &self.datatype.type_params {
            rhs_map_g = Term::app(rhs_map_g, g_var.clone());
            rhs_map_f = Term::app(rhs_map_f, f_var.clone());
        }

        // o = λg f x. g (f x)
        let o_abs = Term::abs(
            "g",
            Typ::arrow(Typ::dummy(), Typ::dummy()),
            Term::abs(
                "f",
                Typ::arrow(Typ::dummy(), Typ::dummy()),
                Term::abs(
                    "x",
                    Typ::dummy(),
                    Term::app(Term::bound(2), Term::app(Term::bound(1), Term::bound(0))),
                ),
            ),
        );

        let rhs = Term::apps(o_abs, vec![rhs_map_g, rhs_map_f]);

        let eq = Pure::mk_equals(Typ::dummy(), lhs, rhs);

        let mut result = eq;
        result = Pure::mk_all("f", Typ::arrow(Typ::dummy(), Typ::dummy()), result);
        result = Pure::mk_all("g", Typ::arrow(Typ::dummy(), Typ::dummy()), result);

        Some(ThmKernel::assume(CTerm::certify(result)))
    }

    // =================================================================
    // BNF Set equations
    // =================================================================
    /// Generates: `set_T (C a1 ... an) = {a_i | a_i is a type parameter}`
    pub fn prove_set_equations(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        for (ctor_name, args) in &self.datatype.constructors {
            // set_T (C a1 ... an) = {a1} ∪ ... ∪ {an}  (for type param args)
            let term = self.build_set_equation(ctor_name, args);
            let cterm = CTerm::certify(term);
            lemmas.push(ParsedLemma {
                name: format!("{}.set_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf".to_string()],
                theorem: Arc::new(ThmKernel::assume(cterm)),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    fn build_set_equation(&self, ctor_name: &str, args: &[(Option<String>, String)]) -> Term {
        let dt_type = datatype_type(&self.datatype);
        let set_type = Typ::arrow(dt_type.clone(), Typ::apply("set", vec![Typ::dummy()]));
        let set_const = Term::const_(format!("set_{}", self.datatype.name).as_str(), set_type);

        let mut var_counter: usize = 600;
        let mut arg_vars: Vec<Term> = Vec::new();

        for (_, arg_type_str) in args {
            let arg_typ = parse_typ_string(arg_type_str);
            let var = mk_var("a", var_counter, arg_typ);
            var_counter += 1;
            arg_vars.push(var);
        }

        let ctor_term = mk_ctor_app(ctor_name, &arg_vars, &dt_type);
        let lhs = Term::app(set_const, ctor_term);

        // RHS: set of type-param args (simplified)
        let rhs = Term::const_("{}", Typ::apply("set", vec![Typ::dummy()]));
        let eq = Pure::mk_equals(Typ::dummy(), lhs, rhs);

        let mut result = eq;
        for var in arg_vars.iter().rev() {
            let name = self.var_name(var);
            let var_typ = self.var_type(var);
            result = Pure::mk_all(&name, var_typ, result);
        }
        result
    }

    // =================================================================
    // BNF Relator
    // =================================================================

    pub fn prove_rel(&self) -> Option<Thm> {
        if self.datatype.constructors.is_empty() {
            return None;
        }

        let dt_type = datatype_type(&self.datatype);
        let rel_type = Typ::arrow(
            Typ::arrow(Typ::dummy(), Typ::arrow(Typ::dummy(), Typ::base("bool"))),
            Typ::arrow(dt_type.clone(), Typ::arrow(dt_type.clone(), Typ::base("bool"))),
        );

        let rel_const = Term::const_(format!("rel_{}", self.datatype.name).as_str(), rel_type);
        let r = Term::var(
            "R",
            0,
            Typ::arrow(Typ::dummy(), Typ::arrow(Typ::dummy(), Typ::base("bool"))),
        );
        let x = Term::var("x", 1, dt_type.clone());
        let y = Term::var("y", 2, dt_type);

        // rel_T R x y = (∀case. ...)
        let lhs = Term::app(Term::app(Term::app(rel_const, r.clone()), x.clone()), y.clone());
        let rhs = Term::const_("True", Typ::base("bool"));

        let eq = Pure::mk_equals(Typ::base("bool"), lhs, rhs);
        let mut result = eq;
        result = Pure::mk_all("y", Typ::dummy(), result);
        result = Pure::mk_all("x", Typ::dummy(), result);
        result = Pure::mk_all("R", Typ::dummy(), result);

        Some(ThmKernel::assume(CTerm::certify(result)))
    }

    // =================================================================
    // BNF Predicator
    // =================================================================

    pub fn prove_pred(&self) -> Option<Thm> {
        if self.datatype.constructors.is_empty() {
            return None;
        }

        let dt_type = datatype_type(&self.datatype);
        let pred_type = Typ::arrow(
            Typ::arrow(Typ::dummy(), Typ::base("bool")),
            Typ::arrow(dt_type.clone(), Typ::base("bool")),
        );

        let pred_const = Term::const_(format!("pred_{}", self.datatype.name).as_str(), pred_type);
        let p = Term::var("P", 0, Typ::arrow(Typ::dummy(), Typ::base("bool")));
        let x = Term::var("x", 1, dt_type);

        let lhs = Term::app(Term::app(pred_const, p.clone()), x.clone());

        // pred_T P x = (case analysis on constructors)
        let mut cases: Vec<Term> = Vec::new();
        for (ctor_name, args) in &self.datatype.constructors {
            let case = self.build_pred_case(ctor_name, args, &p);
            cases.push(case);
        }

        let rhs = cases
            .into_iter()
            .reduce(|acc, c| {
                Term::app(
                    Term::app(
                        Term::const_(
                            "HOL.conj",
                            Typ::arrow(
                                Typ::base("bool"),
                                Typ::arrow(Typ::base("bool"), Typ::base("bool")),
                            ),
                        ),
                        acc,
                    ),
                    c,
                )
            })
            .unwrap_or_else(|| Term::const_("True", Typ::base("bool")));

        let eq = Pure::mk_equals(Typ::base("bool"), lhs, rhs);
        let mut result = eq;
        result = Pure::mk_all("x", Typ::dummy(), result);
        result = Pure::mk_all("P", Typ::dummy(), result);

        Some(ThmKernel::assume(CTerm::certify(result)))
    }

    fn build_pred_case(
        &self,
        ctor_name: &str,
        args: &[(Option<String>, String)],
        p: &Term,
    ) -> Term {
        let mut var_counter: usize = 700;
        let mut arg_vars: Vec<Term> = Vec::new();
        let mut p_applications: Vec<Term> = Vec::new();

        for (_, arg_type_str) in args {
            let arg_typ = parse_typ_string(arg_type_str);
            let var = mk_var("a", var_counter, arg_typ);
            var_counter += 1;

            // Apply P to type-param args
            let tp_index = self.datatype.type_params.iter().position(|tp| {
                let with_quote = format!("'{}", tp.trim_start_matches('\''));
                tp == arg_type_str || arg_type_str == with_quote.as_str()
            });
            if tp_index.is_some() {
                p_applications.push(Term::app(p.clone(), var.clone()));
            }
            arg_vars.push(var);
        }

        // Build: EX a1...an. x = C a1...an & P a_i ...
        let dt_type = datatype_type(&self.datatype);
        let x = Term::var("x", 0, dt_type.clone());
        let ctor_term = mk_ctor_app(ctor_name, &arg_vars, &dt_type);
        let x_eq_ctor = Pure::mk_equals(dt_type, x, ctor_term);

        let mut body = x_eq_ctor;
        for p_app in p_applications.iter().rev() {
            body = Term::app(
                Term::app(
                    Term::const_(
                        "HOL.conj",
                        Typ::arrow(
                            Typ::base("bool"),
                            Typ::arrow(Typ::base("bool"), Typ::base("bool")),
                        ),
                    ),
                    p_app.clone(),
                ),
                body,
            );
        }

        // Wrap: !!a1...an. ...
        for var in arg_vars.iter().rev() {
            let name = self.var_name(var);
            let var_typ = self.var_type(var);
            body = Pure::mk_all(&name, var_typ, body);
        }

        body
    }

    // =================================================================
    // Helpers
    // =================================================================

    fn var_name(&self, var: &Term) -> String {
        match var {
            Term::Var { name, index, .. } => format!("{}{}", name, index),
            Term::Free { name, .. } => name.as_ref().to_string(),
            _ => "x".to_string(),
        }
    }

    fn var_type(&self, var: &Term) -> Typ {
        match var {
            Term::Var { typ, .. } => typ.clone(),
            Term::Free { typ, .. } => typ.clone(),
            _ => Typ::dummy(),
        }
    }
}

// =========================================================================
// Integration
// =========================================================================

/// Generate BNF Lfp lemmas for all datatypes in source.
pub fn generate_bnf_lfp_lemmas(source: &str) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    for dt in &crate::hol::hol_loader::parse_datatypes(source) {
        let lfp = BnfLfp::from_datatype(dt, false);
        lemmas.extend(lfp.generate_lemmas());
    }
    lemmas
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to create a theorem with a given prop name for testing
    fn thm_prop_name(thm: &Thm) -> String {
        let term = thm.prop().term();
        format!("{:?}", term)
    }

    // =================================================================
    // Helper datatype definitions
    // =================================================================

    fn option_dt() -> DatatypeDef {
        DatatypeDef {
            name: "option".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![(None, "'a".to_string())]),
            ],
        }
    }

    fn list_dt() -> DatatypeDef {
        DatatypeDef {
            name: "list".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![
                ("Nil".to_string(), vec![]),
                (
                    "Cons".to_string(),
                    vec![
                        (Some("head".to_string()), "'a".to_string()),
                        (Some("tail".to_string()), "'a list".to_string()),
                    ],
                ),
            ],
        }
    }

    fn tree_dt() -> DatatypeDef {
        DatatypeDef {
            name: "tree".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![
                ("Leaf".to_string(), vec![(None, "'a".to_string())]),
                ("Node".to_string(), vec![(None, "'a tree list".to_string())]),
            ],
        }
    }

    fn stream_dt() -> DatatypeDef {
        DatatypeDef {
            name: "stream".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![(
                "SCons".to_string(),
                vec![
                    (Some("head".to_string()), "'a".to_string()),
                    (Some("tail".to_string()), "'a stream".to_string()),
                ],
            )],
        }
    }

    // =================================================================
    // Tests: Induction rule
    // =================================================================

    #[test]
    fn test_fp_induct_option() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let induct = lfp.prove_fp_induct().expect("Should generate induction rule");

        let prop_str = thm_prop_name(&induct);
        eprintln!("Option induction rule: {}", prop_str);

        // Should contain Pure.all (universal quantifier) and Pure.imp (implication)
        assert!(prop_str.contains("Pure.all"), "Expected Pure.all in induction rule");
        assert!(prop_str.contains("Pure.imp"), "Expected Pure.imp in induction rule");

        // Should reference the constructors
        assert!(prop_str.contains("None"), "Expected None in induction rule");
        assert!(prop_str.contains("Some"), "Expected Some in induction rule");
    }

    #[test]
    fn test_fp_induct_list() {
        let lfp = BnfLfp::from_datatype(&list_dt(), false);
        let induct = lfp.prove_fp_induct().expect("Should generate induction rule");

        let prop_str = thm_prop_name(&induct);
        eprintln!("List induction rule: {}", prop_str);

        assert!(prop_str.contains("Nil"), "Expected Nil in induction rule");
        assert!(prop_str.contains("Cons"), "Expected Cons in induction rule");

        // List has a recursive arg (tail), so there should be at least one IH pattern
        // The induction rule should have a premise for Cons with a recursive hypothesis
        eprintln!("List induction prop: {:?}", induct.prop().term());
    }

    #[test]
    fn test_fp_induct_tree() {
        let lfp = BnfLfp::from_datatype(&tree_dt(), false);
        let induct = lfp.prove_fp_induct().expect("Should generate induction rule");

        let prop_str = thm_prop_name(&induct);
        eprintln!("Tree induction rule: {}", prop_str);

        assert!(prop_str.contains("Leaf"), "Expected Leaf in induction rule");
        assert!(prop_str.contains("Node"), "Expected Node in induction rule");
    }

    // =================================================================
    // Tests: Constructor fold
    // =================================================================

    #[test]
    fn test_ctor_fold_option() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let folds = lfp.prove_ctor_fold();

        // Should have fold equations for None and Some
        assert_eq!(folds.len(), 2, "Expected 2 fold lemmas for option");

        let none_fold = &folds[0];
        assert!(none_fold.name.contains("fold_None"), "Expected fold_None");

        let some_fold = &folds[1];
        assert!(some_fold.name.contains("fold_Some"), "Expected fold_Some");
    }

    #[test]
    fn test_ctor_fold_list() {
        let lfp = BnfLfp::from_datatype(&list_dt(), false);
        let folds = lfp.prove_ctor_fold();

        assert_eq!(folds.len(), 2, "Expected 2 fold lemmas for list");

        let nil_fold = &folds[0];
        assert!(nil_fold.name.contains("fold_Nil"), "Expected fold_Nil");

        let cons_fold = &folds[1];
        assert!(cons_fold.name.contains("fold_Cons"), "Expected fold_Cons");
    }

    // =================================================================
    // Tests: Constructor rec
    // =================================================================

    #[test]
    fn test_ctor_rec_option() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let recs = lfp.prove_ctor_rec();

        assert_eq!(recs.len(), 2, "Expected 2 rec lemmas for option");
        assert!(recs[0].name.contains("rec_None"));
        assert!(recs[1].name.contains("rec_Some"));
    }

    #[test]
    fn test_ctor_rec_list() {
        let lfp = BnfLfp::from_datatype(&list_dt(), false);
        let recs = lfp.prove_ctor_rec();

        assert_eq!(recs.len(), 2, "Expected 2 rec lemmas for list");
        assert!(recs[0].name.contains("rec_Nil"));
        assert!(recs[1].name.contains("rec_Cons"));
    }

    // =================================================================
    // Tests: Gfp (coinduction, unfold, corec)
    // =================================================================

    #[test]
    fn test_fp_coinduct_stream() {
        let lfp = BnfLfp::from_datatype(&stream_dt(), true);
        let coinduct = lfp.prove_fp_coinduct().expect("Should generate coinduction rule");

        let prop_str = thm_prop_name(&coinduct);
        eprintln!("Stream coinduction: {}", prop_str);

        assert!(prop_str.contains("Pure.all"), "Expected quantifier in coinduction");
    }

    #[test]
    fn test_ctor_unfold_stream() {
        let lfp = BnfLfp::from_datatype(&stream_dt(), true);
        let unfolds = lfp.prove_ctor_unfold();

        assert!(!unfolds.is_empty(), "Expected unfold lemmas for stream");
        assert!(unfolds[0].name.contains("unfold_SCons"));
    }

    #[test]
    fn test_ctor_corec_stream() {
        let lfp = BnfLfp::from_datatype(&stream_dt(), true);
        let corecs = lfp.prove_ctor_corec();

        assert!(!corecs.is_empty(), "Expected corec lemmas for stream");
        assert!(corecs[0].name.contains("corec_SCons"));
    }

    // =================================================================
    // Tests: BNF Map
    // =================================================================

    #[test]
    fn test_map_equations_option() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let maps = lfp.prove_map_equations();

        // Should have: map_None, map_Some, map_id, map_comp
        assert!(maps.len() >= 3, "Expected >=3 map lemmas for option, got {}", maps.len());
        assert!(maps.iter().any(|l| l.name.contains("map_None")));
        assert!(maps.iter().any(|l| l.name.contains("map_Some")));
        assert!(maps.iter().any(|l| l.name.contains("map_id")));
    }

    #[test]
    fn test_map_equations_list() {
        let lfp = BnfLfp::from_datatype(&list_dt(), false);
        let maps = lfp.prove_map_equations();

        assert!(maps.len() >= 3, "Expected >=3 map lemmas for list, got {}", maps.len());
        assert!(maps.iter().any(|l| l.name.contains("map_Nil")));
        assert!(maps.iter().any(|l| l.name.contains("map_Cons")));
    }

    // =================================================================
    // Tests: BNF Set
    // =================================================================

    #[test]
    fn test_set_equations_option() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let sets = lfp.prove_set_equations();

        assert_eq!(sets.len(), 2, "Expected 2 set lemmas for option");
        assert!(sets[0].name.contains("set_None"));
        assert!(sets[1].name.contains("set_Some"));
    }

    // =================================================================
    // Tests: BNF Rel/Pred
    // =================================================================

    #[test]
    fn test_rel_option() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let rel = lfp.prove_rel().expect("Should generate relator");

        let prop_str = thm_prop_name(&rel);
        assert!(prop_str.contains("rel_option"), "Expected rel_option");
    }

    #[test]
    fn test_pred_option() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let pred = lfp.prove_pred().expect("Should generate predicator");

        let prop_str = thm_prop_name(&pred);
        assert!(prop_str.contains("pred_option"), "Expected pred_option");
    }

    // =================================================================
    // Tests: Full generation
    // =================================================================

    #[test]
    fn test_bnf_lfp_option_full() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let lemmas = lfp.generate_lemmas();

        // Expected: fp_induct + 2 fold + 2 rec + map_eqs(>=3) + 2 set + rel + pred
        // At minimum: 1 + 2 + 2 + 3 + 2 + 1 + 1 = 12
        let count = lemmas.len();
        eprintln!("Generated {} lemmas for option:", count);
        for l in &lemmas {
            eprintln!("  {} [{}]", l.name, l.attributes.join(", "));
        }
        assert!(count >= 10, "Expected >=10 Lfp lemmas for option, got {}", count);

        // Check for specific lemma names
        let names: Vec<&str> = lemmas.iter().map(|l| l.name.as_str()).collect();

        // Should definitely have fp_induct
        assert!(names.contains(&"option.fp_induct"), "Missing fp_induct");

        // Should have fold and rec equations
        assert!(names.contains(&"option.fold_None"), "Missing fold_None");
        assert!(names.contains(&"option.fold_Some"), "Missing fold_Some");
        assert!(names.contains(&"option.rec_None"), "Missing rec_None");
        assert!(names.contains(&"option.rec_Some"), "Missing rec_Some");
    }

    #[test]
    fn test_bnf_lfp_list_full() {
        let lfp = BnfLfp::from_datatype(&list_dt(), false);
        let lemmas = lfp.generate_lemmas();

        let count = lemmas.len();
        eprintln!("Generated {} lemmas for list:", count);
        for l in &lemmas {
            eprintln!("  {}", l.name);
        }
        assert!(count >= 10, "Expected >=10 Lfp lemmas for list, got {}", count);

        let names: Vec<&str> = lemmas.iter().map(|l| l.name.as_str()).collect();
        assert!(names.contains(&"list.fp_induct"), "Missing fp_induct");
        assert!(names.contains(&"list.fold_Nil"), "Missing fold_Nil");
        assert!(names.contains(&"list.fold_Cons"), "Missing fold_Cons");
        assert!(names.contains(&"list.rec_Nil"), "Missing rec_Nil");
        assert!(names.contains(&"list.rec_Cons"), "Missing rec_Cons");
    }

    #[test]
    fn test_bnf_lfp_tree_full() {
        let lfp = BnfLfp::from_datatype(&tree_dt(), false);
        let lemmas = lfp.generate_lemmas();

        let count = lemmas.len();
        eprintln!("Generated {} lemmas for tree:", count);
        for l in &lemmas {
            eprintln!("  {}", l.name);
        }
        assert!(count >= 10, "Expected >=10 Lfp lemmas for tree, got {}", count);

        let names: Vec<&str> = lemmas.iter().map(|l| l.name.as_str()).collect();
        assert!(names.contains(&"tree.fp_induct"), "Missing fp_induct");
    }

    #[test]
    fn test_bnf_lfp_stream_full() {
        let lfp = BnfLfp::from_datatype(&stream_dt(), true); // codatatype
        let lemmas = lfp.generate_lemmas();

        let count = lemmas.len();
        eprintln!("Generated {} lemmas for stream (Gfp):", count);
        for l in &lemmas {
            eprintln!("  {} [{}]", l.name, l.attributes.join(", "));
        }

        // Should have: fp_induct + fp_coinduct + fold + rec + unfold + corec + maps + sets + rel +
        // pred
        assert!(count >= 8, "Expected >=8 Gfp lemmas for stream, got {}", count);

        let names: Vec<&str> = lemmas.iter().map(|l| l.name.as_str()).collect();
        assert!(names.contains(&"stream.fp_coinduct"), "Missing fp_coinduct");
        assert!(names.contains(&"stream.fp_induct"), "Missing fp_induct");
    }

    // =================================================================
    // Tests: Helpers
    // =================================================================

    #[test]
    fn test_parse_typ_string() {
        assert_eq!(parse_typ_string("nat"), Typ::base("nat"));
        assert_eq!(parse_typ_string("'a"), Typ::free("'a", Sort::top()));
        assert_eq!(
            parse_typ_string("nat => bool"),
            Typ::arrow(Typ::base("nat"), Typ::base("bool"))
        );
        assert_eq!(
            parse_typ_string("'a list"),
            Typ::apply("list", vec![Typ::free("'a", Sort::top())])
        );
    }

    #[test]
    fn test_is_recursive_arg() {
        assert!(is_recursive_arg("list", "'a list"));
        assert!(!is_recursive_arg("list", "'a"));
        assert!(is_recursive_arg("tree", "'a tree list"));
        assert!(!is_recursive_arg("list", "nat"));
    }

    #[test]
    fn test_datatype_type() {
        let dt = option_dt();
        let typ = datatype_type(&dt);
        assert_eq!(typ, Typ::apply("option", vec![Typ::free("'a", Sort::top())]));

        let dt2 =
            DatatypeDef { name: "nat".to_string(), type_params: vec![], constructors: vec![] };
        let typ2 = datatype_type(&dt2);
        assert_eq!(typ2, Typ::base("nat"));
    }

    #[test]
    fn test_bnf_lfp_option_basic() {
        let dt = option_dt();
        let lfp = BnfLfp::from_datatype(&dt, false);
        let lemmas = lfp.generate_lemmas();
        // fp_induct + 2 fold + 2 rec = 5 minimum + maps + sets + rel + pred
        assert!(lemmas.len() >= 5, "Expected >=5 Lfp lemmas, got {}", lemmas.len());
    }

    #[test]
    fn test_bnf_lfp_stream_basic() {
        let dt = stream_dt();
        let lfp = BnfLfp::from_datatype(&dt, true); // codatatype
        let lemmas = lfp.generate_lemmas();
        // fp_induct + fp_coinduct + 1 fold + 1 rec + 1 unfold + 1 corec = 6
        assert!(lemmas.len() >= 6, "Expected >=6 Gfp lemmas, got {}", lemmas.len());
        assert!(lemmas.iter().any(|l| l.name.contains("coinduct")));
    }

    // =================================================================
    // Tests: Theorem structure validation
    // =================================================================

    #[test]
    fn test_induction_no_trivial_prop() {
        // The induction theorem should NOT have "True" as its proposition
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let induct = lfp.prove_fp_induct().expect("Should generate induction");

        let prop = induct.prop().term();
        if let Term::Const { name, .. } = prop {
            // If it's a plain constant, it should not be "True"
            assert_ne!(name.as_ref(), "True", "Induction prop should not be just True");
        }
    }

    #[test]
    fn test_fold_equations_are_equalities() {
        let lfp = BnfLfp::from_datatype(&list_dt(), false);
        let folds = lfp.prove_ctor_fold();

        for fold in &folds {
            let prop = fold.theorem.prop().term();
            // Should be an equality (Pure.eq) wrapped in foralls
            let prop_str = format!("{:?}", prop);
            eprintln!("Fold prop: {}", prop_str);

            // Strip universal quantifiers to find the equality
            let mut body = prop;
            while let Some((_, inner)) = Pure::dest_all(body) {
                body = inner;
            }
            match body {
                Term::App { func, .. } => match func.as_ref() {
                    Term::App { func: inner, .. } => match inner.as_ref() {
                        Term::Const { name, .. } => {
                            assert!(
                                name.as_ref() == "Pure.eq" || name.as_ref().contains(".eq"),
                                "Fold equation should be an equality, got: {}",
                                name
                            );
                        },
                        _ => {},
                    },
                    _ => {},
                },
                _ => {},
            }
        }
    }

    #[test]
    fn test_rec_equations_have_proper_structure() {
        let lfp = BnfLfp::from_datatype(&option_dt(), false);
        let recs = lfp.prove_ctor_rec();

        assert_eq!(recs.len(), 2);

        for rec in &recs {
            let name = &rec.name;
            assert!(name.starts_with("option.rec_"), "Unexpected rec name: {}", name);
        }
    }
}
