//! Tests for propositional (pure-CNF) Craig interpolation.
//!
//! Every test independently re-verifies the three Craig conditions on the side
//! of the test (via SAT over a Tseitin re-encoding), so a test never merely
//! trusts that `propositional_interpolant` checked its own output.

use axeyum_cnf::{
    BoolExpr, CnfClause, CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, check_drat,
    propositional_interpolant, solve_with_drat_proof,
};

/// Builds a literal from a signed DIMACS value over a shared variable space.
fn lit(value: i64) -> CnfLit {
    let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
    if value < 0 {
        CnfLit::positive(var).negated()
    } else {
        CnfLit::positive(var)
    }
}

/// Builds a CNF formula over `vars` variables from signed clauses.
fn formula(vars: usize, clauses: &[&[i64]]) -> CnfFormula {
    let mut f = CnfFormula::new(vars);
    for clause in clauses {
        f.add_clause(CnfClause::new(clause.iter().map(|&v| lit(v)).collect()))
            .unwrap();
    }
    f
}

/// True iff `formula` is unsatisfiable, witnessed by a checked DRAT proof.
fn is_unsat(formula: &CnfFormula) -> bool {
    match solve_with_drat_proof(formula) {
        ProofSolveOutcome::Unsat(drat) => check_drat(formula, &drat) == Ok(true),
        _ => false,
    }
}

/// Independent test-side re-check that `i` is a Craig interpolant of `(a, b)`,
/// mirroring the library's soundness contract but written separately so the test
/// does not just trust the function.
fn is_craig_interpolant(a: &CnfFormula, b: &CnfFormula, i: &BoolExpr) -> bool {
    let shared = a.variable_count();
    assert_eq!(shared, b.variable_count(), "shared variable space");

    // Vocabulary: every variable of I appears in both A and B.
    let in_a = vars_of(a);
    let in_b = vars_of(b);
    for var in i.vars() {
        if !(in_a.contains(&var) && in_b.contains(&var)) {
            return false;
        }
    }

    // A ∧ ¬I unsat.
    let mut fa = clone_over(a);
    let li = i.tseitin(&mut fa);
    fa.add_clause(CnfClause::new(vec![li.negated()])).unwrap();
    if !is_unsat(&fa) {
        return false;
    }

    // I ∧ B unsat.
    let mut fb = clone_over(b);
    let lib = i.tseitin(&mut fb);
    fb.add_clause(CnfClause::new(vec![lib])).unwrap();
    is_unsat(&fb)
}

/// Set of variables appearing in `formula`, as zero-based indices.
fn vars_of(formula: &CnfFormula) -> std::collections::BTreeSet<CnfVar> {
    let mut out = std::collections::BTreeSet::new();
    for clause in formula.clauses() {
        for l in clause.lits() {
            out.insert(l.var());
        }
    }
    out
}

/// Copies `formula` into a fresh formula over the same variable space, ready for
/// extra Tseitin variables to be appended.
fn clone_over(formula: &CnfFormula) -> CnfFormula {
    let mut out = CnfFormula::new(formula.variable_count());
    for clause in formula.clauses() {
        out.add_clause(CnfClause::new(clause.lits().to_vec()))
            .unwrap();
    }
    out
}

#[test]
fn shared_variable_direct_contradiction() {
    // A asserts x, B asserts ¬x; x is the only (shared) variable.
    let a = formula(1, &[&[1]]);
    let b = formula(1, &[&[-1]]);
    assert!(is_unsat_combined(&a, &b));
    let i = propositional_interpolant(&a, &b).expect("interpolant exists");
    assert!(is_craig_interpolant(&a, &b, &i), "got {i:?}");
}

#[test]
fn a_local_variable_must_not_appear() {
    // A: (x ∨ y) ∧ (¬y); y is A-local (vars 2 only in A). B: (¬x).
    // x is the only shared variable, so I must be over {x} only.
    let a = formula(3, &[&[1, 2], &[-2]]);
    let b = formula(3, &[&[-1]]);
    assert!(is_unsat_combined(&a, &b));
    let i = propositional_interpolant(&a, &b).expect("interpolant exists");
    // y (var index 1, dimacs 2) is A-local and must be absent.
    let y = CnfVar::new(1).unwrap();
    assert!(!i.vars().contains(&y), "A-local var leaked: {i:?}");
    assert!(is_craig_interpolant(&a, &b, &i), "got {i:?}");
}

#[test]
fn b_local_variable_present() {
    // A: (x). B: (¬x ∨ z) ∧ (¬z); z is B-local. Shared var: x.
    let a = formula(3, &[&[1]]);
    let b = formula(3, &[&[-1, 3], &[-3]]);
    assert!(is_unsat_combined(&a, &b));
    let i = propositional_interpolant(&a, &b).expect("interpolant exists");
    // z (var index 2) is B-local and must be absent from I.
    let z = CnfVar::new(2).unwrap();
    assert!(!i.vars().contains(&z), "B-local var leaked: {i:?}");
    assert!(is_craig_interpolant(&a, &b, &i), "got {i:?}");
}

#[test]
fn multi_step_resolution() {
    // A pigeonhole-flavored unsat split across A and B with several shared vars,
    // forcing a multi-step resolution proof.
    // A: (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ x3)
    // B: (¬x3 ∨ x4) ∧ (¬x3 ∨ ¬x4) ... combined with A makes ¬x3 forced, contradiction.
    let a = formula(4, &[&[1, 2], &[-1, 3], &[-2, 3]]);
    let b = formula(4, &[&[-3, 4], &[-3, -4]]);
    assert!(is_unsat_combined(&a, &b));
    let i = propositional_interpolant(&a, &b).expect("interpolant exists");
    assert!(is_craig_interpolant(&a, &b, &i), "got {i:?}");
}

#[test]
fn larger_multi_step() {
    // A: (a ∨ b), (¬a ∨ c), (¬b ∨ c)   — entails c
    // B: (¬c)                            — contradiction
    // Shared variable: c. Several resolution steps to derive c then refute.
    let a = formula(3, &[&[1, 2], &[-1, 3], &[-2, 3]]);
    let b = formula(3, &[&[-3]]);
    assert!(is_unsat_combined(&a, &b));
    let i = propositional_interpolant(&a, &b).expect("interpolant exists");
    assert!(is_craig_interpolant(&a, &b, &i), "got {i:?}");
}

#[test]
fn satisfiable_pair_declines() {
    // A: (x), B: (y); A ∧ B is satisfiable, so no interpolant.
    let a = formula(2, &[&[1]]);
    let b = formula(2, &[&[2]]);
    assert!(!is_unsat_combined(&a, &b));
    assert!(propositional_interpolant(&a, &b).is_none());
}

#[test]
fn bool_expr_simplification_laws() {
    let x = BoolExpr::Var(CnfVar::new(0).unwrap());
    assert_eq!(BoolExpr::Top.and(x.clone()), x);
    assert_eq!(x.clone().and(BoolExpr::Top), x);
    assert_eq!(BoolExpr::Bot.and(x.clone()), BoolExpr::Bot);
    assert_eq!(x.clone().and(BoolExpr::Bot), BoolExpr::Bot);
    assert_eq!(BoolExpr::Bot.or(x.clone()), x);
    assert_eq!(x.clone().or(BoolExpr::Bot), x);
    assert_eq!(BoolExpr::Top.or(x.clone()), BoolExpr::Top);
    assert_eq!(BoolExpr::Top.not(), BoolExpr::Bot);
    assert_eq!(BoolExpr::Bot.not(), BoolExpr::Top);
    assert_eq!(x.clone().not().not(), x);
}

#[test]
fn bool_expr_eval() {
    let x = BoolExpr::Var(CnfVar::new(0).unwrap());
    let y = BoolExpr::Var(CnfVar::new(1).unwrap());
    let expr = x.clone().and(y.clone().not());
    assert!(expr.eval(&[true, false]));
    assert!(!expr.eval(&[true, true]));
    assert!(!expr.eval(&[false, false]));
    let or = x.or(y);
    assert!(or.eval(&[false, true]));
    assert!(!or.eval(&[false, false]));
}

/// Combines A's then B's clauses and reports whether the conjunction is unsat.
fn is_unsat_combined(a: &CnfFormula, b: &CnfFormula) -> bool {
    let mut combined = CnfFormula::new(a.variable_count().max(b.variable_count()));
    for clause in a.clauses().iter().chain(b.clauses()) {
        combined
            .add_clause(CnfClause::new(clause.lits().to_vec()))
            .unwrap();
    }
    is_unsat(&combined)
}

/// Deterministic randomized soundness fuzz: random small CNF pairs over a shared
/// 5-variable space. Whenever the combined formula is UNSAT and the function
/// returns an interpolant, the three Craig conditions are independently
/// re-verified. The generator may decline (return `None`); it must NEVER produce
/// an `I` failing a condition. Uses a fixed xorshift LCG — no `rand`, no clock.
#[test]
fn randomized_soundness_fuzz() {
    let mut state = 0x1234_5678_9abc_def0u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let shared = 5usize;
    let shared_bound = u64::try_from(shared).unwrap();

    let mut unsat_seen = 0u32;
    let mut interpolants_verified = 0u32;

    for _ in 0..4000 {
        let a_count = 2 + usize::try_from(next() % 4).unwrap();
        let a = random_formula(&mut next, shared, shared_bound, a_count);
        let b_count = 2 + usize::try_from(next() % 4).unwrap();
        let b = random_formula(&mut next, shared, shared_bound, b_count);

        if !is_unsat_combined(&a, &b) {
            continue;
        }
        unsat_seen += 1;

        if let Some(i) = propositional_interpolant(&a, &b) {
            assert!(
                is_craig_interpolant(&a, &b, &i),
                "produced a NON-interpolant: a={:?} b={:?} i={i:?}",
                a.clauses(),
                b.clauses(),
            );
            interpolants_verified += 1;
        }
    }

    assert!(unsat_seen > 0, "fuzz produced no UNSAT pairs");
    assert!(
        interpolants_verified > 0,
        "fuzz never produced a verified interpolant (coverage zero)"
    );
}

/// Generates a random CNF formula over a shared `vars`-variable space.
fn random_formula(
    next: &mut impl FnMut() -> u64,
    vars: usize,
    vars_bound: u64,
    clause_count: usize,
) -> CnfFormula {
    let mut f = CnfFormula::new(vars);
    for _ in 0..clause_count {
        let width = 1 + usize::try_from(next() % 3).unwrap();
        let mut lits = Vec::new();
        for _ in 0..width {
            let v = i64::try_from(next() % vars_bound).unwrap() + 1;
            let signed = if next() & 1 == 0 { v } else { -v };
            lits.push(lit(signed));
        }
        f.add_clause(CnfClause::new(lits)).unwrap();
    }
    f
}
