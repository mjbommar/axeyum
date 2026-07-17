//! Differential validation of the e-graph EUF UNSAT prover (P1.5) against the
//! established Ackermann-elimination `QF_UFBV` path (ADR-0013).
//!
//! For every instance the e-graph prover claims UNSAT, the trusted bit-blasting
//! Ackermann path must agree it is `unsat`; and on satisfiable instances the
//! prover must not claim UNSAT while Ackermann reports `sat`. This is the
//! "verified against the eager path" check the plan calls for (P1.5 / T1.5.4).
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverConfig, check_qf_uf, check_with_function_elimination,
    prove_unsat_lazy,
};

/// Runs the Ackermann `QF_UFBV` path on `assertions`.
fn ackermann(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    let mut backend = SatBvBackend::new();
    check_with_function_elimination(&mut backend, arena, assertions, &SolverConfig::default())
        .expect("Ackermann QF_UFBV path succeeds")
}

/// Asserts the e-graph prover proves UNSAT, `check_qf_uf` decides UNSAT, and the
/// Ackermann path agrees.
fn assert_unsat_agree(arena: &mut TermArena, assertions: &[TermId]) {
    assert!(
        prove_unsat_lazy(arena, assertions),
        "e-graph EUF prover should prove UNSAT"
    );
    assert_eq!(check_qf_uf(arena, assertions), CheckResult::Unsat);
    assert_eq!(
        ackermann(arena, assertions),
        CheckResult::Unsat,
        "Ackermann path must agree the instance is UNSAT"
    );
}

/// Asserts the instance is satisfiable: the prover does not claim UNSAT,
/// `check_qf_uf` returns a model, and the Ackermann path reports `sat`.
fn assert_sat_agree(arena: &mut TermArena, assertions: &[TermId]) {
    assert!(
        !prove_unsat_lazy(arena, assertions),
        "prover must not claim a satisfiable instance UNSAT"
    );
    assert!(
        matches!(check_qf_uf(arena, assertions), CheckResult::Sat(_)),
        "check_qf_uf should return a (replay-checked) model"
    );
    assert!(
        matches!(ackermann(arena, assertions), CheckResult::Sat(_)),
        "Ackermann path must report sat"
    );
}

#[test]
fn congruence_conflict_agrees() {
    // a = b ∧ f(a) ≠ f(b).
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(8);
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let f = arena.declare_fun("f", &[sort], sort).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let fa_eq_fb = arena.eq(fa, fb).unwrap();
    let fa_ne_fb = arena.not(fa_eq_fb).unwrap();
    assert_unsat_agree(&mut arena, &[ab, fa_ne_fb]);
}

#[test]
fn transitivity_agrees() {
    // a=b ∧ b=c ∧ a≠c.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bv_var("c", 8).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let a_ne_c = arena.not(ac).unwrap();
    assert_unsat_agree(&mut arena, &[ab, bc, a_ne_c]);
}

#[test]
fn disjunctive_refutation_agrees() {
    // (a=b ∨ a=c) ∧ a≠b ∧ a≠c — needs the boolean search.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bv_var("c", 8).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let disj = arena.or(ab, ac).unwrap();
    let a_ne_b = arena.not(ab).unwrap();
    let a_ne_c = arena.not(ac).unwrap();
    assert_unsat_agree(&mut arena, &[disj, a_ne_b, a_ne_c]);
}

#[test]
fn two_argument_congruence_agrees() {
    // x=y ∧ g(x,z) ≠ g(y,z).
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(8);
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let g = arena.declare_fun("g", &[sort, sort], sort).unwrap();
    let gxz = arena.apply(g, &[x, z]).unwrap();
    let gyz = arena.apply(g, &[y, z]).unwrap();
    let xy = arena.eq(x, y).unwrap();
    let g_eq = arena.eq(gxz, gyz).unwrap();
    let g_ne = arena.not(g_eq).unwrap();
    assert_unsat_agree(&mut arena, &[xy, g_ne]);
}

#[test]
fn satisfiable_congruence_agrees() {
    // a = b ∧ f(a) = f(b): satisfiable.
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(8);
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let f = arena.declare_fun("f", &[sort], sort).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let fa_eq_fb = arena.eq(fa, fb).unwrap();
    assert_sat_agree(&mut arena, &[ab, fa_eq_fb]);
}

#[test]
fn satisfiable_disjunction_agrees() {
    // a=b ∨ a=c: satisfiable.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bv_var("c", 8).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let disj = arena.or(ab, ac).unwrap();
    assert_sat_agree(&mut arena, &[disj]);
}

/// Deterministic xorshift PRNG (no clock / `Math.random`).
fn xorshift(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

fn pick(state: &mut u64, n: usize) -> usize {
    usize::try_from(xorshift(state)).unwrap_or(0) % n
}

#[test]
fn random_qf_uf_decisions_agree_with_ackermann() {
    // Random pure equality/UF formulas (no BV arithmetic, so the e-graph path
    // always decides) must match the Ackermann bit-blast path on sat/unsat. This
    // hardens the EUF fast-path now live in check_auto dispatch.
    let mut state = 0xABCD_1234_5678_9F01u64;
    for _ in 0..120 {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(4);
        // 2..=4 leaf variables and a unary + a binary function.
        let n_vars = 2 + pick(&mut state, 3);
        let vars: Vec<TermId> = (0..n_vars)
            .map(|i| arena.bv_var(&format!("v{i}"), 4).unwrap())
            .collect();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort, sort], sort).unwrap();

        // A small pool of terms: the vars plus a few applications.
        let mut terms = vars.clone();
        for _ in 0..3 {
            let t = if xorshift(&mut state) & 1 == 0 {
                let a = terms[pick(&mut state, terms.len())];
                arena.apply(f, &[a]).unwrap()
            } else {
                let a = terms[pick(&mut state, terms.len())];
                let b = terms[pick(&mut state, terms.len())];
                arena.apply(g, &[a, b]).unwrap()
            };
            terms.push(t);
        }

        // Build a handful of (dis)equality literals, combined as a conjunction of
        // random clauses (each clause a disjunction of up to 2 literals).
        let mut assertions = Vec::new();
        let n_clauses = 2 + pick(&mut state, 4);
        for _ in 0..n_clauses {
            let width = 1 + pick(&mut state, 2);
            let mut clause: Option<TermId> = None;
            for _ in 0..width {
                let s = terms[pick(&mut state, terms.len())];
                let t = terms[pick(&mut state, terms.len())];
                let eq = arena.eq(s, t).unwrap();
                let lit = if xorshift(&mut state) & 1 == 0 {
                    eq
                } else {
                    arena.not(eq).unwrap()
                };
                clause = Some(match clause {
                    None => lit,
                    Some(acc) => arena.or(acc, lit).unwrap(),
                });
            }
            assertions.push(clause.unwrap());
        }

        let euf = check_qf_uf(&mut arena, &assertions);
        let ack = ackermann(&mut arena, &assertions);
        // Agreement: same decision, or the e-graph path abstained (`unknown` is a
        // missed decision for pure equality/UF, never a disagreement).
        let agree = matches!(
            (&euf, &ack),
            (CheckResult::Unsat, CheckResult::Unsat)
                | (CheckResult::Sat(_), CheckResult::Sat(_))
                | (CheckResult::Unknown(_), _)
        );
        assert!(agree, "EUF {euf:?} disagrees with Ackermann {ack:?}");
    }
}
