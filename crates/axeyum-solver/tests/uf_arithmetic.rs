//! EUF + linear-arithmetic combination (`QF_UFLIA` / `QF_UFLRA`) via the
//! functional-consistency CEGAR over the arithmetic dispatcher
//! ([`axeyum_solver::check_with_uf_arithmetic`], P1.6). The arithmetic solver and the
//! congruence closure exchange equalities through the shared abstraction: arithmetic
//! forces argument equalities; a functional-consistency lemma then forces the
//! results equal.
#![allow(clippy::many_single_char_names)]

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, check_with_uf_arithmetic};

/// `f(a) ≠ f(b) ∧ a ≤ b ∧ b ≤ a` is UNSAT: LIA forces `a = b`, congruence forces
/// `f(a) = f(b)`, contradicting the disequality. The textbook Nelson–Oppen case.
#[test]
fn uflia_squeeze_forces_congruence_unsat() {
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let y = decl_int(&mut a, "y");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    let fy = a.apply(f, &[y]).unwrap();
    let ne = {
        let e = a.eq(fx, fy).unwrap();
        a.not(e).unwrap()
    };
    let le1 = a.int_le(x, y).unwrap();
    let le2 = a.int_le(y, x).unwrap();
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[ne, le1, le2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// `f(a) ≠ f(b) ∧ a ≤ b` is satisfiable, so it is **never refuted**. (The witnessing
/// model for an arithmetic-sorted UF is not yet built — `project_model` keys function
/// tables by scalar codes — so this returns a sound `Unknown` rather than `Sat`; the
/// point is it is not a wrong `Unsat`.)
#[test]
fn uflia_loose_bound_is_not_refuted() {
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let y = decl_int(&mut a, "y");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    let fy = a.apply(f, &[y]).unwrap();
    let ne = {
        let e = a.eq(fx, fy).unwrap();
        a.not(e).unwrap()
    };
    let le1 = a.int_le(x, y).unwrap();
    assert!(!matches!(
        check_with_uf_arithmetic(&mut a, &[ne, le1], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// `QF_UFLRA`: the same squeeze over the reals (`g(p) ≠ g(q) ∧ p ≤ q ∧ q ≤ p`).
#[test]
fn uflra_squeeze_forces_congruence_unsat() {
    let mut a = TermArena::new();
    let p = a.real_var("p").unwrap();
    let q = a.real_var("q").unwrap();
    let g = a.declare_fun("g", &[Sort::Real], Sort::Real).unwrap();
    let gp = a.apply(g, &[p]).unwrap();
    let gq = a.apply(g, &[q]).unwrap();
    let ne = {
        let e = a.eq(gp, gq).unwrap();
        a.not(e).unwrap()
    };
    let le1 = a.real_le(p, q).unwrap();
    let le2 = a.real_le(q, p).unwrap();
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[ne, le1, le2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

fn decl_int(a: &mut TermArena, name: &str) -> axeyum_ir::TermId {
    let s = a.declare(name, Sort::Int).unwrap();
    a.var(s)
}

/// The dispatcher (`solve`) routes `QF_UFLIA` automatically: the squeeze refutation
/// is decided without naming the combination procedure explicitly.
#[test]
fn solve_dispatches_uflia_combination() {
    use axeyum_solver::solve;
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let y = decl_int(&mut a, "y");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    let fy = a.apply(f, &[y]).unwrap();
    let ne = {
        let e = a.eq(fx, fy).unwrap();
        a.not(e).unwrap()
    };
    let le1 = a.int_le(x, y).unwrap();
    let le2 = a.int_le(y, x).unwrap();
    assert!(matches!(
        solve(&mut a, &[ne, le1, le2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}
