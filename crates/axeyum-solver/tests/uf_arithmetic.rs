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

/// Congruence over an arithmetic argument term: `f(x+0) ≠ f(x)` is UNSAT because
/// `x+0 = x`, so `f(x+0) = f(x)`. The eager Ackermann constraint `(x+0 = x) ⇒
/// (f(x+0) = f(x))` over the arithmetic solver decides it (no unbound-intermediate
/// issue the lazy refinement would have).
#[test]
fn uflia_congruence_over_arith_argument_unsat() {
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let zero = a.int_const(0);
    let xp0 = a.int_add(x, zero).unwrap();
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let f1 = a.apply(f, &[xp0]).unwrap();
    let f2 = a.apply(f, &[x]).unwrap();
    let ne = {
        let e = a.eq(f1, f2).unwrap();
        a.not(e).unwrap()
    };
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[ne], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// The UF result feeding arithmetic: `f(a) + 1 = f(b) ∧ a = b` is UNSAT — `a = b`
/// forces `f(a) = f(b)` by congruence, so `f(a) + 1 = f(a)`, i.e. `1 = 0`.
#[test]
fn uflia_result_in_arithmetic_unsat() {
    let mut a = TermArena::new();
    let p = decl_int(&mut a, "p");
    let q = decl_int(&mut a, "q");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fp = a.apply(f, &[p]).unwrap();
    let fq = a.apply(f, &[q]).unwrap();
    let one = a.int_const(1);
    let fp1 = a.int_add(fp, one).unwrap();
    let eq1 = a.eq(fp1, fq).unwrap(); // f(p) + 1 = f(q)
    let eq2 = a.eq(p, q).unwrap(); // p = q
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[eq1, eq2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// Nested UF over Int: `f(g(a)) ≠ f(g(b)) ∧ a = b` is UNSAT — `a=b` ⇒ `g(a)=g(b)`
/// ⇒ `f(g(a))=f(g(b))` (two rounds of functional-consistency refinement).
#[test]
fn uflia_nested_congruence_unsat() {
    let mut a = TermArena::new();
    let s = decl_int(&mut a, "s");
    let t = decl_int(&mut a, "t");
    let g = a.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let gs = a.apply(g, &[s]).unwrap();
    let gt = a.apply(g, &[t]).unwrap();
    let fgs = a.apply(f, &[gs]).unwrap();
    let fgt = a.apply(f, &[gt]).unwrap();
    let ne = {
        let e = a.eq(fgs, fgt).unwrap();
        a.not(e).unwrap()
    };
    let eq = a.eq(s, t).unwrap();
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[ne, eq], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// Regression: `solve` on a quantified UF+LIA query must not crash. `∀x:Int. f(x)=0`
/// instantiated at `f(5)` contradicts `f(5)≠0`, and the combined path used to panic
/// (`scalar_code` on an Int in function-model projection) — now it decides UNSAT.
#[test]
fn quantified_uf_lia_solve_decides_without_crashing() {
    use axeyum_solver::solve;
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let xsym = a.declare("x", Sort::Int).unwrap();
    let xv = a.var(xsym);
    let fx = a.apply(f, &[xv]).unwrap();
    let zero = a.int_const(0);
    let body = a.eq(fx, zero).unwrap();
    let forall = a.forall(xsym, body).unwrap();
    let five = a.int_const(5);
    let f5 = a.apply(f, &[five]).unwrap();
    let ne = {
        let e = a.eq(f5, zero).unwrap();
        a.not(e).unwrap()
    };
    let r = solve(&mut a, &[forall, ne], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "instantiate x=5: f(5)=0 ∧ f(5)≠0; got {r:?}"
    );
}

/// Value conflict via congruence: `f(a) = 1 ∧ f(b) = 2 ∧ a = b` is UNSAT —
/// `a = b` ⇒ `f(a) = f(b)`, so `1 = 2`.
#[test]
fn uflia_value_conflict_via_congruence_unsat() {
    let mut a = TermArena::new();
    let u = decl_int(&mut a, "u");
    let v = decl_int(&mut a, "v");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fu = a.apply(f, &[u]).unwrap();
    let fv = a.apply(f, &[v]).unwrap();
    let one = a.int_const(1);
    let two = a.int_const(2);
    let e1 = a.eq(fu, one).unwrap();
    let e2 = a.eq(fv, two).unwrap();
    let e3 = a.eq(u, v).unwrap();
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[e1, e2, e3], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}
