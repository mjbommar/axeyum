//! Regression: datatype queries must route through datatype handling on the
//! generic `solve`/`produce_evidence` path (preprocess-default-on), not escape
//! to the bit-blasting backend where a raw `DtSelect` is `Unsupported`.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, Evidence, SolverConfig, produce_evidence, solve};

/// Build `Pair { mk(a: BitVec(2), b: BitVec(2)) }` plus two `BitVec(2)` vars
/// `a`, `b`; returns `(mk_ctor, a_var, b_var)`.
fn pair_sort(
    arena: &mut TermArena,
) -> (axeyum_ir::ConstructorId, axeyum_ir::TermId, axeyum_ir::TermId) {
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[("a".into(), Sort::BitVec(2)), ("b".into(), Sort::BitVec(2))],
    );
    let a = arena.declare("a", Sort::BitVec(2)).unwrap();
    let b = arena.declare("b", Sort::BitVec(2)).unwrap();
    (mk, arena.var(a), arena.var(b))
}

/// `sel = select_0(mk(a, b)) = a`; `sel = 0 ∧ a ≠ 0` is genuinely UNSAT.
fn unsat_assertions(arena: &mut TermArena) -> Vec<axeyum_ir::TermId> {
    let (mk, a, b) = pair_sort(arena);
    let p = arena.construct(mk, &[a, b]).unwrap();
    let sel = arena.dt_select(mk, 0, p).unwrap();
    let zero = arena.bv_const(2, 0).unwrap();
    let sel_eq_zero = arena.eq(sel, zero).unwrap();
    let a_eq_zero = arena.eq(a, zero).unwrap();
    let a_ne_zero = arena.not(a_eq_zero).unwrap();
    vec![sel_eq_zero, a_ne_zero]
}

#[test]
fn datatype_unsat_via_solve_generic_path() {
    let mut arena = TermArena::new();
    let assertions = unsat_assertions(&mut arena);
    let result = solve(&mut arena, &assertions, &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "datatype select conflict must be unsat through generic solve, got {result:?}"
    );
}

#[test]
fn datatype_unsat_via_produce_evidence() {
    let mut arena = TermArena::new();
    let assertions = unsat_assertions(&mut arena);
    let evidence = produce_evidence(
        &mut arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(30)),
    )
    .expect("produce_evidence must not error on a datatype query");
    assert!(
        !matches!(evidence.evidence, Evidence::Sat(_) | Evidence::Unknown(_)),
        "datatype select conflict must be unsat through produce_evidence, got {:?}",
        evidence.evidence
    );
}

#[test]
fn datatype_sat_via_solve_generic_path() {
    // select_0(mk(a, b)) = 1 ∧ select_1(mk(a, b)) = 2  ->  a = 1 ∧ b = 2 -> sat.
    let mut arena = TermArena::new();
    let (mk, a, b) = pair_sort(&mut arena);
    let p = arena.construct(mk, &[a, b]).unwrap();
    let sel0 = arena.dt_select(mk, 0, p).unwrap();
    let sel1 = arena.dt_select(mk, 1, p).unwrap();
    let one = arena.bv_const(2, 1).unwrap();
    let two = arena.bv_const(2, 2).unwrap();
    let c0 = arena.eq(sel0, one).unwrap();
    let c1 = arena.eq(sel1, two).unwrap();
    let result = solve(&mut arena, &[c0, c1], &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "satisfiable datatype select query must be sat through generic solve, got {result:?}"
    );
}
