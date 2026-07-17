//! Exportable `unsat` certificates: a `QF_BV` refutation is emitted as DIMACS +
//! DRAT and independently re-checked (ADR-0011/0012 follow-on).
#![cfg(feature = "full")]

use axeyum_cnf::{check_drat, parse_dimacs, parse_drat};
use axeyum_ir::TermArena;
use axeyum_solver::{UnsatProofOutcome, export_qf_bv_unsat_proof};

#[test]
fn unsatisfiable_query_exports_a_recheckable_drat_certificate() {
    // x & 1 == 1  AND  x & 1 == 0  is unsatisfiable.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(masked, zero).unwrap();

    let outcome = export_qf_bv_unsat_proof(&arena, &[is_one, is_zero]).unwrap();
    let UnsatProofOutcome::Proved(proof) = outcome else {
        panic!("expected an unsat certificate, got {outcome:?}");
    };

    // The exported artifact re-parses and the DRAT refutes the DIMACS CNF —
    // verified independently of the solver that produced it.
    let formula = parse_dimacs(&proof.dimacs).expect("exported DIMACS re-parses");
    let steps = parse_drat(&proof.drat).expect("exported DRAT re-parses");
    assert!(
        check_drat(&formula, &steps).expect("re-check runs"),
        "exported DRAT must refute the exported CNF"
    );
    // A real proof ends by deriving the empty clause.
    assert!(!proof.drat.is_empty());
}

#[test]
fn satisfiable_query_has_no_unsat_proof() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let eq = arena.eq(x, one).unwrap();
    assert_eq!(
        export_qf_bv_unsat_proof(&arena, &[eq]).unwrap(),
        UnsatProofOutcome::Satisfiable
    );
}

#[test]
fn non_bitblastable_query_is_unsupported() {
    // An integer query is outside the bit-blasted fragment.
    use axeyum_ir::Sort;
    let mut arena = TermArena::new();
    let n_sym = arena.declare("n", Sort::Int).unwrap();
    let n = arena.var(n_sym);
    let one = arena.int_const(1);
    let eq = arena.eq(n, one).unwrap();
    assert!(export_qf_bv_unsat_proof(&arena, &[eq]).is_err());
}

#[test]
fn qf_abv_unsat_exports_a_recheckable_certificate() {
    // Read-over-write: with i == j, select(store(mem,i,v),j) == v, so demanding
    // it differ is unsat. The array-eliminated CNF's DRAT refutation is exported
    // and independently re-checked — a checkable certificate for the array
    // fragment (modulo the trusted, replay-validatable elimination).
    use axeyum_ir::{ArraySortKey, Sort};
    use axeyum_solver::export_qf_abv_unsat_proof;

    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: ArraySortKey::BitVec(4),
                element: ArraySortKey::BitVec(4),
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let is = arena.declare("i", Sort::BitVec(4)).unwrap();
    let js = arena.declare("j", Sort::BitVec(4)).unwrap();
    let vs = arena.declare("v", Sort::BitVec(4)).unwrap();
    let (i, j, v) = (arena.var(is), arena.var(js), arena.var(vs));
    let stored = arena.store(mem_v, i, v).unwrap();
    let loaded = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let load_ne_v = {
        let eq = arena.eq(loaded, v).unwrap();
        arena.not(eq).unwrap()
    };

    let outcome = export_qf_abv_unsat_proof(&mut arena, &[i_eq_j, load_ne_v]).unwrap();
    let UnsatProofOutcome::Proved(proof) = outcome else {
        panic!("expected an unsat certificate, got {outcome:?}");
    };
    let formula = parse_dimacs(&proof.dimacs).expect("exported DIMACS re-parses");
    let steps = parse_drat(&proof.drat).expect("exported DRAT re-parses");
    assert!(
        check_drat(&formula, &steps).expect("re-check runs"),
        "exported DRAT must refute the array-eliminated CNF"
    );
}

#[test]
fn qf_uf_unsat_exports_a_recheckable_certificate() {
    // Congruence: x == y but f(x) != f(y) is unsat. The Ackermann-reduced CNF's
    // DRAT refutation is exported and independently re-checked — a checkable
    // certificate for the uninterpreted-function fragment.
    use axeyum_ir::Sort;
    use axeyum_solver::export_qf_uf_unsat_proof;

    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
        .unwrap();
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let x_eq_y = arena.eq(x, y).unwrap();
    let fx_ne_fy = {
        let eq = arena.eq(fx, fy).unwrap();
        arena.not(eq).unwrap()
    };

    let outcome = export_qf_uf_unsat_proof(&mut arena, &[x_eq_y, fx_ne_fy]).unwrap();
    let UnsatProofOutcome::Proved(proof) = outcome else {
        panic!("expected an unsat certificate, got {outcome:?}");
    };
    let formula = parse_dimacs(&proof.dimacs).expect("exported DIMACS re-parses");
    let steps = parse_drat(&proof.drat).expect("exported DRAT re-parses");
    assert!(
        check_drat(&formula, &steps).expect("re-check runs"),
        "exported DRAT must refute the Ackermann-reduced CNF"
    );
}

#[test]
fn qf_aufbv_unsat_exports_a_recheckable_certificate() {
    // Arrays + UF together: with a == b, select(store(mem,a,x),b) == x, so
    // f(select(...)) == f(x) by congruence — demanding they differ is unsat.
    // Exercises both array elimination and Ackermann reduction in one proof.
    use axeyum_ir::{ArraySortKey, Sort};
    use axeyum_solver::export_qf_aufbv_unsat_proof;

    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: ArraySortKey::BitVec(4),
                element: ArraySortKey::BitVec(4),
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let f = arena
        .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
        .unwrap();
    let a = arena.bv_var("a", 4).unwrap();
    let b = arena.bv_var("b", 4).unwrap();
    let x = arena.bv_var("x", 4).unwrap();
    let stored = arena.store(mem_v, a, x).unwrap();
    let loaded = arena.select(stored, b).unwrap();
    let f_loaded = arena.apply(f, &[loaded]).unwrap();
    let f_x = arena.apply(f, &[x]).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let f_ne = {
        let eq = arena.eq(f_loaded, f_x).unwrap();
        arena.not(eq).unwrap()
    };

    let outcome = export_qf_aufbv_unsat_proof(&mut arena, &[a_eq_b, f_ne]).unwrap();
    let UnsatProofOutcome::Proved(proof) = outcome else {
        panic!("expected an unsat certificate, got {outcome:?}");
    };
    let formula = parse_dimacs(&proof.dimacs).expect("exported DIMACS re-parses");
    let steps = parse_drat(&proof.drat).expect("exported DRAT re-parses");
    assert!(
        check_drat(&formula, &steps).expect("re-check runs"),
        "exported DRAT must refute the array+function-reduced CNF"
    );
}

#[test]
fn bounded_qf_lia_unsat_exports_a_recheckable_certificate() {
    // x + 2 == 5 (x == 3) and x == 0 is unsat. Bit-blasted at width 8, the
    // resulting QF_BV CNF's DRAT refutation is exported and re-checked.
    use axeyum_ir::Sort;
    use axeyum_solver::export_qf_lia_unsat_proof;

    let mut arena = TermArena::new();
    let xs = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(xs);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let zero = arena.int_const(0);
    let sum = arena.int_add(x, two).unwrap();
    let sum_eq_5 = arena.eq(sum, five).unwrap();
    let x_eq_0 = arena.eq(x, zero).unwrap();

    let outcome = export_qf_lia_unsat_proof(&mut arena, &[sum_eq_5, x_eq_0], 8).unwrap();
    let UnsatProofOutcome::Proved(proof) = outcome else {
        panic!("expected an unsat certificate, got {outcome:?}");
    };
    let formula = parse_dimacs(&proof.dimacs).expect("exported DIMACS re-parses");
    let steps = parse_drat(&proof.drat).expect("exported DRAT re-parses");
    assert!(
        check_drat(&formula, &steps).expect("re-check runs"),
        "exported DRAT must refute the integer-blasted CNF"
    );
}

#[test]
fn bounded_qf_nia_with_overflow_guard_does_not_export_a_false_proof() {
    // SOUNDNESS REGRESSION (locks the fail-closed guard): x*x == 16 ∧ 0 ≤ x ≤ 100
    // is satisfiable over the integers (x = 4). Bit-blasted at width 4 (signed
    // range [-8, 7]), the genuine witness x = 4 has x*x = 16, which OVERFLOWS the
    // 4-bit product — so the no-overflow side-constraint prunes it and the guarded
    // QF_BV query can be UNSAT at this width. A DRAT refutation of that *restricted*
    // query must NEVER be exported as a proof that the ORIGINAL is unsat (it is
    // not). `export_qf_lia_unsat_proof` must decline to `Inconclusive`.
    use axeyum_ir::Sort;
    use axeyum_solver::export_qf_lia_unsat_proof;

    let mut arena = TermArena::new();
    let xs = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(xs);
    let xx = arena.int_mul(x, x).unwrap();
    let sixteen = arena.int_const(16);
    let xx_eq_16 = arena.eq(xx, sixteen).unwrap();
    let zero = arena.int_const(0);
    let hundred = arena.int_const(100);
    let lo = arena.int_le(zero, x).unwrap();
    let hi = arena.int_le(x, hundred).unwrap();

    let outcome = export_qf_lia_unsat_proof(&mut arena, &[xx_eq_16, lo, hi], 4).unwrap();
    assert!(
        matches!(outcome, UnsatProofOutcome::Inconclusive),
        "a guarded (overflow-restricted) blast must NOT export an unsat proof of \
         the original satisfiable formula; expected Inconclusive, got {outcome:?}"
    );
}

#[test]
fn datatype_unsat_exports_a_recheckable_certificate() {
    // A ground constructor mismatch folds to false: is_green(red) is unsat.
    // simplify_datatypes reduces it to a Boolean contradiction, exported and
    // re-checked through the QF_BV proof path.
    use axeyum_solver::export_datatype_unsat_proof;

    let mut arena = TermArena::new();
    let color = arena.declare_datatype("color");
    let red = arena.add_constructor(color, "red", &[]);
    let green = arena.add_constructor(color, "green", &[]);
    let red_t = arena.construct(red, &[]).unwrap();
    let is_green = arena.dt_test(green, red_t).unwrap();

    let outcome = export_datatype_unsat_proof(&mut arena, &[is_green]).unwrap();
    let UnsatProofOutcome::Proved(proof) = outcome else {
        panic!("expected an unsat certificate, got {outcome:?}");
    };
    let formula = parse_dimacs(&proof.dimacs).expect("exported DIMACS re-parses");
    let steps = parse_drat(&proof.drat).expect("exported DRAT re-parses");
    assert!(
        check_drat(&formula, &steps).expect("re-check runs"),
        "exported DRAT must refute the datatype-simplified CNF"
    );
}
