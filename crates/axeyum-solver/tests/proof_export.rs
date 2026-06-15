//! Exportable `unsat` certificates: a `QF_BV` refutation is emitted as DIMACS +
//! DRAT and independently re-checked (ADR-0011/0012 follow-on).

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
    use axeyum_ir::Sort;
    use axeyum_solver::export_qf_abv_unsat_proof;

    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: 4,
                element: 4,
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
