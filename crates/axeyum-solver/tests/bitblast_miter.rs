//! Certified bit-blasting by an independent-reference miter (track a, path B):
//! a DRAT-checked proof that the production bit-blasting agrees with a separately
//! coded reference on all inputs.

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{BitblastMiterOutcome, certify_bitblast_by_miter};

#[test]
fn covered_fragment_is_certified_faithful() {
    // A mix of the covered operators (bitwise and/or/xor/not, eq, ite, and pure
    // Boolean structure). The production bit-blasting must provably agree with
    // the independent reference on every input.
    let mut arena = TermArena::new();
    let xv = arena.bv_var("x", 8).unwrap();
    let yv = arena.bv_var("y", 8).unwrap();
    let zv = arena.bv_var("z", 8).unwrap();
    let t1 = arena.bv_and(xv, yv).unwrap();
    let t2 = arena.bv_or(xv, yv).unwrap();
    let t3 = arena.bv_xor(xv, yv).unwrap();
    let t4 = arena.bv_not(xv).unwrap();
    let cond = arena.eq(t1, zv).unwrap();
    let mux_term = arena.ite(cond, t2, t3).unwrap();
    let r_eq = arena.eq(mux_term, t4).unwrap();

    let pp = arena.bool_var("p").unwrap();
    let qq = arena.bool_var("q").unwrap();
    let pq = arena.and(pp, qq).unwrap();
    let not_p = arena.not(pp).unwrap();
    let bool_term = arena.or(pq, not_p).unwrap();

    let outcome = certify_bitblast_by_miter(&arena, &[mux_term, r_eq, bool_term]).unwrap();
    let BitblastMiterOutcome::Certified { dimacs, drat } = outcome else {
        panic!("expected the covered fragment to certify, got {outcome:?}");
    };
    assert!(!dimacs.is_empty() && !drat.is_empty());
}

#[test]
fn nand_nor_xnor_are_certified() {
    let mut arena = TermArena::new();
    let xv = arena.bv_var("x", 6).unwrap();
    let yv = arena.bv_var("y", 6).unwrap();
    let nand = arena.bv_nand(xv, yv).unwrap();
    let nor = arena.bv_nor(xv, yv).unwrap();
    let xnor = arena.bv_xnor(nand, nor).unwrap();
    assert!(matches!(
        certify_bitblast_by_miter(&arena, &[xnor]).unwrap(),
        BitblastMiterOutcome::Certified { .. }
    ));
}

#[test]
fn arithmetic_comparisons_and_shifts_are_certified() {
    // Add, sub, mul, neg, unsigned/signed comparisons, and logical/arithmetic
    // shifts (the bug-prone gadgets) must all provably match the production
    // bit-blasting on every input. Small width keeps the miter refutation fast.
    let mut arena = TermArena::new();
    let xv = arena.bv_var("x", 4).unwrap();
    let yv = arena.bv_var("y", 4).unwrap();
    let add = arena.bv_add(xv, yv).unwrap();
    let sub = arena.bv_sub(xv, yv).unwrap();
    let mul = arena.bv_mul(xv, yv).unwrap();
    let neg = arena.bv_neg(xv).unwrap();
    let shl = arena.bv_shl(xv, yv).unwrap();
    let lshr = arena.bv_lshr(mul, xv).unwrap();
    let ashr = arena.bv_ashr(sub, yv).unwrap();
    let ult = arena.bv_ult(add, mul).unwrap();
    let slt = arena.bv_slt(sub, neg).unwrap();
    let uge = arena.bv_uge(shl, lshr).unwrap();

    let roots = [add, sub, mul, neg, shl, lshr, ashr, ult, slt, uge];
    assert!(
        matches!(
            certify_bitblast_by_miter(&arena, &roots).unwrap(),
            BitblastMiterOutcome::Certified { .. }
        ),
        "arithmetic/comparison/shift bit-blasting should certify faithful"
    );
}

#[test]
fn uncovered_operator_is_not_certifiable() {
    // Division is outside the reference's covered fragment (for now).
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let q = arena.bv_udiv(x, y).unwrap();
    assert_eq!(
        certify_bitblast_by_miter(&arena, &[q]).unwrap(),
        BitblastMiterOutcome::NotCertifiable
    );
}

#[test]
fn non_bitblastable_is_not_certifiable() {
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let zero = arena.real_ratio(0, 1);
    let gt = arena.real_gt(r, zero).unwrap();
    assert_eq!(
        certify_bitblast_by_miter(&arena, &[gt]).unwrap(),
        BitblastMiterOutcome::NotCertifiable
    );
}
