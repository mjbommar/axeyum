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

#[test]
fn structural_operators_are_certified() {
    // concat, extract, zero/sign extension, and constant rotates must match the
    // production bit-blasting exactly (a convention mismatch would show as a
    // miter divergence, not a certificate).
    let mut arena = TermArena::new();
    let xv = arena.bv_var("x", 4).unwrap();
    let yv = arena.bv_var("y", 4).unwrap();
    let cat = arena.concat(xv, yv).unwrap(); // 8 bits
    let ext = arena.extract(5, 2, cat).unwrap(); // 4 bits from the middle
    let ze = arena.zero_ext(3, ext).unwrap(); // 7 bits
    let se = arena.sign_ext(2, xv).unwrap(); // 6 bits
    let rl = arena.rotate_left(1, xv).unwrap();
    let rr = arena.rotate_right(3, yv).unwrap();

    let roots = [cat, ext, ze, se, rl, rr];
    assert!(
        matches!(
            certify_bitblast_by_miter(&arena, &roots).unwrap(),
            BitblastMiterOutcome::Certified { .. }
        ),
        "structural bit-blasting (concat/extract/extend/rotate) should certify"
    );
}

#[test]
fn unsigned_division_and_remainder_are_certified() {
    // The restoring divider (and its divide-by-zero totality) must match the
    // production bit-blasting on every input — the most bug-prone gadget.
    let mut arena = TermArena::new();
    let xv = arena.bv_var("x", 4).unwrap();
    let yv = arena.bv_var("y", 4).unwrap();
    let q = arena.bv_udiv(xv, yv).unwrap();
    let r = arena.bv_urem(xv, yv).unwrap();
    assert!(
        matches!(
            certify_bitblast_by_miter(&arena, &[q, r]).unwrap(),
            BitblastMiterOutcome::Certified { .. }
        ),
        "unsigned division/remainder bit-blasting should certify faithful"
    );
}

#[test]
fn signed_division_is_still_uncovered() {
    // Signed division/remainder/modulo are not yet in the reference fragment.
    let mut arena = TermArena::new();
    let xv = arena.bv_var("x", 8).unwrap();
    let yv = arena.bv_var("y", 8).unwrap();
    let s = arena.bv_sdiv(xv, yv).unwrap();
    assert_eq!(
        certify_bitblast_by_miter(&arena, &[s]).unwrap(),
        BitblastMiterOutcome::NotCertifiable
    );
}
