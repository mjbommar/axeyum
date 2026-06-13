//! Differential faithfulness checking of the `QF_BV` bit-blasting reduction:
//! the lowered AIG must evaluate to the same value as the original term on
//! random assignments (track a — scalable assurance for term→AIG).

use axeyum_ir::TermArena;
use axeyum_solver::{FaithfulnessOutcome, check_qf_bv_faithfulness};

#[test]
fn faithful_arithmetic_and_bitwise_terms_agree() {
    // A mix of operators (add, mul, sub, and, or, xor, comparisons) over two
    // 8-bit variables: the bit-blasting is faithful, so AIG and term agree on
    // every sample.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let prod = arena.bv_mul(x, y).unwrap();
    let diff = arena.bv_sub(sum, prod).unwrap();
    let anded = arena.bv_and(x, y).unwrap();
    let ored = arena.bv_or(diff, anded).unwrap();
    let xored = arena.bv_xor(ored, x).unwrap();
    let lt = arena.bv_ult(xored, y).unwrap();
    let eqb = arena.eq(anded, ored).unwrap();
    let goal = arena.and(lt, eqb).unwrap();

    let outcome = check_qf_bv_faithfulness(&arena, &[goal, xored, prod], 500, 0xABCD).unwrap();
    assert_eq!(outcome, FaithfulnessOutcome::Agreed { samples: 500 });
}

#[test]
fn faithful_division_and_shift_terms_agree() {
    // Division/remainder and shifts (the gadgets most prone to off-by-one /
    // carry / totality bugs) must also stay faithful, including the SMT-LIB
    // divide-by-zero totality (bvudiv x 0 = all-ones).
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 6).unwrap();
    let y = arena.bv_var("y", 6).unwrap();
    let q = arena.bv_udiv(x, y).unwrap();
    let r = arena.bv_urem(x, y).unwrap();
    let shifted = arena.bv_shl(q, r).unwrap();
    let rsh = arena.bv_lshr(shifted, x).unwrap();

    let outcome = check_qf_bv_faithfulness(&arena, &[q, r, shifted, rsh], 1000, 0x1234).unwrap();
    assert_eq!(outcome, FaithfulnessOutcome::Agreed { samples: 1000 });
}

#[test]
fn non_bitblastable_query_is_unsupported() {
    // An integer term is outside the bit-blaster's reach; faithfulness checking
    // does not apply.
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let one = arena.int_const(1);
    let sum = arena.int_add(x, one).unwrap();
    let five = arena.int_const(5);
    let eq = arena.eq(sum, five).unwrap();
    assert_eq!(
        check_qf_bv_faithfulness(&arena, &[eq], 10, 1).unwrap(),
        FaithfulnessOutcome::Unsupported
    );
}

#[test]
fn determinism_same_seed_same_result() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let first = check_qf_bv_faithfulness(&arena, &[sum], 200, 42).unwrap();
    let second = check_qf_bv_faithfulness(&arena, &[sum], 200, 42).unwrap();
    assert_eq!(first, second);
}
