//! Differential testing of the ground evaluator against the Z3 oracle.
//!
//! For each operator, build the conjunction over *all* input values at a
//! small width of `op(cx, cy) == c_evaluated`. The conjunction is ground,
//! so Z3 reports `Sat` iff its semantics agree with the evaluator on every
//! input. Any divergence (including SMT-LIB edge cases such as division by
//! zero and over-shift) makes the conjunction false and the test fail.

#![cfg(feature = "z3")]

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverBackend, SolverConfig, Z3Backend};

const W: u32 = 3;
const COUNT: u128 = 1 << W;

/// Builds `term == eval(term)` as a ground equality.
fn eval_eq(a: &mut TermArena, term: TermId) -> TermId {
    let expected = eval(a, term, &Assignment::new()).unwrap();
    let constant = match expected {
        Value::Bool(b) => a.bool_const(b),
        Value::Bv { width, value } => a.bv_const(width, value).unwrap(),
        Value::Array(_) | Value::Int(_) | Value::Real(_) => {
            unreachable!("differential terms are bit-vector/Bool")
        }
    };
    a.eq(term, constant).unwrap()
}

fn assert_z3_agrees(a: &TermArena, conjuncts: &[TermId], what: &str) {
    let result = Z3Backend::new()
        .check(a, conjuncts, &SolverConfig::default())
        .expect("backend invocation succeeds");
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "Z3 disagrees with the evaluator on {what}"
    );
}

/// Exhaustively cross-checks a binary BV-result operator.
fn diff_binary(name: &str, build: impl Fn(&mut TermArena, TermId, TermId) -> TermId) {
    let mut a = TermArena::new();
    let mut conjuncts = Vec::new();
    for x in 0..COUNT {
        for y in 0..COUNT {
            let tx = a.bv_const(W, x).unwrap();
            let ty = a.bv_const(W, y).unwrap();
            let term = build(&mut a, tx, ty);
            conjuncts.push(eval_eq(&mut a, term));
        }
    }
    assert_z3_agrees(&a, &conjuncts, name);
}

#[test]
fn differential_bitwise_and_arithmetic() {
    diff_binary("bvand", |a, x, y| a.bv_and(x, y).unwrap());
    diff_binary("bvor", |a, x, y| a.bv_or(x, y).unwrap());
    diff_binary("bvxor", |a, x, y| a.bv_xor(x, y).unwrap());
    diff_binary("bvnand", |a, x, y| a.bv_nand(x, y).unwrap());
    diff_binary("bvnor", |a, x, y| a.bv_nor(x, y).unwrap());
    diff_binary("bvxnor", |a, x, y| a.bv_xnor(x, y).unwrap());
    diff_binary("bvadd", |a, x, y| a.bv_add(x, y).unwrap());
    diff_binary("bvsub", |a, x, y| a.bv_sub(x, y).unwrap());
    diff_binary("bvmul", |a, x, y| a.bv_mul(x, y).unwrap());
}

#[test]
fn differential_division_and_remainder_including_zero() {
    diff_binary("bvudiv", |a, x, y| a.bv_udiv(x, y).unwrap());
    diff_binary("bvurem", |a, x, y| a.bv_urem(x, y).unwrap());
    diff_binary("bvsdiv", |a, x, y| a.bv_sdiv(x, y).unwrap());
    diff_binary("bvsrem", |a, x, y| a.bv_srem(x, y).unwrap());
    diff_binary("bvsmod", |a, x, y| a.bv_smod(x, y).unwrap());
}

#[test]
fn differential_shifts_including_overshift() {
    diff_binary("bvshl", |a, x, y| a.bv_shl(x, y).unwrap());
    diff_binary("bvlshr", |a, x, y| a.bv_lshr(x, y).unwrap());
    diff_binary("bvashr", |a, x, y| a.bv_ashr(x, y).unwrap());
}

#[test]
fn differential_comparisons() {
    diff_binary("bvult", |a, x, y| a.bv_ult(x, y).unwrap());
    diff_binary("bvule", |a, x, y| a.bv_ule(x, y).unwrap());
    diff_binary("bvugt", |a, x, y| a.bv_ugt(x, y).unwrap());
    diff_binary("bvuge", |a, x, y| a.bv_uge(x, y).unwrap());
    diff_binary("bvslt", |a, x, y| a.bv_slt(x, y).unwrap());
    diff_binary("bvsle", |a, x, y| a.bv_sle(x, y).unwrap());
    diff_binary("bvsgt", |a, x, y| a.bv_sgt(x, y).unwrap());
    diff_binary("bvsge", |a, x, y| a.bv_sge(x, y).unwrap());
    diff_binary("bvcomp", |a, x, y| a.bv_comp(x, y).unwrap());
    diff_binary("concat", |a, x, y| a.concat(x, y).unwrap());
}

#[test]
fn differential_unary_and_parameterized() {
    let mut a = TermArena::new();
    let mut conjuncts = Vec::new();
    for x in 0..COUNT {
        let tx = a.bv_const(W, x).unwrap();
        let mut terms = vec![a.bv_not(tx).unwrap(), a.bv_neg(tx).unwrap()];
        for by in 0..=2u32 {
            terms.push(a.zero_ext(by, tx).unwrap());
            terms.push(a.sign_ext(by, tx).unwrap());
            terms.push(a.rotate_left(by, tx).unwrap());
            terms.push(a.rotate_right(by, tx).unwrap());
        }
        for hi in 0..W {
            for lo in 0..=hi {
                terms.push(a.extract(hi, lo, tx).unwrap());
            }
        }
        for term in terms {
            conjuncts.push(eval_eq(&mut a, term));
        }
    }
    assert_z3_agrees(&a, &conjuncts, "unary/parameterized operators");
}

#[test]
fn differential_boolean_connectives() {
    let mut a = TermArena::new();
    let mut conjuncts = Vec::new();
    for p in [false, true] {
        for q in [false, true] {
            let tp = a.bool_const(p);
            let tq = a.bool_const(q);
            let terms = [
                a.and(tp, tq).unwrap(),
                a.or(tp, tq).unwrap(),
                a.xor(tp, tq).unwrap(),
                a.implies(tp, tq).unwrap(),
                a.not(tp).unwrap(),
                a.eq(tp, tq).unwrap(),
            ];
            for term in terms {
                conjuncts.push(eval_eq(&mut a, term));
            }
        }
    }
    assert_z3_agrees(&a, &conjuncts, "boolean connectives");
}
