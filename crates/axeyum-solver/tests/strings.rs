//! Bounded-length string theory (BV-lowered): literals, length, equality,
//! char-at, and symbolic string solving.

use axeyum_ir::{Assignment, TermArena, Value, eval};
use axeyum_solver::strings::BoundedString;
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn eval_bool(arena: &TermArena, term: axeyum_ir::TermId) -> bool {
    matches!(eval(arena, term, &Assignment::new()), Ok(Value::Bool(true)))
}

#[test]
fn literal_equality_and_length() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let ab = s.literal(&mut a, "ab").unwrap();
    let ab2 = s.literal(&mut a, "ab").unwrap();
    let ac = s.literal(&mut a, "ac").unwrap();
    let abc = s.literal(&mut a, "abc").unwrap();

    let eq_same = s.equal(&mut a, &ab, &ab2).unwrap();
    assert!(eval_bool(&a, eq_same), "\"ab\" == \"ab\"");
    let eq_diff = s.equal(&mut a, &ab, &ac).unwrap();
    assert!(!eval_bool(&a, eq_diff), "\"ab\" != \"ac\"");
    let eq_len = s.equal(&mut a, &ab, &abc).unwrap();
    assert!(!eval_bool(&a, eq_len), "\"ab\" != \"abc\" (length)");

    // length and char-at on a literal
    let len = s.length(&ab);
    let two = a.bv_const(s_len_width(8), 2).unwrap();
    let len_eq = a.eq(len, two).unwrap();
    assert!(eval_bool(&a, len_eq), "len(\"ab\") == 2");
    let c0 = s.char_at(&mut a, &abc, 0).unwrap();
    let a_byte = a.bv_const(8, u128::from(b'a')).unwrap();
    let c0_eq = a.eq(c0, a_byte).unwrap();
    assert!(eval_bool(&a, c0_eq), "char_at(\"abc\", 0) == 'a'");
}

// helper mirroring BoundedString::len_width for the test.
fn s_len_width(max_len: u32) -> u32 {
    32 - max_len.leading_zeros()
}

#[test]
fn symbolic_string_equals_literal_is_sat() {
    // exists x (<=8): x == "hi"  -> sat.
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let x = s.declare(&mut a, "x").unwrap();
    let wf = s.well_formed(&mut a, &x).unwrap();
    let hi = s.literal(&mut a, "hi").unwrap();
    let eq = s.equal(&mut a, &x, &hi).unwrap();

    let result = solve(&mut a, &[wf, eq], &SolverConfig::default()).unwrap();
    assert!(matches!(result, CheckResult::Sat(_)), "x == \"hi\" sat, got {result:?}");
}

#[test]
fn symbolic_length_and_char_constraint_is_sat() {
    // exists x: len(x) == 3 AND char_at(x,0) == 'h'  -> sat.
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let x = s.declare(&mut a, "x").unwrap();
    let wf = s.well_formed(&mut a, &x).unwrap();
    let three = a.bv_const(s_len_width(8), 3).unwrap();
    let len_eq = a.eq(s.length(&x), three).unwrap();
    let c0 = s.char_at(&mut a, &x, 0).unwrap();
    let h = a.bv_const(8, u128::from(b'h')).unwrap();
    let c0_eq = a.eq(c0, h).unwrap();

    let result = solve(&mut a, &[wf, len_eq, c0_eq], &SolverConfig::default()).unwrap();
    assert!(matches!(result, CheckResult::Sat(_)), "len=3 ∧ x[0]='h' sat, got {result:?}");
}

#[test]
fn contradictory_string_constraints_are_unsat() {
    // x == "ab" AND len(x) == 3  -> unsat.
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let x = s.declare(&mut a, "x").unwrap();
    let wf = s.well_formed(&mut a, &x).unwrap();
    let ab = s.literal(&mut a, "ab").unwrap();
    let eq = s.equal(&mut a, &x, &ab).unwrap();
    let three = a.bv_const(s_len_width(8), 3).unwrap();
    let len3 = a.eq(s.length(&x), three).unwrap();

    let result = solve(&mut a, &[wf, eq, len3], &SolverConfig::default()).unwrap();
    assert!(matches!(result, CheckResult::Unsat), "x=\"ab\" ∧ len(x)=3 unsat, got {result:?}");
}
