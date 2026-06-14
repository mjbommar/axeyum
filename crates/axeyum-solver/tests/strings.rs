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
fn concat_of_literals_equals_joined_literal() {
    // "ab" ++ "cd" == "abcd".
    let mut a = TermArena::new();
    let s4 = BoundedString::new(4);
    let ab = s4.literal(&mut a, "ab").unwrap();
    let cd = s4.literal(&mut a, "cd").unwrap();
    let (s8, joined) = s4.concat(&mut a, &ab, s4, &cd).unwrap();
    let abcd = s8.literal(&mut a, "abcd").unwrap();
    let eq = s8.equal(&mut a, &joined, &abcd).unwrap();
    assert!(eval_bool(&a, eq), "\"ab\"++\"cd\" == \"abcd\"");

    // length is 4
    let four = a.bv_const(s_len_width(8), 4).unwrap();
    let len_eq = a.eq(s8.length(&joined), four).unwrap();
    assert!(eval_bool(&a, len_eq), "len(\"ab\"++\"cd\") == 4");
}

#[test]
fn concat_with_empty_and_symbolic() {
    // "" ++ "cd" == "cd" (empty-length operand) — exercises len_x = 0 shift.
    let mut a = TermArena::new();
    let s4 = BoundedString::new(4);
    let empty = s4.literal(&mut a, "").unwrap();
    let cd = s4.literal(&mut a, "cd").unwrap();
    let (s8, joined) = s4.concat(&mut a, &empty, s4, &cd).unwrap();
    let cd8 = s8.literal(&mut a, "cd").unwrap();
    let eq = s8.equal(&mut a, &joined, &cd8).unwrap();
    assert!(eval_bool(&a, eq), "\"\"++\"cd\" == \"cd\"");

    // symbolic: exists x (<=4): x ++ "!" == "hi!"  -> sat with x = "hi".
    let x = s4.declare(&mut a, "x").unwrap();
    let wf = s4.well_formed(&mut a, &x).unwrap();
    let bang = s4.literal(&mut a, "!").unwrap();
    let (s8b, joined2) = s4.concat(&mut a, &x, s4, &bang).unwrap();
    let hi_bang = s8b.literal(&mut a, "hi!").unwrap();
    let goal = s8b.equal(&mut a, &joined2, &hi_bang).unwrap();
    let result = solve(&mut a, &[wf, goal], &SolverConfig::default()).unwrap();
    assert!(matches!(result, CheckResult::Sat(_)), "x ++ \"!\" = \"hi!\" sat, got {result:?}");
}

#[test]
fn prefix_and_contains_on_literals() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let abc = s.literal(&mut a, "abc").unwrap();
    let ab = s.literal(&mut a, "ab").unwrap();
    let ac = s.literal(&mut a, "ac").unwrap();
    let bc = s.literal(&mut a, "bc").unwrap();
    let xy = s.literal(&mut a, "xy").unwrap();
    let empty = s.literal(&mut a, "").unwrap();

    let t = s.prefix_of(&mut a, &ab, &abc).unwrap();
    assert!(eval_bool(&a, t), "\"ab\" prefixof \"abc\"");
    let t = s.prefix_of(&mut a, &ac, &abc).unwrap();
    assert!(!eval_bool(&a, t), "\"ac\" not prefixof \"abc\"");
    let t = s.prefix_of(&mut a, &empty, &abc).unwrap();
    assert!(eval_bool(&a, t), "\"\" prefixof \"abc\"");

    let t = s.contains(&mut a, &abc, &bc).unwrap();
    assert!(eval_bool(&a, t), "\"abc\" contains \"bc\"");
    let t = s.contains(&mut a, &abc, &ab).unwrap();
    assert!(eval_bool(&a, t), "\"abc\" contains \"ab\"");
    let t = s.contains(&mut a, &abc, &xy).unwrap();
    assert!(!eval_bool(&a, t), "\"abc\" does not contain \"xy\"");
    let t = s.contains(&mut a, &abc, &empty).unwrap();
    assert!(eval_bool(&a, t), "\"abc\" contains \"\"");
}

#[test]
fn symbolic_contains_is_sat() {
    // exists x (<=8): x contains "lo" AND len(x)==5  -> sat (e.g. "hello").
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let x = s.declare(&mut a, "x").unwrap();
    let wf = s.well_formed(&mut a, &x).unwrap();
    let lo = s.literal(&mut a, "lo").unwrap();
    let has = s.contains(&mut a, &x, &lo).unwrap();
    let five = a.bv_const(s_len_width(8), 5).unwrap();
    let len5 = a.eq(s.length(&x), five).unwrap();
    let r = solve(&mut a, &[wf, has, len5], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "x contains \"lo\" ∧ len 5 sat, got {r:?}");
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
