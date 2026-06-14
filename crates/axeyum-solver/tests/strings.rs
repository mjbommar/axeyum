//! Bounded-length string theory (BV-lowered): literals, length, equality,
//! char-at, and symbolic string solving.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

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
fn suffix_and_substr_on_literals() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let hello = s.literal(&mut a, "hello").unwrap();
    let lo = s.literal(&mut a, "lo").unwrap();
    let he = s.literal(&mut a, "he").unwrap();

    let t = s.suffix_of(&mut a, &lo, &hello).unwrap();
    assert!(eval_bool(&a, t), "\"lo\" suffixof \"hello\"");
    let t = s.suffix_of(&mut a, &he, &hello).unwrap();
    assert!(!eval_bool(&a, t), "\"he\" not suffixof \"hello\"");

    // substr("hello", 1, 3) == "ell"
    let (s3, sub) = s.substr(&mut a, &hello, 1, 3).unwrap();
    let ell = s3.literal(&mut a, "ell").unwrap();
    let eq = s3.equal(&mut a, &sub, &ell).unwrap();
    assert!(eval_bool(&a, eq), "substr(\"hello\",1,3) == \"ell\"");

    // substr past the end clamps: substr("hi", 1, 3) == "i"
    let hi = s.literal(&mut a, "hi").unwrap();
    let (s3b, sub2) = s.substr(&mut a, &hi, 1, 3).unwrap();
    let i = s3b.literal(&mut a, "i").unwrap();
    let eq = s3b.equal(&mut a, &sub2, &i).unwrap();
    assert!(eval_bool(&a, eq), "substr(\"hi\",1,3) == \"i\"");
}

#[test]
fn index_of_literals() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let hello = s.literal(&mut a, "hello").unwrap();
    let l = s.literal(&mut a, "l").unwrap();
    let z = s.literal(&mut a, "z").unwrap();

    let want = |a: &TermArena, t: axeyum_ir::TermId, v: u128| {
        matches!(eval(a, t, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == v)
    };

    let (found, idx) = s.index_of(&mut a, &hello, &l, 0).unwrap();
    assert!(eval_bool(&a, found), "\"hello\" contains \"l\"");
    assert!(want(&a, idx, 2), "first \"l\" in \"hello\" is at 2");

    // from = 3 -> the second 'l' at index 3
    let (found, idx) = s.index_of(&mut a, &hello, &l, 3).unwrap();
    assert!(eval_bool(&a, found));
    assert!(want(&a, idx, 3), "first \"l\" from index 3 is at 3");

    // not found
    let (found, _idx) = s.index_of(&mut a, &hello, &z, 0).unwrap();
    assert!(!eval_bool(&a, found), "\"hello\" has no \"z\"");
}

#[test]
fn substr_at_symbolic_start() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let hello = s.literal(&mut a, "hello").unwrap();

    // constant-folded symbolic start: substr_at("hello", 1, 3) == "ell".
    let one = a.bv_const(s_len_width(8), 1).unwrap();
    let (s3, sub) = s.substr_at(&mut a, &hello, one, 3).unwrap();
    let ell = s3.literal(&mut a, "ell").unwrap();
    let eq = s3.equal(&mut a, &sub, &ell).unwrap();
    assert!(eval_bool(&a, eq), "substr_at(\"hello\",1,3) == \"ell\"");

    // symbolic: exists i: substr_at("hello", i, 2) == "lo"  -> sat (i = 3).
    let is = a.declare("i", axeyum_ir::Sort::BitVec(s_len_width(8))).unwrap();
    let i = a.var(is);
    let bound = a.bv_const(s_len_width(8), 8).unwrap();
    let wf = a.bv_ule(i, bound).unwrap();
    let (s2, sub2) = s.substr_at(&mut a, &hello, i, 2).unwrap();
    let lo = s2.literal(&mut a, "lo").unwrap();
    let goal = s2.equal(&mut a, &sub2, &lo).unwrap();
    let r = solve(&mut a, &[wf, goal], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "exists i: hello[i..i+2]=\"lo\" sat, got {r:?}");
}

#[test]
fn lexicographic_order() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let mk = |a: &mut TermArena, t: &str| s.literal(a, t).unwrap();
    let ab = mk(&mut a, "ab");
    let ac = mk(&mut a, "ac");
    let abc = mk(&mut a, "abc");
    let ab2 = mk(&mut a, "ab");
    let empty = mk(&mut a, "");

    let t = s.less(&mut a, &ab, &ac).unwrap();
    assert!(eval_bool(&a, t), "\"ab\" < \"ac\"");
    let t = s.less(&mut a, &ab, &abc).unwrap();
    assert!(eval_bool(&a, t), "\"ab\" < \"abc\" (prefix)");
    let t = s.less(&mut a, &abc, &ab).unwrap();
    assert!(!eval_bool(&a, t), "not \"abc\" < \"ab\"");
    let t = s.less(&mut a, &ab, &ab2).unwrap();
    assert!(!eval_bool(&a, t), "not \"ab\" < \"ab\"");
    let t = s.less_equal(&mut a, &ab, &ab2).unwrap();
    assert!(eval_bool(&a, t), "\"ab\" <= \"ab\"");
    let t = s.less(&mut a, &empty, &ab).unwrap();
    assert!(eval_bool(&a, t), "\"\" < \"ab\"");
}

#[test]
fn take_and_drop() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let hello = s.literal(&mut a, "hello").unwrap();

    let two = a.bv_const(s_len_width(8), 2).unwrap();
    let pre = s.take(&mut a, &hello, two).unwrap();
    let he = s.literal(&mut a, "he").unwrap();
    let pre_eq = s.equal(&mut a, &pre, &he).unwrap();
    assert!(eval_bool(&a, pre_eq), "take(\"hello\",2)==\"he\"");

    let suf = s.drop(&mut a, &hello, two).unwrap();
    let llo = s.literal(&mut a, "llo").unwrap();
    let suf_eq = s.equal(&mut a, &suf, &llo).unwrap();
    assert!(eval_bool(&a, suf_eq), "drop(\"hello\",2)==\"llo\"");

    // symbolic: exists k: take("hello", k) == "hel"  -> sat (k = 3).
    let ks = a.declare("k", axeyum_ir::Sort::BitVec(s_len_width(8))).unwrap();
    let k = a.var(ks);
    let bound = a.bv_const(s_len_width(8), 8).unwrap();
    let wf = a.bv_ule(k, bound).unwrap();
    let tk = s.take(&mut a, &hello, k).unwrap();
    let hel = s.literal(&mut a, "hel").unwrap();
    let goal = s.equal(&mut a, &tk, &hel).unwrap();
    let r = solve(&mut a, &[wf, goal], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "exists k: take(hello,k)=\"hel\" sat, got {r:?}");
}

#[test]
fn replace_same_len_first_occurrence() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let hello = s.literal(&mut a, "hello").unwrap();
    let l = s.literal(&mut a, "l").unwrap();
    let big_l = s.literal(&mut a, "L").unwrap();

    // replace first "l" with "L": "hello" -> "heLlo".
    let r = s.replace_same_len(&mut a, &hello, &l, &big_l).unwrap();
    let want = s.literal(&mut a, "heLlo").unwrap();
    let eq = s.equal(&mut a, &r, &want).unwrap();
    assert!(eval_bool(&a, eq), "replace first \"l\"->\"L\" in \"hello\" == \"heLlo\"");

    // not found -> unchanged.
    let z = s.literal(&mut a, "z").unwrap();
    let r2 = s.replace_same_len(&mut a, &hello, &z, &big_l).unwrap();
    let eq2 = s.equal(&mut a, &r2, &hello).unwrap();
    assert!(eval_bool(&a, eq2), "replace of absent needle leaves string unchanged");

    // multi-char same-length: replace "ll" with "LL" in "hello" -> "heLLo".
    let ll = s.literal(&mut a, "ll").unwrap();
    let bigll = s.literal(&mut a, "LL").unwrap();
    let r3 = s.replace_same_len(&mut a, &hello, &ll, &bigll).unwrap();
    let want3 = s.literal(&mut a, "heLLo").unwrap();
    let eq3 = s.equal(&mut a, &r3, &want3).unwrap();
    assert!(eval_bool(&a, eq3), "replace \"ll\"->\"LL\" == \"heLLo\"");
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
