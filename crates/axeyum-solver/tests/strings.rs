//! Bounded-length string theory (BV-lowered): literals, length, equality,
//! char-at, and symbolic string solving.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use axeyum_ir::{Assignment, TermArena, Value, eval};
use axeyum_solver::strings::{BoundedString, Regex};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn eval_bool(arena: &TermArena, term: axeyum_ir::TermId) -> bool {
    matches!(eval(arena, term, &Assignment::new()), Ok(Value::Bool(true)))
}

fn eval_bv(arena: &TermArena, term: axeyum_ir::TermId, v: u128) -> bool {
    matches!(eval(arena, term, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == v)
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
fn to_int_literals() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);

    // "1234" -> valid, 1234
    let lit = s.literal(&mut a, "1234").unwrap();
    let (valid, value) = s.to_int(&mut a, &lit).unwrap();
    assert!(eval_bool(&a, valid), "\"1234\" is a numeral");
    assert!(eval_bv(&a, value, 1234), "to_int(\"1234\") == 1234");

    // "0" -> valid, 0
    let z = s.literal(&mut a, "0").unwrap();
    let (vz, valz) = s.to_int(&mut a, &z).unwrap();
    assert!(eval_bool(&a, vz) && eval_bv(&a, valz, 0), "to_int(\"0\") == 0");

    // "007" -> valid, 7 (leading zeros are fine, just digits)
    let lz = s.literal(&mut a, "007").unwrap();
    let (vlz, vallz) = s.to_int(&mut a, &lz).unwrap();
    assert!(eval_bool(&a, vlz) && eval_bv(&a, vallz, 7), "to_int(\"007\") == 7");

    // "12a4" -> invalid (non-digit)
    let bad = s.literal(&mut a, "12a4").unwrap();
    let (vbad, _) = s.to_int(&mut a, &bad).unwrap();
    assert!(!eval_bool(&a, vbad), "\"12a4\" is not a numeral");

    // "" -> invalid (empty)
    let empty = s.literal(&mut a, "").unwrap();
    let (ve, _) = s.to_int(&mut a, &empty).unwrap();
    assert!(!eval_bool(&a, ve), "\"\" is not a numeral");
}

#[test]
fn symbolic_to_int_is_sat() {
    // exists x (<=4): to_int(x) valid AND value == 42 -> sat (e.g. "42").
    let mut a = TermArena::new();
    let s = BoundedString::new(4);
    let x = s.declare(&mut a, "x").unwrap();
    let wf = s.well_formed(&mut a, &x).unwrap();
    let (valid, value) = s.to_int(&mut a, &x).unwrap();
    let target = a.bv_const(64, 42).unwrap();
    let is42 = a.eq(value, target).unwrap();
    let r = solve(&mut a, &[wf, valid, is42], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "exists x with to_int(x)==42, got {r:?}");
}

#[test]
fn from_int_literals() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);

    let check = |a: &mut TermArena, n: u128, expect: &str| {
        let nv = a.bv_const(64, n).unwrap();
        let (fits, st) = s.from_int(a, nv).unwrap();
        assert!(eval_bool(a, fits), "from_int({n}) fits");
        let lit = s.literal(a, expect).unwrap();
        let eq = s.equal(a, &st, &lit).unwrap();
        assert!(eval_bool(a, eq), "from_int({n}) == {expect:?}");
    };
    check(&mut a, 0, "0");
    check(&mut a, 7, "7");
    check(&mut a, 42, "42");
    check(&mut a, 1234, "1234");
    check(&mut a, 1_000, "1000");
    check(&mut a, 90_807, "90807");

    // out of range: 9 digits does not fit max_len 8
    let big = a.bv_const(64, 123_456_789).unwrap();
    let (fits, _) = s.from_int(&mut a, big).unwrap();
    assert!(!eval_bool(&a, fits), "123456789 does not fit 8 chars");
}

#[test]
fn from_int_to_int_roundtrip_is_sat() {
    // exists n: to_int(from_int(n)) == n AND n == 555 -> sat.
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let n = a.bv_const(64, 555).unwrap();
    let (fits, st) = s.from_int(&mut a, n).unwrap();
    let (valid, value) = s.to_int(&mut a, &st).unwrap();
    let back = a.eq(value, n).unwrap();
    let r = solve(&mut a, &[fits, valid, back], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "to_int(from_int(555))==555, got {r:?}");
}

#[test]
fn replace_general_length() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);

    let check = |a: &mut TermArena, hay: &str, old: &str, new: &str, expect: &str| {
        let h = s.literal(a, hay).unwrap();
        let o = s.literal(a, old).unwrap();
        let n = s.literal(a, new).unwrap();
        let (rs, out) = s.replace(a, &h, &o, &n).unwrap();
        let exp = rs.literal(a, expect).unwrap();
        let eq = rs.equal(a, &out, &exp).unwrap();
        assert!(eval_bool(a, eq), "replace({hay:?},{old:?},{new:?}) == {expect:?}");
    };
    // equal-length
    check(&mut a, "abab", "ab", "XY", "XYab");
    // longer replacement
    check(&mut a, "hello", "l", "LL", "heLLlo");
    // shorter replacement (deletion)
    check(&mut a, "aXbXc", "X", "", "abXc");
    // first occurrence only
    check(&mut a, "abcabc", "bc", "Q", "aQabc");
    // not found -> unchanged
    check(&mut a, "xyz", "q", "123", "xyz");
    // empty old -> prepend new
    check(&mut a, "hi", "", "AB", "ABhi");
    // multi-byte needle at offset 0
    check(&mut a, "aaa", "a", "bb", "bbaa");
}

#[test]
fn symbolic_replace_is_sat() {
    // exists x (<=4): replace(x, "a", "bb") == "bbc" -> sat (x = "ac").
    let mut a = TermArena::new();
    let s = BoundedString::new(4);
    let x = s.declare(&mut a, "x").unwrap();
    let wf = s.well_formed(&mut a, &x).unwrap();
    let old = s.literal(&mut a, "a").unwrap();
    let new = s.literal(&mut a, "bb").unwrap();
    let (rs, out) = s.replace(&mut a, &x, &old, &new).unwrap();
    let target = rs.literal(&mut a, "bbc").unwrap();
    let eq = rs.equal(&mut a, &out, &target).unwrap();
    let r = solve(&mut a, &[wf, eq], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "exists x: replace(x,a,bb)=bbc, got {r:?}");
}

#[test]
fn replace_all_non_overlapping() {
    let mut a = TermArena::new();
    let s = BoundedString::new(4);

    let check = |a: &mut TermArena, hay: &str, old: &str, new: &str, expect: &str| {
        let h = s.literal(a, hay).unwrap();
        let o = s.literal(a, old).unwrap();
        let n = s.literal(a, new).unwrap();
        let (rs, out) = s.replace_all(a, &h, &o, &n).unwrap();
        let exp = rs.literal(a, expect).unwrap();
        let eq = rs.equal(a, &out, &exp).unwrap();
        assert!(eval_bool(a, eq), "replace_all({hay:?},{old:?},{new:?}) == {expect:?}");
    };
    // all occurrences
    check(&mut a, "abab", "ab", "X", "XX");
    // non-overlapping, left to right: "aaaa"/"aa" -> two matches
    check(&mut a, "aaaa", "aa", "b", "bb");
    // non-overlapping leaves a trailing unmatched byte: "aaa"/"aa" -> "ba"
    check(&mut a, "aaa", "aa", "b", "ba");
    // growing replacement, multiple matches
    check(&mut a, "aaa", "a", "bb", "bbbbbb");
    // deletion of all occurrences
    check(&mut a, "aba", "a", "", "b");
    // not found -> unchanged
    check(&mut a, "xyz", "q", "1", "xyz");
    // empty old -> unchanged
    check(&mut a, "hi", "", "AB", "hi");
}

#[test]
fn symbolic_replace_all_is_sat() {
    // exists x (<=4): replace_all(x, "a", "bb") == "bb" -> sat (x = "a" or "bb").
    let mut a = TermArena::new();
    let s = BoundedString::new(4);
    let x = s.declare(&mut a, "x").unwrap();
    let wf = s.well_formed(&mut a, &x).unwrap();
    let old = s.literal(&mut a, "a").unwrap();
    let new = s.literal(&mut a, "bb").unwrap();
    let (rs, out) = s.replace_all(&mut a, &x, &old, &new).unwrap();
    let target = rs.literal(&mut a, "bb").unwrap();
    let eq = rs.equal(&mut a, &out, &target).unwrap();
    let r = solve(&mut a, &[wf, eq], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "exists x: replace_all(x,a,bb)=bb, got {r:?}");
}

#[test]
fn regex_membership() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);

    // a(b|c)*
    let re = Regex::Concat(
        Box::new(Regex::Char(b'a')),
        Box::new(Regex::Star(Box::new(Regex::Union(
            Box::new(Regex::Char(b'b')),
            Box::new(Regex::Char(b'c')),
        )))),
    );
    let check = |a: &mut TermArena, lit: &str, expect: bool, what: &str| {
        let st = s.literal(a, lit).unwrap();
        let m = s.in_re(a, &st, &re).unwrap();
        assert_eq!(eval_bool(a, m), expect, "{what}");
    };
    check(&mut a, "a", true, "\"a\" matches a(b|c)*");
    check(&mut a, "abccb", true, "\"abccb\" matches");
    check(&mut a, "ac", true, "\"ac\" matches");
    check(&mut a, "b", false, "\"b\" does not match");
    check(&mut a, "ba", false, "\"ba\" does not match");
    check(&mut a, "", false, "\"\" does not match (needs leading a)");

    // [a-z]* matches lowercase only.
    let lower = Regex::Star(Box::new(Regex::Range(b'a', b'z')));
    let abc = s.literal(&mut a, "abc").unwrap();
    let m = s.in_re(&mut a, &abc, &lower).unwrap();
    assert!(eval_bool(&a, m), "\"abc\" matches [a-z]*");
    let mixed = s.literal(&mut a, "aBc").unwrap();
    let m = s.in_re(&mut a, &mixed, &lower).unwrap();
    assert!(!eval_bool(&a, m), "\"aBc\" does not match [a-z]*");
}

#[test]
fn regex_plus_opt_anychar() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);

    let matches = |a: &mut TermArena, re: &Regex, lit: &str| -> bool {
        let st = s.literal(a, lit).unwrap();
        let m = s.in_re(a, &st, re).unwrap();
        eval_bool(a, m)
    };

    // a+ : one or more 'a'
    let plus = Regex::Plus(Box::new(Regex::Char(b'a')));
    assert!(matches(&mut a, &plus, "a"), "a+ matches \"a\"");
    assert!(matches(&mut a, &plus, "aaa"), "a+ matches \"aaa\"");
    assert!(!matches(&mut a, &plus, ""), "a+ rejects \"\"");
    assert!(!matches(&mut a, &plus, "ab"), "a+ rejects \"ab\"");

    // a b? : optional 'b'
    let opt = Regex::Concat(
        Box::new(Regex::Char(b'a')),
        Box::new(Regex::Opt(Box::new(Regex::Char(b'b')))),
    );
    assert!(matches(&mut a, &opt, "a"), "ab? matches \"a\"");
    assert!(matches(&mut a, &opt, "ab"), "ab? matches \"ab\"");
    assert!(!matches(&mut a, &opt, "abb"), "ab? rejects \"abb\"");
    assert!(!matches(&mut a, &opt, "b"), "ab? rejects \"b\"");

    // a . c : any byte in the middle
    let dot = Regex::Concat(
        Box::new(Regex::Char(b'a')),
        Box::new(Regex::Concat(
            Box::new(Regex::AnyChar),
            Box::new(Regex::Char(b'c')),
        )),
    );
    assert!(matches(&mut a, &dot, "axc"), "a.c matches \"axc\"");
    assert!(matches(&mut a, &dot, "abc"), "a.c matches \"abc\"");
    assert!(!matches(&mut a, &dot, "ac"), "a.c rejects \"ac\"");
    assert!(!matches(&mut a, &dot, "axyc"), "a.c rejects \"axyc\"");

    // .* matches anything (incl. empty)
    let any = Regex::Star(Box::new(Regex::AnyChar));
    assert!(matches(&mut a, &any, ""), ".* matches \"\"");
    assert!(matches(&mut a, &any, "hello"), ".* matches \"hello\"");

    // a{2,4} : two to four 'a'
    let loop24 = Regex::Loop(Box::new(Regex::Char(b'a')), 2, 4);
    assert!(!matches(&mut a, &loop24, "a"), "a{{2,4}} rejects \"a\"");
    assert!(matches(&mut a, &loop24, "aa"), "a{{2,4}} matches \"aa\"");
    assert!(matches(&mut a, &loop24, "aaaa"), "a{{2,4}} matches \"aaaa\"");
    assert!(!matches(&mut a, &loop24, "aaaaa"), "a{{2,4}} rejects \"aaaaa\"");

    // a{0,2} : up to two 'a' (incl. empty)
    let loop02 = Regex::Loop(Box::new(Regex::Char(b'a')), 0, 2);
    assert!(matches(&mut a, &loop02, ""), "a{{0,2}} matches \"\"");
    assert!(matches(&mut a, &loop02, "aa"), "a{{0,2}} matches \"aa\"");
    assert!(!matches(&mut a, &loop02, "aaa"), "a{{0,2}} rejects \"aaa\"");

    // exact a{3,3}
    let loop33 = Regex::Loop(Box::new(Regex::Char(b'a')), 3, 3);
    assert!(matches(&mut a, &loop33, "aaa"), "a{{3,3}} matches \"aaa\"");
    assert!(!matches(&mut a, &loop33, "aa"), "a{{3,3}} rejects \"aa\"");

    // empty language a{3,1} matches nothing
    let empty_lang = Regex::Loop(Box::new(Regex::Char(b'a')), 3, 1);
    assert!(!matches(&mut a, &empty_lang, ""), "a{{3,1}} matches nothing");
    assert!(!matches(&mut a, &empty_lang, "aaa"), "a{{3,1}} matches nothing");
}

#[test]
fn regex_boolean_combinators() {
    let mut a = TermArena::new();
    let s = BoundedString::new(8);

    let matches = |a: &mut TermArena, re: &Regex, lit: &str| -> bool {
        let st = s.literal(a, lit).unwrap();
        let m = s.in_re(a, &st, re).unwrap();
        eval_bool(a, m)
    };

    // Inter: [a-z]* AND .{3} = exactly three lowercase letters.
    let lower_star = Regex::Star(Box::new(Regex::Range(b'a', b'z')));
    let three = Regex::Loop(Box::new(Regex::AnyChar), 3, 3);
    let inter = Regex::Inter(Box::new(lower_star), Box::new(three));
    assert!(matches(&mut a, &inter, "abc"), "inter matches \"abc\"");
    assert!(!matches(&mut a, &inter, "ab"), "inter rejects \"ab\" (len)");
    assert!(!matches(&mut a, &inter, "abcd"), "inter rejects \"abcd\" (len)");
    assert!(!matches(&mut a, &inter, "aBc"), "inter rejects \"aBc\" (uppercase)");

    // Comp: complement of the literal "no".
    let comp = Regex::Comp(Box::new(Regex::literal("no")));
    assert!(!matches(&mut a, &comp, "no"), "comp rejects \"no\"");
    assert!(matches(&mut a, &comp, "yes"), "comp matches \"yes\"");
    assert!(matches(&mut a, &comp, ""), "comp matches \"\"");

    // Diff: [a-z]+ minus the literal "x" = lowercase words except "x".
    let lower_plus = Regex::Plus(Box::new(Regex::Range(b'a', b'z')));
    let diff = Regex::Diff(Box::new(lower_plus), Box::new(Regex::literal("x")));
    assert!(matches(&mut a, &diff, "abc"), "diff matches \"abc\"");
    assert!(!matches(&mut a, &diff, "x"), "diff rejects \"x\"");
    assert!(matches(&mut a, &diff, "xy"), "diff matches \"xy\"");

    // Nested Boolean (Comp inside Inter) is allowed.
    let nested = Regex::Inter(
        Box::new(Regex::Plus(Box::new(Regex::Range(b'a', b'z')))),
        Box::new(Regex::Comp(Box::new(Regex::literal("no")))),
    );
    assert!(matches(&mut a, &nested, "yes"), "nested matches \"yes\"");
    assert!(!matches(&mut a, &nested, "no"), "nested rejects \"no\"");

    // A Boolean op nested under a repetition is rejected with an error.
    let bad = Regex::Star(Box::new(Regex::Comp(Box::new(Regex::Char(b'a')))));
    let st = s.literal(&mut a, "a").unwrap();
    assert!(s.in_re(&mut a, &st, &bad).is_err(), "nested-under-star is unsupported");
}

#[test]
fn symbolic_regex_membership_is_sat() {
    // exists x (<=8): x matches a(b|c)* AND len(x)==3 -> sat (e.g. "abc").
    let mut a = TermArena::new();
    let s = BoundedString::new(8);
    let re = Regex::Concat(
        Box::new(Regex::Char(b'a')),
        Box::new(Regex::Star(Box::new(Regex::Union(
            Box::new(Regex::Char(b'b')),
            Box::new(Regex::Char(b'c')),
        )))),
    );
    let x = s.declare(&mut a, "x").unwrap();
    let wf = s.well_formed(&mut a, &x).unwrap();
    let m = s.in_re(&mut a, &x, &re).unwrap();
    let three = a.bv_const(s_len_width(8), 3).unwrap();
    let len3 = a.eq(s.length(&x), three).unwrap();
    let r = solve(&mut a, &[wf, m, len3], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "exists x in a(b|c)* with len 3, got {r:?}");
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
