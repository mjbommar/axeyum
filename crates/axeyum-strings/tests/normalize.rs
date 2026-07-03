//! Per-rule unit tests for the T-B.1 normalization invariant.

mod common;

use axeyum_ir::{Assignment, Op, TermArena, TermId, TermNode};
use axeyum_strings::{concat_components, normalize};
use common::{assert_normal_form, bv_var, cat, ch, empty, is_const, seq_var, unit};

/// `eval` the term closed and, for a length term, return the `Int`.
fn eval_int(arena: &TermArena, t: TermId) -> i128 {
    match axeyum_ir::eval(arena, t, &Assignment::new()).expect("closed eval") {
        axeyum_ir::Value::Int(n) => n,
        other => panic!("expected Int, got {other:?}"),
    }
}

// ----- rule 1: flatten -------------------------------------------------------

#[test]
fn flatten_left_nested_to_right_assoc() {
    let mut a = TermArena::new();
    let (s0, s1, s2) = (
        seq_var(&mut a, "s0"),
        seq_var(&mut a, "s1"),
        seq_var(&mut a, "s2"),
    );

    // ((s0 ++ s1) ++ s2)
    let left_nested = {
        let inner = cat(&mut a, s0, s1);
        cat(&mut a, inner, s2)
    };
    // canonical: s0 ++ (s1 ++ s2)
    let expected = {
        let inner = cat(&mut a, s1, s2);
        cat(&mut a, s0, inner)
    };

    let n = normalize(&mut a, left_nested);
    assert_eq!(n, expected, "left-nested concat must right-associate");
    assert_normal_form(&a, n);
}

#[test]
fn flatten_confluent_across_associations() {
    let mut a = TermArena::new();
    let (s0, s1, s2) = (
        seq_var(&mut a, "s0"),
        seq_var(&mut a, "s1"),
        seq_var(&mut a, "s2"),
    );

    let left = {
        let inner = cat(&mut a, s0, s1);
        cat(&mut a, inner, s2)
    };
    let right = {
        let inner = cat(&mut a, s1, s2);
        cat(&mut a, s0, inner)
    };
    // Two different parses of s0 ++ s1 ++ s2 must reach the same normal form.
    assert_eq!(normalize(&mut a, left), normalize(&mut a, right));
}

// ----- rule 2: drop ε --------------------------------------------------------

#[test]
fn drop_epsilon_components() {
    let mut a = TermArena::new();
    let s0 = seq_var(&mut a, "s0");
    let e = empty(&mut a);

    let s0e = cat(&mut a, s0, e);
    let es0 = cat(&mut a, e, s0);
    assert_eq!(normalize(&mut a, s0e), s0, "s0 ++ ε → s0");
    assert_eq!(normalize(&mut a, es0), s0, "ε ++ s0 → s0");

    // s0 ++ (ε ++ s1) → s0 ++ s1
    let s1 = seq_var(&mut a, "s1");
    let mid = {
        let inner = cat(&mut a, e, s1);
        cat(&mut a, s0, inner)
    };
    let expected = cat(&mut a, s0, s1);
    let n = normalize(&mut a, mid);
    assert_eq!(n, expected);
    assert_normal_form(&a, n);
}

#[test]
fn all_epsilon_collapses_to_empty() {
    let mut a = TermArena::new();
    let e = empty(&mut a);
    let ee = cat(&mut a, e, e);
    assert_eq!(normalize(&mut a, ee), e, "ε ++ ε → ε");
    // A bare ε normalizes to itself and has no components.
    assert_eq!(normalize(&mut a, e), e);
    assert!(concat_components(&a, e).is_empty());
}

// ----- rule 3: fuse adjacent constants ---------------------------------------

#[test]
fn fuse_makes_a_single_constant_component() {
    let mut a = TermArena::new();
    let (c0, c1) = (ch(&mut a, b'a'.into()), ch(&mut a, b'b'.into()));
    let s0 = seq_var(&mut a, "s0");
    let (u0, u1) = (unit(&mut a, c0), unit(&mut a, c1));

    // Two different parses of  "a" ++ "b" ++ s0.
    let left = {
        let ab = cat(&mut a, u0, u1);
        cat(&mut a, ab, s0)
    };
    let right = {
        let bs = cat(&mut a, u1, s0);
        cat(&mut a, u0, bs)
    };
    let nl = normalize(&mut a, left);
    let nr = normalize(&mut a, right);
    assert_eq!(nl, nr, "fusion is confluent across associations");
    assert_normal_form(&a, nl);

    // The two constant units fuse into ONE constant component; s0 is the other.
    let comps = concat_components(&a, nl);
    assert_eq!(comps.len(), 2, "expected [const-block, s0]");
    assert!(
        is_const(&a, comps[0]),
        "first component is the fused constant"
    );
    assert!(!is_const(&a, comps[1]), "second component is the variable");
    assert_eq!(comps[1], s0);
}

#[test]
fn non_adjacent_constants_do_not_fuse() {
    let mut a = TermArena::new();
    let (c0, c1) = (ch(&mut a, b'a'.into()), ch(&mut a, b'b'.into()));
    let s0 = seq_var(&mut a, "s0");
    let (u0, u1) = (unit(&mut a, c0), unit(&mut a, c1));

    // "a" ++ s0 ++ "b" — the constants are separated by s0.
    let t = {
        let sb = cat(&mut a, s0, u1);
        cat(&mut a, u0, sb)
    };
    let n = normalize(&mut a, t);
    assert_normal_form(&a, n);
    let comps = concat_components(&a, n);
    assert_eq!(comps, vec![u0, s0, u1], "no fusion across a variable");
}

// ----- rule 4: push len ------------------------------------------------------

#[test]
fn len_of_empty_is_zero() {
    let mut a = TermArena::new();
    let e = empty(&mut a);
    let len = a.seq_len(e).unwrap();
    let n = normalize(&mut a, len);
    assert_eq!(eval_int(&a, n), 0);
    assert!(matches!(a.node(n), TermNode::IntConst(0)));
}

#[test]
fn len_of_unit_is_one() {
    let mut a = TermArena::new();
    // constant element
    let cu = {
        let c = ch(&mut a, b'x'.into());
        unit(&mut a, c)
    };
    let ln_c = a.seq_len(cu).unwrap();
    let n_c = normalize(&mut a, ln_c);
    assert!(matches!(a.node(n_c), TermNode::IntConst(1)));

    // variable element — still length 1
    let vu = {
        let e = bv_var(&mut a, "e0");
        unit(&mut a, e)
    };
    let ln_v = a.seq_len(vu).unwrap();
    let n_v = normalize(&mut a, ln_v);
    assert!(matches!(a.node(n_v), TermNode::IntConst(1)));
}

#[test]
fn len_distributes_over_concat() {
    let mut a = TermArena::new();
    let (s0, s1) = (seq_var(&mut a, "s0"), seq_var(&mut a, "s1"));
    let cc = cat(&mut a, s0, s1);
    let len = a.seq_len(cc).unwrap();
    let n = normalize(&mut a, len);

    // Expected: len(s0) + len(s1).
    let ls0 = a.seq_len(s0).unwrap();
    let ls1 = a.seq_len(s1).unwrap();
    let expected = a.int_add(ls0, ls1).unwrap();
    assert_eq!(n, expected);
}

#[test]
fn len_of_opaque_seq_is_unchanged() {
    let mut a = TermArena::new();
    let s0 = seq_var(&mut a, "s0");
    let len = a.seq_len(s0).unwrap();
    let n = normalize(&mut a, len);
    assert_eq!(n, len, "len of a bare variable stays str.len");
    assert!(matches!(a.node(n), TermNode::App { op: Op::SeqLen, .. }));
}

#[test]
fn len_of_constant_block_folds() {
    let mut a = TermArena::new();
    let (c0, c1) = (ch(&mut a, b'a'.into()), ch(&mut a, b'b'.into()));
    let (u0, u1) = (unit(&mut a, c0), unit(&mut a, c1));
    let block = cat(&mut a, u0, u1); // constant "ab"
    let len = a.seq_len(block).unwrap();
    let n = normalize(&mut a, len);
    assert!(matches!(a.node(n), TermNode::IntConst(2)));
}

#[test]
fn len_under_arithmetic_is_reached() {
    let mut a = TermArena::new();
    let (s0, s1) = (seq_var(&mut a, "s0"), seq_var(&mut a, "s1"));
    // (+ (str.len (s0 ++ s1)) 1)
    let cc = cat(&mut a, s0, s1);
    let len = a.seq_len(cc).unwrap();
    let one = a.int_const(1);
    let sum = a.int_add(len, one).unwrap();

    let n = normalize(&mut a, sum);

    // Expected: (+ (+ (len s0) (len s1)) 1)
    let ls0 = a.seq_len(s0).unwrap();
    let ls1 = a.seq_len(s1).unwrap();
    let inner = a.int_add(ls0, ls1).unwrap();
    let one2 = a.int_const(1);
    let expected = a.int_add(inner, one2).unwrap();
    assert_eq!(n, expected, "len must be pushed even under arithmetic");
}

// ----- idempotence -----------------------------------------------------------

#[test]
fn idempotent_on_mixed_term() {
    let mut a = TermArena::new();
    let (c0, c1) = (ch(&mut a, b'a'.into()), ch(&mut a, b'b'.into()));
    let (u0, u1) = (unit(&mut a, c0), unit(&mut a, c1));
    let s0 = seq_var(&mut a, "s0");
    let e = empty(&mut a);

    // ((("a" ++ ε) ++ "b") ++ (s0 ++ ε))
    let t = {
        let a0 = cat(&mut a, u0, e);
        let a1 = cat(&mut a, a0, u1);
        let a2 = cat(&mut a, s0, e);
        cat(&mut a, a1, a2)
    };
    let n1 = normalize(&mut a, t);
    let n2 = normalize(&mut a, n1);
    assert_eq!(n1, n2, "normalize must be idempotent");
    assert_normal_form(&a, n1);
}
