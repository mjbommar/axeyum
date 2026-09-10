//! **A recorded measurement, not a gate.** Every test here is `#[ignore]`d, so
//! nothing in this file runs in `cargo test` and nothing in it can fail a build.
//!
//! It is the probe behind roadmap item 3.3 (word-level rewrite depth), kept
//! because it answers that item's own exit criterion — "measure AIG size
//! before/after on the parity slice per candidate rule" — on a minimal instance
//! of each candidate rule, and because the answer is re-derivable in under a
//! second by anyone who doubts it:
//!
//! ```sh
//! cargo test -p axeyum-bv --release --test rewrite_rule_aig_neutrality -- --ignored --nocapture
//! ```
//!
//! Each case builds the rule's left-hand side and its right-hand side as two
//! separate terms, lowers both with the shipping eager `lower_terms`, and counts
//! **AND gates** — `Aig::node_count` also counts the constant node and one node
//! per primary input, so comparing raw node counts credits a rule with the
//! inputs it happens to drop (32 "saved nodes" for a rule that saved no gate).
//!
//! A delta of zero means the rule is AIG-neutral *for a bit-blaster*: the
//! circuit our lowering already builds for the unrewritten term is the circuit
//! the rewrite would have produced, because `Aig::and` folds constant literals
//! and hash-conses. It does not mean the rule is worthless in general — a
//! word-level solver that reasons over terms (Bitwuzla's `prop` local search,
//! for one) gets value from a rewrite our bit-blaster gets for free.
//!
//! Why this is not promoted to a live gate here: the measurement note
//! (`docs/research/03-measurements/rewrite-depth-gap-2026-09-10.md`)
//! recommends it, but wiring a new gate is outside a measurement lane's scope.
//! The neutral cases are the ones worth gating — each is an assertion that the
//! lowering's constant folding still fires, which a change to `Aig::and` or to
//! `lower_shift_op` / `lower_mul_op` would break silently today.

use axeyum_ir::{TermArena, TermId};

const W: u32 = 32;

/// AND gates only; see the module docs for why `node_count` is the wrong number.
fn and_gates(build: impl FnOnce(&mut TermArena) -> TermId) -> usize {
    let mut arena = TermArena::new();
    let root = build(&mut arena);
    let lowering = axeyum_bv::lower_terms(&arena, &[root]).expect("lower");
    lowering
        .aig()
        .node_count()
        .saturating_sub(lowering.aig().input_count())
        .saturating_sub(1)
}

fn x(a: &mut TermArena) -> TermId {
    a.bv_var("x", W).expect("x")
}
fn y(a: &mut TermArena) -> TermId {
    a.bv_var("y", W).expect("y")
}
fn z(a: &mut TermArena) -> TermId {
    a.bv_var("z", W).expect("z")
}
fn k(a: &mut TermArena, v: u128) -> TermId {
    a.bv_const(W, v).expect("const")
}

fn report(rule: &str, lhs: usize, rhs: usize) {
    println!(
        "{rule}\tlhs={lhs}\trhs={rhs}\tdelta={}",
        i64::try_from(lhs).expect("fits") - i64::try_from(rhs).expect("fits")
    );
}

/// Measured 2026-09-10: every rule below costs zero AND gates to leave
/// unrewritten. `BV_MUL_POW2`, `BV_UDIV_POW2` and `BV_SUB_SAME` are rules we
/// **do** ship — they are in this list because the lowering reaches the same
/// circuit without them, which is the control that the zero deltas below mean
/// what they say.
#[test]
#[ignore = "recorded measurement for roadmap item 3.3, not a gate"]
#[allow(
    clippy::too_many_lines,
    reason = "one rule per block; splitting them hides the list this measures"
)]
fn rules_that_cost_zero_aig_gates() {
    // BV_SHL_CONST: a constant shift amount makes every barrel-shifter mux
    // selector a constant literal, and `Aig::and` folds those to wiring.
    let lhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, 5));
        a.bv_shl(xx, c).expect("shl")
    });
    let rhs = and_gates(|a| {
        let xx = x(a);
        let lo = a.extract(W - 6, 0, xx).expect("extract");
        let zeros = a.bv_const(5, 0).expect("zeros");
        a.concat(lo, zeros).expect("concat")
    });
    report("BV_SHL_CONST", lhs, rhs);
    assert_eq!((lhs, rhs), (0, 0));

    // BV_SHR_CONST
    let lhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, 5));
        a.bv_lshr(xx, c).expect("lshr")
    });
    let rhs = and_gates(|a| {
        let xx = x(a);
        let hi = a.extract(W - 1, 5, xx).expect("extract");
        a.zero_ext(5, hi).expect("zext")
    });
    report("BV_SHR_CONST", lhs, rhs);
    assert_eq!((lhs, rhs), (0, 0));

    // BV_ASHR_CONST
    let lhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, 5));
        a.bv_ashr(xx, c).expect("ashr")
    });
    let rhs = and_gates(|a| {
        let xx = x(a);
        let hi = a.extract(W - 1, 5, xx).expect("extract");
        a.sign_ext(5, hi).expect("sext")
    });
    report("BV_ASHR_CONST", lhs, rhs);
    assert_eq!((lhs, rhs), (0, 0));

    // BV_MUL_POW2 [we ship it] -- and the lowering reaches it anyway.
    let lhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, 8));
        a.bv_mul(xx, c).expect("mul")
    });
    report("BV_MUL_POW2", lhs, 0);
    assert_eq!(lhs, 0);

    // BV_UDIV_POW2 [we ship it]
    let lhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, 8));
        a.bv_udiv(xx, c).expect("udiv")
    });
    report("BV_UDIV_POW2", lhs, 0);
    assert_eq!(lhs, 0);

    // BV_ULT_SPECIAL_CONST: `x <u 0` folds to the constant, no comparator built.
    let lhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, 0));
        a.bv_ult(xx, c).expect("ult")
    });
    report("BV_ULT_SPECIAL_CONST", lhs, 0);
    assert_eq!(lhs, 0);

    // BV_ADD_SAME: `x + x` -- every sum bit is a carry and every carry is an
    // input bit, so the adder collapses.
    let lhs = and_gates(|a| {
        let xx = x(a);
        a.bv_add(xx, xx).expect("add")
    });
    report("BV_ADD_SAME", lhs, 0);
    assert_eq!(lhs, 0);

    // BV_ADD_NOT: `x + ~x` == ones.
    let lhs = and_gates(|a| {
        let xx = x(a);
        let n = a.bv_not(xx).expect("not");
        a.bv_add(xx, n).expect("add")
    });
    report("BV_ADD_NOT", lhs, 0);
    assert_eq!(lhs, 0);

    // BV_SUB_SAME [we ship it]
    let lhs = and_gates(|a| {
        let xx = x(a);
        a.bv_sub(xx, xx).expect("sub")
    });
    report("BV_SUB_SAME", lhs, 0);
    assert_eq!(lhs, 0);

    // BV_CONCAT_CONST
    let lhs = and_gates(|a| {
        let hi = a.bv_const(16, 0x00FF).expect("c");
        let lo = a.bv_const(16, 0xAB00).expect("c");
        a.concat(hi, lo).expect("concat")
    });
    report("BV_CONCAT_CONST", lhs, 0);
    assert_eq!(lhs, 0);

    // BV_EXTRACT_CONCAT [we ship it]
    let lhs = and_gates(|a| {
        let (xx, yy) = (a.bv_var("x", 16).expect("x"), a.bv_var("y", 16).expect("y"));
        let c = a.concat(yy, xx).expect("concat");
        a.extract(15, 0, c).expect("extract")
    });
    report("BV_EXTRACT_CONCAT", lhs, 0);
    assert_eq!(lhs, 0);

    // BV_MUL_CONST_SHL / BV_MUL_CONST_ADD: a general constant multiplier is
    // already the shift-and-add form, because the gated partial products of the
    // multiplier's zero bits fold away.
    let lhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, 100));
        a.bv_mul(xx, c).expect("mul")
    });
    let rhs = and_gates(|a| {
        let xx = x(a);
        let (c2, c5, c6) = (k(a, 2), k(a, 5), k(a, 6));
        let s2 = a.bv_shl(xx, c2).expect("shl");
        let s5 = a.bv_shl(xx, c5).expect("shl");
        let s6 = a.bv_shl(xx, c6).expect("shl");
        let t = a.bv_add(s2, s5).expect("add");
        a.bv_add(t, s6).expect("add")
    });
    report("BV_MUL_CONST_SHL", lhs, rhs);
    assert_eq!(lhs, rhs);

    // BV_AND_CONCAT
    let build = |a: &mut TermArena, split: bool| {
        let hi_left = a.bv_var("p", 16).expect("p");
        let lo_left = a.bv_var("q", 16).expect("q");
        let hi_right = a.bv_var("r", 16).expect("r");
        let lo_right = a.bv_var("s", 16).expect("s");
        if split {
            let hi = a.bv_and(hi_left, hi_right).expect("and");
            let lo = a.bv_and(lo_left, lo_right).expect("and");
            a.concat(hi, lo).expect("concat")
        } else {
            let left = a.concat(hi_left, lo_left).expect("concat");
            let right = a.concat(hi_right, lo_right).expect("concat");
            a.bv_and(left, right).expect("and")
        }
    };
    let lhs = and_gates(|a| build(a, false));
    let rhs = and_gates(|a| build(a, true));
    report("BV_AND_CONCAT", lhs, rhs);
    assert_eq!(lhs, rhs);

    // EQUAL_CONST_BV_NOT
    let lhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, 0x1234));
        let n = a.bv_not(xx).expect("not");
        a.eq(n, c).expect("eq")
    });
    let rhs = and_gates(|a| {
        let (xx, c) = (x(a), k(a, u128::from(!0x1234_u32)));
        a.eq(xx, c).expect("eq")
    });
    report("EQUAL_CONST_BV_NOT", lhs, rhs);
    assert_eq!(lhs, rhs);
}

/// Measured 2026-09-10: these rules DO remove AND gates. The number beside each
/// is the removal on this one minimal instance; multiply by the corpus
/// opportunity count in the measurement note before believing anything about
/// their value.
#[test]
#[ignore = "recorded measurement for roadmap item 3.3, not a gate"]
fn rules_that_remove_aig_gates() {
    // BV_UDIV_SAME: a full restoring divider against a two-branch ite.
    let lhs = and_gates(|a| {
        let xx = x(a);
        a.bv_udiv(xx, xx).expect("udiv")
    });
    let rhs = and_gates(|a| {
        let (xx, zero, ones, one) = (x(a), k(a, 0), k(a, u128::from(u32::MAX)), k(a, 1));
        let c = a.eq(xx, zero).expect("eq");
        a.ite(c, ones, one).expect("ite")
    });
    report("BV_UDIV_SAME", lhs, rhs);
    assert!(lhs > rhs * 100, "{lhs} vs {rhs}");

    // NORM_BV_ADD_MUL: `x*y + x*z` -> `x*(y+z)` halves the multiplier count.
    let lhs = and_gates(|a| {
        let (xx, yy, zz) = (x(a), y(a), z(a));
        let p = a.bv_mul(xx, yy).expect("mul");
        let q = a.bv_mul(xx, zz).expect("mul");
        a.bv_add(p, q).expect("add")
    });
    let rhs = and_gates(|a| {
        let (xx, yy, zz) = (x(a), y(a), z(a));
        let s = a.bv_add(yy, zz).expect("add");
        a.bv_mul(xx, s).expect("mul")
    });
    report("NORM_BV_ADD_MUL", lhs, rhs);
    assert!(lhs > rhs);

    // BV_EXTRACT_ADD_MUL: only the low bits of the product are demanded.
    let lhs = and_gates(|a| {
        let (xx, yy) = (x(a), y(a));
        let s = a.bv_mul(xx, yy).expect("mul");
        a.extract(7, 0, s).expect("extract")
    });
    let rhs = and_gates(|a| {
        let (xx, yy) = (x(a), y(a));
        let lx = a.extract(7, 0, xx).expect("extract");
        let ly = a.extract(7, 0, yy).expect("extract");
        a.bv_mul(lx, ly).expect("mul")
    });
    report("BV_EXTRACT_ADD_MUL", lhs, rhs);
    assert!(lhs > rhs * 10, "{lhs} vs {rhs}");

    // EQUAL_BV_ADD: `x+a = x+b` -> `a = b` drops two adders.
    let lhs = and_gates(|a| {
        let (xx, yy, zz) = (x(a), y(a), z(a));
        let l = a.bv_add(xx, yy).expect("add");
        let r = a.bv_add(xx, zz).expect("add");
        a.eq(l, r).expect("eq")
    });
    let rhs = and_gates(|a| {
        let (yy, zz) = (y(a), z(a));
        a.eq(yy, zz).expect("eq")
    });
    report("EQUAL_BV_ADD", lhs, rhs);
    assert!(lhs > rhs);

    // ITE_THEN_ITE1
    let lhs = and_gates(|a| {
        let c = a.bool_var("c").expect("c");
        let (xx, yy, zz) = (x(a), y(a), z(a));
        let inner = a.ite(c, xx, yy).expect("ite");
        a.ite(c, inner, zz).expect("ite")
    });
    let rhs = and_gates(|a| {
        let c = a.bool_var("c").expect("c");
        let (xx, zz) = (x(a), z(a));
        a.ite(c, xx, zz).expect("ite")
    });
    report("ITE_THEN_ITE1", lhs, rhs);
    assert!(lhs > rhs);
}

/// Measured 2026-09-10: these two Bitwuzla rules would make our circuit BIGGER.
/// Both push an operator into an `ite`'s branches, duplicating it. Bitwuzla can
/// afford them because its word-level layer profits elsewhere; a bit-blaster
/// pays the duplication directly.
#[test]
#[ignore = "recorded measurement for roadmap item 3.3, not a gate"]
fn rules_that_would_grow_the_aig() {
    // BV_MUL_ITE
    let lhs = and_gates(|a| {
        let c = a.bool_var("c").expect("c");
        let (xx, yy, zz) = (x(a), y(a), z(a));
        let i = a.ite(c, xx, zz).expect("ite");
        a.bv_mul(i, yy).expect("mul")
    });
    let rhs = and_gates(|a| {
        let c = a.bool_var("c").expect("c");
        let (xx, yy, zz) = (x(a), y(a), z(a));
        let p = a.bv_mul(xx, yy).expect("mul");
        let q = a.bv_mul(zz, yy).expect("mul");
        a.ite(c, p, q).expect("ite")
    });
    report("BV_MUL_ITE", lhs, rhs);
    assert!(
        rhs > lhs,
        "expected the rewrite to be larger: {lhs} vs {rhs}"
    );

    // ITE_BV_OP
    let lhs = and_gates(|a| {
        let c = a.bool_var("c").expect("c");
        let (xx, yy, zz) = (x(a), y(a), z(a));
        let i = a.ite(c, xx, zz).expect("ite");
        a.bv_and(i, yy).expect("and")
    });
    let rhs = and_gates(|a| {
        let c = a.bool_var("c").expect("c");
        let (xx, yy, zz) = (x(a), y(a), z(a));
        let p = a.bv_and(xx, yy).expect("and");
        let q = a.bv_and(zz, yy).expect("and");
        a.ite(c, p, q).expect("ite")
    });
    report("ITE_BV_OP", lhs, rhs);
    assert!(
        rhs > lhs,
        "expected the rewrite to be larger: {lhs} vs {rhs}"
    );
}
