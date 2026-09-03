//! Tests for `decide` over ℚ.
//!
//! Every fixture value here has denominator `1` (an integer embedded in
//! `Rat`, built the same way `rat_prelude::defs`'s own `Rat.zero`/`Rat.one`
//! constants are) — a disclosed scope choice, not an oversight: it already
//! exercises this producer's own logic in full (`Eq Rat` via the `(num,
//! den)` peel, `Rat.le`/`Rat.lt` via `whnf`-unfolding to `Int.le`/`Int.lt`
//! and delegating to [`super::super::int`]), and building a genuinely
//! fractional reduced `Rat` value needs a real `gcd`-coprimality proof this
//! test module does not otherwise need.
//!
//! Four batteries, mirroring [`super::super::int::tests`]'s own structure:
//!
//! 1. **Six closed goals accepted** — two `Eq Rat`, two `Rat.le`, two
//!    `Rat.lt`, covering the `True`-by-sign-alone case (`Rat.le` between a
//!    negative and a non-negative) and a same-sign case.
//! 2. **Three goals with a free variable decline `NotClosed`.**
//! 3. **Two goals decline `Undecidable`** — a plain false comparison, and a
//!    magnitude past the fuel bound.
//! 4. **Two corrupted terms are rejected by the KERNEL.**

#![allow(clippy::many_single_char_names)]

use crate::decide::rat;
use crate::decide::{self, Decline};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{mk, req, rrefl};
use crate::{Kernel, NameId, RatPrelude, build_rat_prelude, on_a_deep_stack};

struct Fixture {
    k: Kernel,
    p: RatPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("Rat prelude must build");
        Self { k, p }
    }

    fn dev(&mut self) -> IntDev<'_> {
        IntDev::new(&mut self.k, self.p.int)
    }
}

fn name(d: &mut IntDev<'_>, s: &str) -> NameId {
    let anon = d.kernel().anon();
    d.kernel().name_str(anon, s)
}

/// Build the `Rat` value `sign * mag / 1` (`mag >= 1` when `negative`), the
/// same recipe `rat_prelude::defs`'s own `Rat.zero`/`Rat.one` constants use:
/// denominator `1`, positivity `Nat.le_refl 1`, reducedness
/// `Rat.gcd_one_right (natAbs numerator)`.
fn int_rat(d: &mut IntDev<'_>, p: &RatPrelude, mag: u32, negative: bool) -> ExprId {
    let numerator = if negative {
        assert!(mag >= 1, "a negative Rat value needs mag >= 1");
        let pred = d.num(mag - 1);
        d.neg_succ(pred)
    } else {
        let magnitude = d.num(mag);
        d.of_nat(magnitude)
    };
    let unit = d.num(1);
    let nat = p.int.nat;
    let positive = d.lemma(nat.le_refl, &[unit]);
    let nat_abs_name = p.int.nat_abs;
    let nat_abs = d.const_app(nat_abs_name, &[numerator]);
    let reduced = d.lemma(p.gcd_one_right, &[nat_abs]);
    mk(d, numerator, unit, positive, reduced)
}

/// Run `decide::rat::run` on `goal`, require `Ok`, and require the KERNEL
/// to accept a fresh `theorem <tag> : goal := <term>` declaration.
fn accept(tag: &str, goal_of: &dyn Fn(&mut IntDev<'_>, &RatPrelude) -> ExprId) {
    let mut f = Fixture::new();
    let p = f.p;
    let mut d = f.dev();
    let goal = goal_of(&mut d, &p);
    let term = rat::run(&mut d, &p, goal).unwrap_or_else(|e| panic!("{tag}: declined: {e:?}"));
    let n = name(&mut d, tag);
    d.declare_theorem(n, goal, term)
        .unwrap_or_else(|e| panic!("{tag}: kernel rejected the emitted term: {e:?}"));
}

// ---------------------------------------------------------------------------
// 1. six closed goals accepted
// ---------------------------------------------------------------------------

#[test]
fn eq_two_two() {
    on_a_deep_stack(|| {
        accept("rat_eq_two_two", &|d, p| {
            let a = int_rat(d, p, 2, false);
            let b = int_rat(d, p, 2, false);
            req(d, a, b)
        });
    });
}

#[test]
fn eq_negative_three_negative_three() {
    on_a_deep_stack(|| {
        accept("rat_eq_neg3_neg3", &|d, p| {
            let a = int_rat(d, p, 3, true);
            let b = int_rat(d, p, 3, true);
            req(d, a, b)
        });
    });
}

#[test]
fn le_two_le_five() {
    on_a_deep_stack(|| {
        accept("rat_le_two_five", &|d, p| {
            let a = int_rat(d, p, 2, false);
            let b = int_rat(d, p, 5, false);
            d.lemma(p.le, &[a, b])
        });
    });
}

#[test]
fn le_negative_always_below_nonnegative() {
    on_a_deep_stack(|| {
        accept("rat_le_neg3_zero", &|d, p| {
            let a = int_rat(d, p, 3, true);
            let b = int_rat(d, p, 0, false);
            d.lemma(p.le, &[a, b])
        });
    });
}

#[test]
fn lt_two_lt_five() {
    on_a_deep_stack(|| {
        accept("rat_lt_two_five", &|d, p| {
            let a = int_rat(d, p, 2, false);
            let b = int_rat(d, p, 5, false);
            d.lemma(p.lt, &[a, b])
        });
    });
}

#[test]
fn lt_negative_five_lt_negative_two() {
    on_a_deep_stack(|| {
        accept("rat_lt_neg5_neg2", &|d, p| {
            let a = int_rat(d, p, 5, true);
            let b = int_rat(d, p, 2, true);
            d.lemma(p.lt, &[a, b])
        });
    });
}

// ---------------------------------------------------------------------------
// 2. three goals with a free variable decline `NotClosed`
// ---------------------------------------------------------------------------

fn expect_not_closed(goal_of: &dyn Fn(&mut IntDev<'_>, &RatPrelude) -> ExprId) {
    let mut f = Fixture::new();
    let p = f.p;
    let mut d = f.dev();
    let goal = goal_of(&mut d, &p);
    let result = rat::run(&mut d, &p, goal);
    assert_eq!(result, Err(Decline::NotClosed), "got {result:?}");
}

#[test]
fn eq_with_a_free_lhs_declines_not_closed() {
    expect_not_closed(&|d, p| {
        let fv = d.fresh_fvar();
        let a = d.kernel().fvar(fv);
        let b = int_rat(d, p, 0, false);
        req(d, a, b)
    });
}

#[test]
fn le_with_a_free_rhs_declines_not_closed() {
    expect_not_closed(&|d, p| {
        let a = int_rat(d, p, 1, false);
        let fv = d.fresh_fvar();
        let b = d.kernel().fvar(fv);
        d.lemma(p.le, &[a, b])
    });
}

#[test]
fn lt_with_a_free_lhs_declines_not_closed() {
    expect_not_closed(&|d, p| {
        let fv = d.fresh_fvar();
        let a = d.kernel().fvar(fv);
        let b = int_rat(d, p, 1, false);
        d.lemma(p.lt, &[a, b])
    });
}

// ---------------------------------------------------------------------------
// 3. two goals decline `Undecidable`
// ---------------------------------------------------------------------------

#[test]
fn a_false_comparison_declines_undecidable() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let a = int_rat(&mut d, &p, 5, false);
        let b = int_rat(&mut d, &p, 2, false);
        let goal = d.lemma(p.le, &[a, b]); // 5 <= 2, false
        let result = rat::run(&mut d, &p, goal);
        assert_eq!(result, Err(Decline::Undecidable), "got {result:?}");
    });
}

#[test]
fn a_magnitude_past_the_fuel_bound_declines_undecidable_not_a_hang() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let big = decide::MAX_MAGNITUDE + 1;
        let a = int_rat(&mut d, &p, big, false);
        let b = int_rat(&mut d, &p, big, false);
        let goal = req(&mut d, a, b);
        let result = rat::run(&mut d, &p, goal);
        assert_eq!(result, Err(Decline::Undecidable), "got {result:?}");
    });
}

// ---------------------------------------------------------------------------
// 4. two corrupted terms, rejected by the KERNEL
// ---------------------------------------------------------------------------

#[test]
fn a_hand_built_irefl_for_a_false_eq_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let a = int_rat(&mut d, &p, 2, false);
        let b = int_rat(&mut d, &p, 3, false);
        let term = rrefl(&mut d, a); // proves `Eq Rat a a`, NOT `Eq Rat a b`.
        let goal = req(&mut d, a, b);
        let n = name(&mut d, "corrupted_rat_eq");
        let result = d.declare_theorem(n, goal, term);
        assert!(
            result.is_err(),
            "an irefl witness for a=2,b=3 must be rejected, not admitted"
        );
    });
}

#[test]
fn a_hand_built_witness_for_a_false_le_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let a = int_rat(&mut d, &p, 5, false);
        let b = int_rat(&mut d, &p, 2, false);
        // A witness for the (true) REVERSE comparison `2 <= 5`, spliced in
        // as if it proved `Rat.le 5 2` (false).
        let true_goal = d.lemma(p.le, &[b, a]);
        let term = rat::run(&mut d, &p, true_goal)
            .unwrap_or_else(|e| panic!("2 <= 5 must be provable: {e:?}"));
        let goal = d.lemma(p.le, &[a, b]);
        let n = name(&mut d, "corrupted_rat_le");
        let result = d.declare_theorem(n, goal, term);
        assert!(
            result.is_err(),
            "a witness for 2<=5 must be rejected against `Rat.le 5 2`, not admitted"
        );
    });
}
