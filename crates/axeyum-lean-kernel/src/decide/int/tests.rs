//! Tests for `decide` over ℤ.
//!
//! Four batteries, mirroring [`super::super::tests`]'s (the ℕ `decide`
//! producer's) own structure:
//!
//! 1. **Eight closed goals accepted** — covering all four `(constructor,
//!    constructor)` combinations `Int.le`/`Int.lt` case-split on
//!    (`ofNat`/`ofNat`, `ofNat`/`negSucc`, `negSucc`/`ofNat`,
//!    `negSucc`/`negSucc`), plus two `Eq Int` goals.
//! 2. **Three goals with a free variable decline `NotClosed`.**
//! 3. **Two goals decline `Undecidable`** — one a plain false comparison,
//!    one whose magnitude exceeds the fuel bound (`MAX_MAGNITUDE`, reused
//!    from the ℕ peeling this producer calls directly) and does not hang.
//! 4. **Two corrupted terms are rejected by the KERNEL** — built BY HAND
//!    from the exact shapes `decide::int::run` emits (`IntDev::irefl`, a
//!    `Nat.le`-witness chain) for a goal that is actually FALSE.

#![allow(clippy::many_single_char_names)]

use crate::decide::int;
use crate::decide::{self, Decline};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{IntPrelude, Kernel, NameId, build_int_prelude, on_a_deep_stack};

struct Fixture {
    k: Kernel,
    p: IntPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_int_prelude(&mut k).expect("Int prelude must build");
        Self { k, p }
    }

    fn dev(&mut self) -> IntDev<'_> {
        IntDev::new(&mut self.k, self.p)
    }
}

fn name(d: &mut IntDev<'_>, s: &str) -> NameId {
    let anon = d.kernel().anon();
    d.kernel().name_str(anon, s)
}

/// Run `decide::int::run` on `goal`, require `Ok`, and require the KERNEL
/// to accept a fresh `theorem <tag> : goal := <term>` declaration.
fn accept(tag: &str, goal_of: &dyn Fn(&mut IntDev<'_>) -> ExprId) {
    let mut f = Fixture::new();
    let mut d = f.dev();
    let goal = goal_of(&mut d);
    let term = int::run(&mut d, goal).unwrap_or_else(|e| panic!("{tag}: declined: {e:?}"));
    let n = name(&mut d, tag);
    d.declare_theorem(n, goal, term)
        .unwrap_or_else(|e| panic!("{tag}: kernel rejected the emitted term: {e:?}"));
}

fn ofnat(d: &mut IntDev<'_>, n: u32) -> ExprId {
    let nat = d.num(n);
    d.of_nat(nat)
}

fn negsucc(d: &mut IntDev<'_>, n: u32) -> ExprId {
    let nat = d.num(n);
    d.neg_succ(nat)
}

// ---------------------------------------------------------------------------
// 1. eight closed goals accepted
// ---------------------------------------------------------------------------

#[test]
fn eq_ofnat_three_three() {
    on_a_deep_stack(|| {
        accept("eq_ofnat_three_three", &|d| {
            let a = ofnat(d, 3);
            let b = ofnat(d, 3);
            d.ieq(a, b)
        });
    });
}

#[test]
fn eq_negsucc_two_two() {
    on_a_deep_stack(|| {
        accept("eq_negsucc_two_two", &|d| {
            let a = negsucc(d, 2);
            let b = negsucc(d, 2);
            d.ieq(a, b)
        });
    });
}

#[test]
fn le_ofnat_ofnat_two_le_five() {
    on_a_deep_stack(|| {
        accept("le_ofnat_ofnat_two_le_five", &|d| {
            let a = ofnat(d, 2);
            let b = ofnat(d, 5);
            d.ile(a, b)
        });
    });
}

#[test]
fn le_negsucc_ofnat_always_true() {
    on_a_deep_stack(|| {
        accept("le_negsucc_ofnat_always_true", &|d| {
            let a = negsucc(d, 3);
            let b = ofnat(d, 0);
            d.ile(a, b)
        });
    });
}

#[test]
fn le_negsucc_negsucc_reversed() {
    on_a_deep_stack(|| {
        // negSucc 5 <= negSucc 2, i.e. -6 <= -3 -- reduces to `Nat.le 2 5`.
        accept("le_negsucc_negsucc_reversed", &|d| {
            let a = negsucc(d, 5);
            let b = negsucc(d, 2);
            d.ile(a, b)
        });
    });
}

#[test]
fn lt_ofnat_ofnat_two_lt_five() {
    on_a_deep_stack(|| {
        accept("lt_ofnat_ofnat_two_lt_five", &|d| {
            let a = ofnat(d, 2);
            let b = ofnat(d, 5);
            d.ilt(a, b)
        });
    });
}

#[test]
fn lt_negsucc_negsucc_reversed() {
    on_a_deep_stack(|| {
        // negSucc 5 < negSucc 2, i.e. -6 < -3 -- reduces to `Nat.lt 2 5`.
        accept("lt_negsucc_negsucc_reversed", &|d| {
            let a = negsucc(d, 5);
            let b = negsucc(d, 2);
            d.ilt(a, b)
        });
    });
}

#[test]
fn lt_negsucc_ofnat_always_true() {
    on_a_deep_stack(|| {
        accept("lt_negsucc_ofnat_always_true", &|d| {
            let a = negsucc(d, 0);
            let b = ofnat(d, 0);
            d.ilt(a, b)
        });
    });
}

// ---------------------------------------------------------------------------
// 2. three goals with a free variable decline `NotClosed`
// ---------------------------------------------------------------------------

fn expect_not_closed(goal_of: &dyn Fn(&mut IntDev<'_>) -> ExprId) {
    let mut f = Fixture::new();
    let mut d = f.dev();
    let goal = goal_of(&mut d);
    let result = int::run(&mut d, goal);
    assert_eq!(result, Err(Decline::NotClosed), "got {result:?}");
}

#[test]
fn eq_with_a_free_lhs_declines_not_closed() {
    expect_not_closed(&|d| {
        let fv = d.fresh_fvar();
        let a = d.kernel().fvar(fv);
        let b = ofnat(d, 0);
        d.ieq(a, b)
    });
}

#[test]
fn le_with_a_free_lhs_declines_not_closed() {
    expect_not_closed(&|d| {
        let fv = d.fresh_fvar();
        let a = d.kernel().fvar(fv);
        let b = ofnat(d, 1);
        d.ile(a, b)
    });
}

#[test]
fn lt_with_a_free_rhs_declines_not_closed() {
    expect_not_closed(&|d| {
        let a = ofnat(d, 0);
        let fv = d.fresh_fvar();
        let b = d.kernel().fvar(fv);
        d.ilt(a, b)
    });
}

// ---------------------------------------------------------------------------
// 3. two goals decline `Undecidable`
// ---------------------------------------------------------------------------

#[test]
fn a_false_comparison_declines_undecidable() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let mut d = f.dev();
        let a = ofnat(&mut d, 5);
        let b = ofnat(&mut d, 2);
        let goal = d.ile(a, b); // 5 <= 2, false
        let result = int::run(&mut d, goal);
        assert_eq!(result, Err(Decline::Undecidable), "got {result:?}");
    });
}

#[test]
fn a_magnitude_past_the_fuel_bound_declines_undecidable_not_a_hang() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let mut d = f.dev();
        let a = ofnat(&mut d, decide::MAX_MAGNITUDE + 1);
        let b = ofnat(&mut d, decide::MAX_MAGNITUDE + 1);
        let goal = d.ieq(a, b);
        let result = int::run(&mut d, goal);
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
        let mut d = f.dev();
        let a = ofnat(&mut d, 2);
        let b = ofnat(&mut d, 3);
        let term = d.irefl(a); // proves `Eq Int a a`, NOT `Eq Int a b`.
        let goal = d.ieq(a, b);
        let n = name(&mut d, "corrupted_eq");
        let result = d.declare_theorem(n, goal, term);
        assert!(
            result.is_err(),
            "an irefl witness for a=2,b=3 must be rejected, not admitted"
        );
    });
}

#[test]
fn a_hand_built_le_witness_for_a_false_le_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let mut d = f.dev();
        let a = ofnat(&mut d, 5);
        let b = ofnat(&mut d, 2);
        let nat_prelude = d.int().nat;
        // A `Nat.le` witness for a DIFFERENT (true) pair, spliced in as if
        // it proved `Int.le a b` (5 <= 2, false).
        let term = decide::le_witness(&mut d, &nat_prelude, 2, 5);
        let goal = d.ile(a, b);
        let n = name(&mut d, "corrupted_le");
        let result = d.declare_theorem(n, goal, term);
        assert!(
            result.is_err(),
            "a le_witness(2,5) term must be rejected against `Int.le 5 2`, not admitted"
        );
    });
}
