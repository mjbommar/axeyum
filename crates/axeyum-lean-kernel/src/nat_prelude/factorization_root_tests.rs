//! Concrete-instance tests for `nat_prelude::factorization_root`.
//!
//! A separate file (rather than an addition to the dense
//! `nat_prelude_tests.rs`) for the merge hazard `find_greatest_tests.rs`,
//! `avg_pair_tests.rs` and `abundant_deficient_tests.rs` all record: two lanes
//! editing that one file at once have repeatedly produced a conflict git cuts
//! mid-item.
//!
//! **The kernel cannot tell a `Definition` is wrong.** `Nat → Nat → Nat` is
//! that type whatever the body computes, so `add_declaration` accepts a
//! reversed scan, a `bool_select_nat` with its branches swapped, a scan that
//! starts at `0`, a missing `n = 0` guard and an off-by-one fuel bound exactly
//! as happily as the intended search. Only evaluation separates them.
//!
//! Every value below was computed **in Python before any Rust was written**,
//! both by the bounded search these definitions implement and by Mathlib's
//! prime-factorisation formula, over all `(n, a)` with `n ∈ [0, 4]` and
//! `a ∈ [0, 79]`: 400 pairs, zero mismatches. The arguments used here were
//! then chosen from that table for what they DISCRIMINATE, not for what they
//! confirm.
//!
//! ## What the arguments rule out
//!
//! | instance | value | rules out |
//! | --- | --- | --- |
//! | `floorRoot 2 12` | `2` | `12` (branches swapped), `1` (scan reversed), `3` (the numeric root) |
//! | `ceilRoot 2 12` | `6` | `0` (scan starts at `0`, where `a ∣ 0 ^ n` always), `12` (least/greatest confused), `4` (the numeric root) |
//! | `floorRoot 3 8`, `ceilRoot 3 8` | `2`, `2` | an off-by-one in either scan, at a perfect cube where the two must agree |
//! | `floorRoot 0 5` | `0` | a missing `n = 0` guard, which would give `5` |
//! | `ceilRoot 0 1` | `0` | a missing `n = 0` guard, which would give `1` |
//! | `ceilRoot 2 1` | `1` | a fuel bound of `a - 1` rather than `a` |
//!
//! ## The control that does NOT work, and it is measured rather than asserted
//!
//! `ceilRoot 0 5` is `0` **with or without** the `n = 0` guard: with `n = 0`
//! the test is `5 ∣ i ^ 0 = 1`, false at every `i`, so the unguarded scan runs
//! out of fuel and returns `0` anyway. Using it as the guard's control would
//! be the vacuous-control failure this repository keeps rediscovering, so
//! `the_n_zero_guard_is_live` builds the UNGUARDED scan as a term and pins
//! both directions: the guard bites at `a = 1` and is invisible at `a = 5`.
//!
//! All magnitudes are single- or low-double-digit: this prelude's numerals are
//! unary towers, so the kernel's binary literal fast path never fires and a
//! large argument would cost more than the whole prelude (`CLAUDE.md`). The
//! largest value formed anywhere below is `8 ^ 3 = 512`.

use crate::expr::ExprId;
use crate::{BinderInfo, Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    fn floor_root(&mut self, n: u32, a: u32) -> ExprId {
        let p = self.p;
        let n_expr = self.num(n);
        let a_expr = self.num(a);
        self.const_app(p.floor_root, &[n_expr, a_expr])
    }

    fn ceil_root(&mut self, n: u32, a: u32) -> ExprId {
        let p = self.p;
        let n_expr = self.num(n);
        let a_expr = self.num(a);
        self.const_app(p.ceil_root, &[n_expr, a_expr])
    }

    /// Assert `lhs` reduces to the numeral `want`, and to nothing else in
    /// `wrong`. Both sides of every comparison are closed numerals, so the
    /// negative direction terminates — a failing `def_eq` between two open
    /// terms is unbounded, which is the pathology ADR-1230 records.
    fn expect(&mut self, lhs: ExprId, want: u32, wrong: &[(u32, &str)], what: &str) {
        let want_expr = self.num(want);
        assert!(
            self.k.def_eq(lhs, want_expr),
            "{what} must reduce to {want}"
        );
        for (value, why) in wrong {
            let bad = self.num(*value);
            assert!(
                !self.k.def_eq(lhs, bad),
                "{what} must not be {value}: that is {why}"
            );
        }
    }

    /// `Nat.floorRoot`'s inner scan with the `n = 0` guard REMOVED, at a
    /// concrete exponent. Duplicated from `factorization_root.rs` on purpose
    /// and only here: it exists so the guard's control can be shown to
    /// discriminate rather than asserted to.
    fn unguarded_floor_scan(&mut self, n: u32, a: u32) -> ExprId {
        let p = self.p;
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let one = self.level_one();
        let exponent = self.num(n);
        let a_expr = self.num(a);

        let motive = self.k.lam(anon, nat, nat, BinderInfo::Default);
        let base = self.zero();
        let step = {
            let b_fv = self.fresh_fvar();
            let ih_fv = self.fresh_fvar();
            let b = self.k.fvar(b_fv);
            let ih = self.k.fvar(ih_fv);
            let candidate = self.succ(b);
            let power = self.pow(candidate, exponent);
            let remainder = self.modulo(a_expr, power);
            let zero = self.zero();
            let divides = self.beq(remainder, zero);
            let body = self.bool_select_nat(divides, candidate, ih);
            let with_ih = self.lam_fv(ih_fv, nat, body);
            self.lam_fv(b_fv, nat, with_ih)
        };
        let rec = self.k.const_(p.rec, vec![one]);
        self.apply(rec, &[motive, base, step, a_expr])
    }

    /// `Nat.ceilRoot`'s inner scan with the `n = 0` guard REMOVED. See
    /// [`Self::unguarded_floor_scan`].
    fn unguarded_ceil_scan(&mut self, n: u32, a: u32) -> ExprId {
        let p = self.p;
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let one = self.level_one();
        let exponent = self.num(n);
        let a_expr = self.num(a);

        let nat_to_nat = self.arrow(nat, nat);
        let motive = self.k.lam(anon, nat, nat_to_nat, BinderInfo::Default);
        let base = {
            let zero = self.zero();
            self.k.lam(anon, nat, zero, BinderInfo::Default)
        };
        let step = {
            let fuel_fv = self.fresh_fvar();
            let g_fv = self.fresh_fvar();
            let i_fv = self.fresh_fvar();
            let g = self.k.fvar(g_fv);
            let i = self.k.fvar(i_fv);
            let power = self.pow(i, exponent);
            let remainder = self.modulo(power, a_expr);
            let zero = self.zero();
            let divided = self.beq(remainder, zero);
            let next = self.succ(i);
            let recurse = self.apply(g, &[next]);
            let body = self.bool_select_nat(divided, i, recurse);
            let with_i = self.lam_fv(i_fv, nat, body);
            let with_g = self.lam_fv(g_fv, nat_to_nat, with_i);
            self.lam_fv(fuel_fv, nat, with_g)
        };
        let rec = self.k.const_(p.rec, vec![one]);
        let scan = self.apply(rec, &[motive, base, step, a_expr]);
        let start = self.num(1);
        self.k.app(scan, start)
    }
}

/// The two roots disagree with each other AND with the numeric `n`-th root.
///
/// `a = 12 = 2^2 · 3`. The greatest `b` with `b^2 ∣ 12` is `2`; the least
/// `b ≥ 1` with `12 ∣ b^2` is `6`; and `⌊√12⌋ = 3` is neither. That third
/// comparison is the one that matters for the adjacency question, because
/// `Nat.nthRoot` is already declared and shares the word "root": these are
/// divisibility-lattice adjoints and it is an order statement, and here they
/// are measured to be different functions rather than argued to be.
///
/// `a = 8` is deliberately NOT used for the numeric comparison:
/// `floorRoot 2 8 = 2` and `⌊√8⌋ = 2` agree, so that control would pass while
/// measuring nothing.
#[test]
fn the_two_roots_disagree_with_each_other_and_with_the_numeric_root() {
    let mut f = Fixture::new();
    let p = f.p;

    let floor = f.floor_root(2, 12);
    f.expect(
        floor,
        2,
        &[
            (12, "the `bool_select_nat` branches swapped, so the first `b` tried wins"),
            (1, "the scan reversed, returning the LEAST such `b` instead"),
            (3, "the numeric root, which this is not"),
        ],
        "floorRoot 2 12",
    );

    let ceil = f.ceil_root(2, 12);
    f.expect(
        ceil,
        6,
        &[
            (0, "a scan started at `i = 0`, where `a ∣ 0 ^ n` holds vacuously"),
            (12, "the greatest witness rather than the least"),
            (4, "the numeric root, which this is not"),
        ],
        "ceilRoot 2 12",
    );

    // The numeric root is pinned too, so neither negative above can pass for
    // the wrong reason -- an `Nat.nthRoot` that computed something else would
    // make "these differ" true and meaningless.
    let numeric = {
        let two = f.num(2);
        let twelve = f.num(12);
        f.const_app(p.nth_root, &[two, twelve])
    };
    f.expect(numeric, 3, &[], "nthRoot 2 12 (the control's control)");
}

/// At a perfect `n`-th power the two roots must coincide, and `8 = 2^3` is the
/// cheapest place to say so: both scans stop at `2`.
///
/// This is the case an off-by-one in either scan breaks — `floorRoot` would
/// return `1` if it tested `b` rather than `succ b`, and `ceilRoot` would
/// return `3` if it advanced before testing.
#[test]
fn a_perfect_power_makes_the_two_roots_coincide() {
    let mut f = Fixture::new();

    let floor = f.floor_root(3, 8);
    f.expect(
        floor,
        2,
        &[(1, "a step testing `b` rather than `succ b`"), (8, "the bound itself")],
        "floorRoot 3 8",
    );

    let ceil = f.ceil_root(3, 8);
    f.expect(
        ceil,
        2,
        &[(3, "a scan advancing before testing"), (1, "a scan that never advances")],
        "ceilRoot 3 8",
    );
}

/// The `n = 0` guard is live on BOTH definitions — and the obvious control is
/// vacuous on one of them, which is measured here rather than asserted.
///
/// `floorRoot 0 5 = 0`, while the unguarded scan gives `5` (`b^0 = 1` divides
/// everything, so the greatest `b ≤ 5` wins). `ceilRoot 0 1 = 0`, while the
/// unguarded scan gives `1` (`1 ∣ 1^0`). But `ceilRoot 0 5` is `0` either way,
/// because `5 ∤ 1`, so a guard test written at `a = 5` would pass against a
/// definition with no guard at all.
#[test]
fn the_n_zero_guard_is_live_and_one_obvious_control_is_vacuous() {
    let mut f = Fixture::new();

    let floor = f.floor_root(0, 5);
    f.expect(floor, 0, &[(5, "the unguarded scan's answer")], "floorRoot 0 5");
    let floor_unguarded = f.unguarded_floor_scan(0, 5);
    f.expect(
        floor_unguarded,
        5,
        &[(0, "the guarded answer, which would make this control vacuous")],
        "the unguarded floorRoot scan at (0, 5)",
    );

    let ceil = f.ceil_root(0, 1);
    f.expect(ceil, 0, &[(1, "the unguarded scan's answer")], "ceilRoot 0 1");
    let ceil_unguarded = f.unguarded_ceil_scan(0, 1);
    f.expect(
        ceil_unguarded,
        1,
        &[(0, "the guarded answer, which would make this control vacuous")],
        "the unguarded ceilRoot scan at (0, 1)",
    );

    // ... and the vacuity itself, so nobody reuses `a = 5` for `ceilRoot`.
    let ceil_five = f.ceil_root(0, 5);
    f.expect(ceil_five, 0, &[], "ceilRoot 0 5");
    let ceil_five_unguarded = f.unguarded_ceil_scan(0, 5);
    f.expect(
        ceil_five_unguarded,
        0,
        &[],
        "the unguarded ceilRoot scan at (0, 5) -- EQUAL to the guarded one, \
         which is why `a = 5` is not a control for ceilRoot's guard",
    );
}

/// Mathlib guards on `n = 0 ∨ a = 0`; only the first disjunct survives here,
/// and this is why the second is dead code rather than a dropped case.
///
/// `floorRoot`'s downward scan over `a = 0` hits its `Nat.rec` base case and
/// `ceilRoot`'s upward scan has zero fuel, so both return `0` unaided. The
/// `ceilRoot 2 1 = 1` assertion is what separates that from a fuel bound one
/// too small, which would return `0` there as well.
#[test]
fn the_dropped_a_zero_disjunct_is_dead_code() {
    let mut f = Fixture::new();

    let floor = f.floor_root(2, 0);
    f.expect(floor, 0, &[(1, "a scan whose base case is not `0`")], "floorRoot 2 0");

    let ceil = f.ceil_root(2, 0);
    f.expect(ceil, 0, &[(1, "a scan given fuel it should not have")], "ceilRoot 2 0");

    // One unit of fuel is enough and is present: the bound is `a`, not `a - 1`.
    let ceil_one = f.ceil_root(2, 1);
    f.expect(ceil_one, 1, &[(0, "a fuel bound of `a - 1`")], "ceilRoot 2 1");

    let floor_one = f.floor_root(2, 1);
    f.expect(floor_one, 1, &[(0, "a scan that never reaches `b = 1`")], "floorRoot 2 1");
}
