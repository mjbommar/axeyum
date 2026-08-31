//! Concrete-instance tests for `nat_prelude::find_greatest`.
//!
//! A separate file (rather than an addition to the dense
//! `nat_prelude_tests.rs`) for the merge hazard `avg_pair_tests.rs` and
//! `abundant_deficient_tests.rs` both record: two lanes editing that one file
//! at once have repeatedly produced a conflict git cuts mid-item.
//!
//! **The kernel cannot tell a `Definition` is wrong.**
//! `Π (P : Nat → Prop), DecidablePred Nat P → Nat → Nat` is that type whatever
//! the body computes, so `add_declaration` accepts a swapped `byCases` pair, a
//! predicate tested at the wrong argument, or a base case returning something
//! other than `0` exactly as happily as the intended recursion. Only
//! evaluation separates them, and only at a predicate that is true somewhere
//! and false somewhere else — an always-true or always-false predicate makes
//! every one of those bugs invisible.
//!
//! The predicate used below is `P k := Nat.beq k 2 = true`, true at exactly
//! one point. `Nat.findGreatest P 5` is `2` under the intended definition and
//! a DIFFERENT value under each of the three bugs above (`5` if the branches
//! are swapped, `3` if the test is applied to `m` rather than `succ m`, and
//! whatever the wrong base returns when the search finds nothing). All
//! magnitudes are single digits: this prelude's numerals are unary towers, so
//! the kernel's binary literal fast path never fires and a large argument
//! would cost more than the whole prelude (`CLAUDE.md`).

use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};
use crate::BinderInfo;
use crate::expr::ExprId;

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

    /// `P := fun k => Eq Bool (Nat.beq k target) Bool.true`, together with a
    /// `DecidablePred Nat P` witness.
    ///
    /// The witness goes through `Decidable.ofBool`, which needs both spec
    /// directions of a computed `Bool`. Here the proposition IS the equation
    /// `beq k target = true`, so the positive direction is the identity and
    /// the negative one composes `hf : beq k target = false` with
    /// `hp : beq k target = true` into `Bool.false = Bool.true` (one
    /// `bool_symm` and one `bool_trans`) and eliminates it — the same
    /// contraposition `rat_prelude/decidable.rs` uses for `Rat.decidable_le`.
    fn beq_predicate(&mut self, target: u32) -> (ExprId, ExprId) {
        let p = self.p;
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let bool_true = self.bool_true();
        let bool_false = self.bool_false();

        let pred = {
            let k_fv = self.fresh_fvar();
            let k = self.k.fvar(k_fv);
            let target_expr = self.num(target);
            let test = self.beq(k, target_expr);
            let body = self.bool_eq(test, bool_true);
            self.lam_fv(k_fv, nat, body)
        };

        let witness = {
            let k_fv = self.fresh_fvar();
            let k = self.k.fvar(k_fv);
            let target_expr = self.num(target);
            let test = self.beq(k, target_expr);
            let claim = self.bool_eq(test, bool_true);

            // `Eq Bool test Bool.true -> claim` is `fun h => h`.
            let positive = {
                let h_fv = self.fresh_fvar();
                let h = self.k.fvar(h_fv);
                self.lam_fv(h_fv, claim, h)
            };

            // `Eq Bool test Bool.false -> (claim -> False)`.
            let negative = {
                let hf_fv = self.fresh_fvar();
                let hp_fv = self.fresh_fvar();
                let hf = self.k.fvar(hf_fv);
                let hp = self.k.fvar(hp_fv);
                let flipped = self.bool_symm(test, bool_false, hf);
                let contradiction =
                    self.bool_trans(bool_false, test, bool_true, flipped, hp);
                let false_ty = self.k.const_(p.logic.false_, vec![]);
                let elim = self.false_true_elim(false_ty, contradiction);
                let inner = self.lam_fv(hp_fv, claim, elim);
                let hf_ty = self.bool_eq(test, bool_false);
                self.lam_fv(hf_fv, hf_ty, inner)
            };

            let of_bool = self.k.const_(p.logic.decidable_of_bool, vec![]);
            let body = self.apply(of_bool, &[claim, test, positive, negative]);
            self.lam_fv(k_fv, nat, body)
        };

        // Sanity: the witness really does have type `DecidablePred Nat P`, so
        // a later `def_eq` failure cannot be blamed on a mistyped fixture.
        let one = self.level_one();
        let head = self.k.const_(p.logic.decidable_pred, vec![one]);
        let expected = self.apply(head, &[nat, pred]);
        let inferred = self
            .k
            .infer(witness)
            .expect("the DecidablePred witness must type-check");
        assert!(
            self.k.def_eq(inferred, expected),
            "the fixture witness is not a `DecidablePred Nat P`"
        );
        let _ = anon;
        (pred, witness)
    }

    fn find_greatest(&mut self, pred: ExprId, witness: ExprId, n: u32) -> ExprId {
        let p = self.p;
        let n_expr = self.num(n);
        self.const_app(p.find_greatest, &[pred, witness, n_expr])
    }
}

/// `DecidablePred` unfolds to the Pi type it is defined as, at the one
/// instantiation this prelude uses. If it did not, every `def_eq` below would
/// fail for a reason that has nothing to do with `findGreatest`.
#[test]
fn decidable_pred_unfolds_to_a_pi_over_decidable() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();
    let one = f.level_one();

    let pred = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let two = f.num(2);
        let test = f.beq(k, two);
        let bool_true = f.bool_true();
        let body = f.bool_eq(test, bool_true);
        f.lam_fv(k_fv, nat, body)
    };

    let head = f.k.const_(p.logic.decidable_pred, vec![one]);
    let applied = f.apply(head, &[nat, pred]);

    let expected = {
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let pred_at_a = f.apply(pred, &[a]);
        let decidable = f.k.const_(p.logic.decidable, vec![]);
        let body = f.k.app(decidable, pred_at_a);
        f.pi_fv(a_fv, nat, body)
    };

    assert!(
        f.k.def_eq(applied, expected),
        "`DecidablePred Nat P` must be `Π (a : Nat), Decidable (P a)`"
    );

    // Negative control, differing in one small term: the codomain is
    // `Decidable (P a)`, not `Decidable (P 0)`.
    let wrong = {
        let a_fv = f.fresh_fvar();
        let zero = f.zero();
        let pred_at_zero = f.apply(pred, &[zero]);
        let decidable = f.k.const_(p.logic.decidable, vec![]);
        let body = f.k.app(decidable, pred_at_zero);
        f.pi_fv(a_fv, nat, body)
    };
    assert!(
        !f.k.def_eq(applied, wrong),
        "the unfolding must depend on the bound argument"
    );
    let _ = anon;
}

/// The search walks DOWN from `n` and stops at the greatest witness.
///
/// `P k := (k = 2)`, so `findGreatest P 5 = 2`: `5`, `4` and `3` all fail and
/// `2` is the first success reached from above. This one value rules out three
/// distinct wrong definitions at once —
///
/// * `5`, if the `Decidable.byCases` branches are swapped (the predicate is
///   consulted and the answer ignored, so the first argument tested wins);
/// * `3`, if the step tests `P m` rather than `P (succ m)` (an off-by-one
///   that a `findGreatest P 2 = 2` check alone would NOT catch, because the
///   two definitions agree there);
/// * `0`, if the recursion never returns `succ m` at all.
#[test]
fn find_greatest_returns_the_greatest_witness_below_the_bound() {
    let mut f = Fixture::new();
    let (pred, witness) = f.beq_predicate(2);

    let got = f.find_greatest(pred, witness, 5);
    let two = f.num(2);
    assert!(
        f.k.def_eq(got, two),
        "findGreatest (· = 2) 5 must be 2 -- the greatest k <= 5 with k = 2"
    );

    for (wrong, why) in [(5u32, "branches swapped"), (3, "tests P m, not P (m+1)")] {
        let wrong_expr = f.num(wrong);
        assert!(
            !f.k.def_eq(got, wrong_expr),
            "findGreatest (· = 2) 5 must not be {wrong} ({why})"
        );
    }
}

/// The bound itself is in range: `findGreatest P n = n` when `P n` holds.
///
/// Paired with the test above rather than standing alone: `5 -> 2` alone is
/// also consistent with a definition that never returns its own argument, and
/// `2 -> 2` alone is consistent with the identity. Each rules out what the
/// other admits.
#[test]
fn find_greatest_accepts_the_bound_itself() {
    let mut f = Fixture::new();
    let (pred, witness) = f.beq_predicate(2);

    let got = f.find_greatest(pred, witness, 2);
    let two = f.num(2);
    assert!(
        f.k.def_eq(got, two),
        "findGreatest (· = 2) 2 must be 2 -- the bound satisfies the predicate"
    );

    let zero = f.zero();
    assert!(
        !f.k.def_eq(got, zero),
        "findGreatest (· = 2) 2 must not be 0; the bound is a legal answer"
    );
}

/// `0` is the sentinel when no witness is in range, and it is NOT a witness
/// itself: `findGreatest P n` never tests `P 0`, so the two situations are
/// deliberately indistinguishable in the value — Mathlib's own convention,
/// which `Nat.findGreatest_eq_zero_iff` is about.
#[test]
fn find_greatest_returns_zero_when_no_witness_is_in_range() {
    let mut f = Fixture::new();
    let (pred, witness) = f.beq_predicate(2);

    let got = f.find_greatest(pred, witness, 1);
    let zero = f.zero();
    assert!(
        f.k.def_eq(got, zero),
        "findGreatest (· = 2) 1 must be 0 -- no k <= 1 satisfies k = 2"
    );

    let one = f.num(1);
    assert!(
        !f.k.def_eq(got, one),
        "findGreatest (· = 2) 1 must not be 1; the bound does not satisfy the \
         predicate"
    );
}

/// The base case does not consult the predicate: `findGreatest P 0 = 0` even
/// when `P 0` holds.
///
/// This is the one place the definition could plausibly have been written
/// "helpfully" and wrongly, and no other test here reaches it — every
/// predicate above is false at `0`.
#[test]
fn find_greatest_at_zero_is_zero_even_when_the_predicate_holds_there() {
    let mut f = Fixture::new();
    let (pred, witness) = f.beq_predicate(0);

    let got = f.find_greatest(pred, witness, 0);
    let zero = f.zero();
    assert!(
        f.k.def_eq(got, zero),
        "findGreatest (· = 0) 0 must be 0"
    );

    // ... and the SAME predicate at a positive bound still finds nothing,
    // because `0` is never tested. `findGreatest (· = 0) 3 = 0` too, which
    // is the value the sentinel takes -- so this pair is what shows the base
    // case is a sentinel and not a witness.
    let at_three = f.find_greatest(pred, witness, 3);
    let zero_again = f.zero();
    assert!(
        f.k.def_eq(at_three, zero_again),
        "findGreatest (· = 0) 3 must be 0"
    );
}

/// A predicate true at more than one point returns the LARGEST, not the
/// first found or the smallest.
///
/// `P k := (k <= 3)` via `Nat.ble`, true at `0..3`. `findGreatest P 6 = 3`.
/// Distinct from the single-witness tests above: with one witness, "largest"
/// and "any" coincide.
#[test]
fn find_greatest_picks_the_largest_of_several_witnesses() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let bool_true = f.bool_true();
    let bool_false = f.bool_false();

    let pred = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let three = f.num(3);
        let test = f.ble(k, three);
        let body = f.bool_eq(test, bool_true);
        f.lam_fv(k_fv, nat, body)
    };
    let witness = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let three = f.num(3);
        let test = f.ble(k, three);
        let claim = f.bool_eq(test, bool_true);
        let positive = {
            let h_fv = f.fresh_fvar();
            let h = f.k.fvar(h_fv);
            f.lam_fv(h_fv, claim, h)
        };
        let negative = {
            let hf_fv = f.fresh_fvar();
            let hp_fv = f.fresh_fvar();
            let hf = f.k.fvar(hf_fv);
            let hp = f.k.fvar(hp_fv);
            let flipped = f.bool_symm(test, bool_false, hf);
            let contradiction = f.bool_trans(bool_false, test, bool_true, flipped, hp);
            let false_ty = f.k.const_(p.logic.false_, vec![]);
            let elim = f.false_true_elim(false_ty, contradiction);
            let inner = f.lam_fv(hp_fv, claim, elim);
            let hf_ty = f.bool_eq(test, bool_false);
            f.lam_fv(hf_fv, hf_ty, inner)
        };
        let of_bool = f.k.const_(p.logic.decidable_of_bool, vec![]);
        let body = f.apply(of_bool, &[claim, test, positive, negative]);
        f.lam_fv(k_fv, nat, body)
    };

    let got = f.find_greatest(pred, witness, 6);
    let three = f.num(3);
    assert!(
        f.k.def_eq(got, three),
        "findGreatest (· <= 3) 6 must be 3 -- the LARGEST k <= 6 with k <= 3"
    );

    for (wrong, why) in [(6u32, "returned the bound"), (0, "returned the smallest")] {
        let wrong_expr = f.num(wrong);
        assert!(
            !f.k.def_eq(got, wrong_expr),
            "findGreatest (· <= 3) 6 must not be {wrong} ({why})"
        );
    }
    let _ = BinderInfo::Default;
}
