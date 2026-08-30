//! Two small pieces toward `Nat.totient_mul_of_coprime`
//! (`Coprime m n -> totient(m*n) = totient(m)*totient(n)`), the base case
//! all three remaining open `ml430` totient mirrors need per
//! `docs/plan/status/301-totient-multiplicative.md` and its correction in
//! `docs/plan/status/316-queue-sweep.md`.
//!
//! **This file does NOT attempt the full formula.** `316` corrected `301`'s
//! own Step 4 (`Nat.count_range_row_major`): the row-major double-counting
//! identity is FALSE without `Coprime m n` (it is exactly CRT bijectivity of
//! `x -> (x mod m, x mod n)`), and a correct version needs "`countRange` is
//! invariant under a domain bijection" as a further new primitive plus the
//! CRT self-map `g` from `nat_prelude/crt.rs` -- sized by `316` as several
//! more dispatches, not a same-session extension. Nothing here touches that.
//!
//! What this file lands instead are the two pieces `301`'s own Steps 1 and 3
//! named as buildable from what already exists in this prelude, neither of
//! which needed `count_range_row_major` at all:
//!
//! [`declare_gcd_mod_left_eq_gcd`] is `Nat.gcd_mod_left_eq_gcd : ∀ x m, Eq
//! (gcd (mod x m) m) (gcd x m)` (`301`'s "Step 1", mod-gcd invariance). Case
//! split on `m`: at `m = 0`, `Nat.mod_zero` gives `mod x 0 = x` directly, so
//! congruence closes it. At `m = succ k`, `Nat.gcd_succ` gives
//! `gcd m x = gcd (mod x m) m` and `Nat.gcd_comm` bridges `gcd m x` to
//! `gcd x m`, chained via `symm`/`trans` to the stated direction. Both
//! ingredients (`gcd_succ`, `gcd_comm`) were already declared before this
//! file's dispatch point; no new induction.
//!
//! [`declare_coprime_mul_iff`] is `Nat.coprime_mul_iff : ∀ x m n, Iff (Eq
//! (gcd x (mul m n)) one) (And (Eq (gcd x m) one) (Eq (gcd x n) one))` --
//! `301`'s "Step 3" pointwise predicate identity, minus the `mod`
//! substitution (which needs [`declare_gcd_mod_left_eq_gcd`] composed in at
//! the call site, not here). **No `Coprime m n` hypothesis is needed at
//! all** -- this is a genuine unconditional fact, unlike
//! `count_range_row_major`: the forward direction is pure shrinking
//! (`Nat.coprime_mul_right_right`/`Nat.coprime_mul_left_right`, both already
//! declared), and the backward direction is exactly
//! `Nat.coprime_mul_of_coprime` (landed by the prior `totient-mult-finish`
//! dispatch), applied to `x` against `m` and `n` separately -- it was never
//! stated as an `Iff` before, only as its two constituent implications.
//!
//! Neither lemma is attached to a fact (unregistered nat-prelude helper
//! theorems, like `gcd_comm`/`coprime_mul_of_coprime` before them).

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.gcd_mod_left_eq_gcd : ∀ x m, Eq (gcd (mod x m) m) (gcd x m)`. See the
/// module doc for the case split.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gcd_mod_left_eq_gcd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gcd_mod_left_eq_gcd, 2, &|d, v| {
        let x = v[0];
        let m_outer = v[1];

        let motive = |d: &mut NatDev<'_>, m: ExprId| -> ExprId {
            let mod_x_m = d.modulo(x, m);
            let lhs = d.gcd(mod_x_m, m);
            let rhs = d.gcd(x, m);
            d.eq(lhs, rhs)
        };

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let mod_x_zero_eq_x = d.lemma(p.mod_zero, &[x]); // Eq (mod x 0) x
            let mod_x_zero = d.modulo(x, zero);
            d.congr(mod_x_zero, x, mod_x_zero_eq_x, &|d, z| d.gcd(z, zero))
        };

        let at_succ = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
            let m = d.succ(k);
            // gcd_succ(k, x) : Eq (gcd m x) (gcd (mod x m) m)
            let gs = d.lemma(p.gcd_succ, &[k, x]);
            // gcd_comm(m, x) : Eq (gcd m x) (gcd x m)
            let gc = d.lemma(p.gcd_comm, &[m, x]);
            let gcd_m_x = d.gcd(m, x);
            let gcd_x_m = d.gcd(x, m);
            let mod_x_m = d.modulo(x, m);
            let gcd_modxm_m = d.gcd(mod_x_m, m);

            // step1 : Eq (gcd x m) (gcd m x)  = symm(gc)
            let step1 = d.symm(gcd_m_x, gcd_x_m, gc);
            // combined : Eq (gcd x m) (gcd (mod x m) m), chaining step1 then gs
            let combined = d.trans(gcd_x_m, gcd_m_x, gcd_modxm_m, step1, gs);
            // final : Eq (gcd (mod x m) m) (gcd x m)
            d.symm(gcd_x_m, gcd_modxm_m, combined)
        };

        let proof = cases_zero_succ(d, m_outer, &motive, &at_zero, &at_succ);
        let stmt = motive(d, m_outer);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.coprime_mul_iff : ∀ x m n, Iff (Eq (gcd x (mul m n)) one) (And (Eq
/// (gcd x m) one) (Eq (gcd x n) one))`. See the module doc: no `Coprime m n`
/// hypothesis needed, `mp` shrinks via the two already-declared
/// `coprime_mul_*_right` lemmas, `mpr` is `coprime_mul_of_coprime`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_mul_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_mul_iff, 3, &|d, v| {
        let x = v[0];
        let m = v[1];
        let n = v[2];
        let one = d.num(1);

        let mn = d.mul(m, n);
        let gcd_x_mn = d.gcd(x, mn);
        let lhs_ty = d.eq(gcd_x_mn, one);

        let gcd_x_m = d.gcd(x, m);
        let eq_x_m_ty = d.eq(gcd_x_m, one);
        let gcd_x_n = d.gcd(x, n);
        let eq_x_n_ty = d.eq(gcd_x_n, one);
        let rhs_ty = d.const_app(p.logic.and, &[eq_x_m_ty, eq_x_n_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let left = d.lemma(p.coprime_mul_right_right, &[x, m, n, h]); // Eq (gcd x m) one
            let right = d.lemma(p.coprime_mul_left_right, &[x, m, n, h]); // Eq (gcd x n) one
            let body = d.const_app(p.logic.and_intro, &[eq_x_m_ty, eq_x_n_ty, left, right]);
            d.lam_fv(h_fv, lhs_ty, body)
        };

        let mpr = {
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let h1 = and_left(d, eq_x_m_ty, eq_x_n_ty, hand);
            let h2 = and_right(d, eq_x_m_ty, eq_x_n_ty, hand);
            let body = d.lemma(p.coprime_mul_of_coprime, &[x, m, n, h1, h2]);
            d.lam_fv(hand_fv, rhs_ty, body)
        };

        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}
