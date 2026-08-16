//! `Rat` — the rational numbers, as a **normalised structure** over the proved
//! `ℤ` and `ℕ` developments.
//!
//! ## Why a structure and not a quotient
//!
//! The textbook construction is a setoid quotient of `ℤ × ℤ≠0` by
//! cross-multiplication. In *this* kernel that is not merely expensive, it is
//! **inexpressible**: the quotient package is four declarations — `Quot`,
//! `Quot.mk`, `Quot.lift`, `Quot.ind` — with **no `Quot.sound`**, so nothing can
//! prove two `Quot.mk`s equal (ADR-0456).
//!
//! Lean 4.30.0's own source, read rather than guessed, does not use a quotient
//! either (`Init/Data/Rat/Basic.lean`):
//!
//! ```text
//! structure Rat where
//!   num : Int
//!   den : Nat := 1
//!   den_nz : den ≠ 0
//!   reduced : num.natAbs.Coprime den
//! ```
//!
//! A normalised representative plus two proof fields. That is the same move
//! `Int` already makes here — `ofNat`/`negSucc` give every integer exactly one
//! representative — so `Eq Rat` is ordinary propositional equality and a derived
//! law's axiom footprint stays genuinely empty.
//!
//! ## The two proof fields
//!
//! - **Positivity** is stated as `1 ≤ den` rather than Lean's `den ≠ 0`. Our
//!   order development produces and consumes `Nat.le (succ zero) d` directly —
//!   it is the shape `div_mod_exists`, `mul_left_cancel_of_pos` and
//!   `dvd_add_right_cancel_of_pos` all take — whereas `≠ 0` would have to be
//!   converted at every use. The two are equivalent over `ℕ`; this one is free.
//! - **Reducedness** is `gcd (natAbs num) den = 1`, discharged for a concrete
//!   rational by `rfl`, because `Nat.gcd` is executable.
//!
//! ## Where this lives
//!
//! Inside the integer prelude, for now. ADR-0001's rule is that a boundary is
//! added once it is *proven by use*, and that applies to a new prelude as much
//! as to a new crate: `IntDev` already carries both the `Int` and `Nat` names
//! this needs, and nothing yet consumes `Rat` from outside.

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{BinderInfo, ExprId};
use crate::nat_prelude::NatOps;

use super::ops::IntDev;

/// Height for `Rat.normalize`: it unfolds to one `Int.rec` over the reduced
/// pair, so it sits with the other derived operations.
const DERIVED_HEIGHT: u16 = 6;

/// Admit `Rat : Type` with its single normalising constructor.
///
/// ```text
/// Rat.mk : (num : Int) → (den : Nat) → 1 ≤ den →
///          gcd (natAbs num) den = 1 → Rat
/// ```
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructor's telescope does not
/// check — in particular if a proof field's type mentions a later field.
pub(super) fn declare_rat(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let one = d.level_one();
    let type1 = d.kernel().sort(one);
    let rat_ty = d.kernel().const_(p.rat, vec![]);

    let num_fv = d.fresh_fvar();
    let num = d.kernel().fvar(num_fv);
    let den_fv = d.fresh_fvar();
    let den = d.kernel().fvar(den_fv);

    // `1 ≤ den`, the positivity the ℕ division and cancellation lemmas take.
    let positive = {
        let zero = d.zero();
        let unit = d.succ(zero);
        NatOps::le(d, unit, den)
    };
    // `gcd (natAbs num) den = 1`, reducible to `rfl` at a concrete rational.
    let reduced = {
        let magnitude = d.const_app(p.nat_abs, &[num]);
        let common = NatOps::gcd(d, magnitude, den);
        let zero = d.zero();
        let unit = d.succ(zero);
        d.eq(common, unit)
    };

    let anon = d.anon_name();
    let ctor_ty = {
        let after_reduced = d.kernel().pi(anon, reduced, rat_ty, BinderInfo::Default);
        let after_positive = d
            .kernel()
            .pi(anon, positive, after_reduced, BinderInfo::Default);
        let after_den = d.pi_fv(den_fv, nat, after_positive);
        d.pi_fv(num_fv, int_ty, after_den)
    };

    d.kernel()
        .add_inductive(p.rat, &[], 0, type1, &[(p.rat_mk, ctor_ty)])
}

/// Admit `Rat.normalize : (num : Int) → (den : Nat) → 1 ≤ den → Rat`.
///
/// The smart constructor. It divides numerator and denominator by
/// `g = gcd (natAbs num) den` and discharges both of `Rat`'s proof fields,
/// so a caller never has to supply them.
///
/// Every step is a lemma proved in this development:
///
/// ```text
/// 1 ≤ g            one_le_of_dvd_pos, straight from the divisibility WITNESS —
///                  no division, which is what breaks the circularity
/// g·(den/g) = den  div_mul_cancel_of_dvd
/// 1 ≤ den/g        one_le_right_of_mul, on the rewritten `1 ≤ den`
/// reduced          gcd_cofactors_coprime, fed by the two cancellations
/// ```
///
/// The `negSucc` branch additionally rewrites through
/// [`super::nat_abs::declare_nat_abs_neg_of_nat`], because its numerator is
/// built with `negOfNat` and the `reduced` field speaks of `natAbs`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_normalize(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let rat_ty = d.kernel().const_(p.rat, vec![]);

    let num_fv = d.fresh_fvar();
    let num = d.kernel().fvar(num_fv);
    let den_fv = d.fresh_fvar();
    let den = d.kernel().fvar(den_fv);
    let positive_fv = d.fresh_fvar();
    let positive = d.kernel().fvar(positive_fv);

    let positive_ty = {
        let zero = d.zero();
        let unit = d.succ(zero);
        NatOps::le(d, unit, den)
    };

    // One branch, parameterised by the numerator's magnitude and how to rebuild
    // the numerator from its reduced magnitude.
    let branch = |d: &mut IntDev<'_>, magnitude: ExprId, negative: bool| -> ExprId {
        let common = NatOps::gcd(d, magnitude, den);
        let divides_magnitude = d.const_app(p.nat.gcd_dvd_left, &[magnitude, den]);
        let divides_den = d.const_app(p.nat.gcd_dvd_right, &[magnitude, den]);
        let common_positive = d.const_app(
            p.nat.one_le_of_dvd_pos,
            &[common, den, positive, divides_den],
        );
        let cancel_den = d.const_app(
            p.nat.div_mul_cancel_of_dvd,
            &[common, den, common_positive, divides_den],
        );
        let cancel_magnitude = d.const_app(
            p.nat.div_mul_cancel_of_dvd,
            &[common, magnitude, common_positive, divides_magnitude],
        );

        let reduced_den = NatOps::div(d, den, common);
        let reduced_magnitude = NatOps::div(d, magnitude, common);
        let scaled_den = NatOps::mul(d, common, reduced_den);
        let scaled_magnitude = NatOps::mul(d, common, reduced_magnitude);

        // 1 ≤ den/g, by rewriting `1 ≤ den` back through the cancellation.
        let den_positive = {
            let lifted = {
                // Anchored at `den`, because that is where the transport
                // STARTS; anchoring it at `scaled_den` type-checks in Rust and
                // is rejected by the kernel.
                let motive = d.eq_motive(den, &|d, x| {
                    let zero = d.zero();
                    let unit = d.succ(zero);
                    NatOps::le(d, unit, x)
                });
                let back = d.symm(scaled_den, den, cancel_den);
                d.transport(den, motive, positive, scaled_den, back)
            };
            d.const_app(p.nat.one_le_right_of_mul, &[common, reduced_den, lifted])
        };

        // gcd (g·(m/g)) (g·(den/g)) = gcd m den, which IS `= g` definitionally.
        let witness = {
            let mid = NatOps::gcd(d, magnitude, scaled_den);
            let target = NatOps::gcd(d, magnitude, den);
            let first = d.congr(scaled_magnitude, magnitude, cancel_magnitude, &|d, x| {
                NatOps::gcd(d, x, scaled_den)
            });
            let second = d.congr(scaled_den, den, cancel_den, &|d, x| {
                NatOps::gcd(d, magnitude, x)
            });
            let start = NatOps::gcd(d, scaled_magnitude, scaled_den);
            let (_reached, chained) = d.chain(start, &[(mid, first), (target, second)]);
            chained
        };
        let coprime = d.const_app(
            p.nat.gcd_cofactors_coprime,
            &[
                common,
                reduced_magnitude,
                reduced_den,
                common_positive,
                witness,
            ],
        );

        let (numerator, reduced) = if negative {
            let numerator = d.neg_of_nat(reduced_magnitude);
            // `natAbs (negOfNat k) = k`, so the coprimality transports across.
            let seen = d.const_app(p.nat_abs_neg_of_nat, &[reduced_magnitude]);
            let restated = {
                let motive = d.eq_motive(reduced_magnitude, &|d, x| {
                    let zero = d.zero();
                    let unit = d.succ(zero);
                    let common = NatOps::gcd(d, x, reduced_den);
                    d.eq(common, unit)
                });
                let magnitude_of = d.const_app(p.nat_abs, &[numerator]);
                let back = d.symm(magnitude_of, reduced_magnitude, seen);
                d.transport(reduced_magnitude, motive, coprime, magnitude_of, back)
            };
            (numerator, restated)
        } else {
            (d.of_nat(reduced_magnitude), coprime)
        };

        let constructor = d.kernel().const_(p.rat_mk, vec![]);
        d.apply(
            constructor,
            &[numerator, reduced_den, den_positive, reduced],
        )
    };

    let motive = d.kernel().lam(anon, int_ty, rat_ty, BinderInfo::Default);
    let minor_of_nat = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = branch(d, n, false);
        d.lam_fv(n_fv, nat, body)
    };
    let minor_neg_succ = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let magnitude = d.succ(n);
        let body = branch(d, magnitude, true);
        d.lam_fv(n_fv, nat, body)
    };
    let rec = d.kernel().const_(p.rec, vec![one]);
    let selected = d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, num]);

    let ty = {
        let after_positive = d
            .kernel()
            .pi(anon, positive_ty, rat_ty, BinderInfo::Default);
        let after_den = d.pi_fv(den_fv, nat, after_positive);
        d.pi_fv(num_fv, int_ty, after_den)
    };
    let value = {
        let with_positive = d.lam_fv(positive_fv, positive_ty, selected);
        let with_den = d.lam_fv(den_fv, nat, with_positive);
        d.lam_fv(num_fv, int_ty, with_den)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.rat_normalize,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })?;
    Ok(())
}
