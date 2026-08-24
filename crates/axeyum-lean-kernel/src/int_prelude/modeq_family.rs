//! The `Int.ModEq` family beyond [`super::modeq`] — closing specific rows of
//! the fact ledger's Mathlib-parity slice (`docs/plan/status/` tracks which).
//!
//! ## Why this is a separate file from a separate blocker than `modeq.rs`
//!
//! Every congruence law in [`super::modeq`] is proved under a `0 < n`
//! hypothesis, because its only bridge to `Int.dvd`
//! ([`super::modeq::declare_modeq_iff_dvd`]) needs `Int.emod_lt_of_pos`, which
//! is the ONLY proved upper bound on `emod`'s magnitude in this development —
//! and it only holds for a *positive* divisor
//! (`crates/axeyum-lean-kernel/src/int_prelude/division.rs`'s own header
//! admits a `natAbs`-based bound "not yet built"). Every one of the fifteen
//! Mathlib `Int.ModEq` ledger rows this file targets is stated for **all**
//! `n : ℤ` — no positivity hypothesis anywhere in the Mathlib surface syntax —
//! so reusing `modEq_iff_dvd` as-is would either understate the target (an
//! extra `0 < n` hypothesis the ledger row does not have) or require
//! rebuilding the `natAbs` bound first. This module does neither: instead it
//! proves the one structural fact that sidesteps the bound entirely —
//! [`declare_emod_neg`] — and builds what it can from *that* plus the
//! existing positive-divisor lemmas, without weakening any statement.
//!
//! [`declare_emod_neg`] (`emod a (neg n) = emod a n`) is purely about which
//! *shape* of `n` (`ofNat`/`negSucc`) selects which branch of `emod`'s own
//! `Int.rec` — the natAbs bound never enters it, so it holds unconditionally.
//! It gives the two halves of the ledger's `Int.modEq_neg` row directly
//! ([`declare_modeq_of_neg_modulus`], [`declare_modeq_neg_modulus`]), and
//! chains with the *existing* positive bridge to give the one modulus-`1`
//! row too ([`declare_modeq_one`]) — `0 < 1` is [`super::defs`]'s own
//! `zero_lt_one`, already proved, so no new positivity work is needed there.
//!
//! The remaining rows (additive/multiplicative congruence with no positivity
//! hypothesis, `n ∣ n` style "mod itself" rows, and the `m*n`-modulus rows)
//! all need the general-`n` bridge this module does not build — see
//! `docs/plan/status/` for the record of which ledger ids remain open and
//! why.

use super::ops::{IntDev, Shape, case_split};
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Int.emod_neg : ∀ a n, Int.emod a (Int.neg n) = Int.emod a n`.
///
/// `emod`'s own definition ([`super::division::declare_emod`]) dispatches
/// on the *shape* of its second argument, and — cell by cell — the row
/// chosen for `ofNat (succ k)` and the row chosen for `negSucc k` are the
/// **same formula** (both read off `succ k`, the shared `natAbs`), for
/// either shape of the first argument. Since `Int.neg` sends `ofNat (succ k)`
/// to `negSucc k` and back, negating the modulus only ever swaps between
/// these two rows — so every branch below closes by `Eq.refl` at the shared
/// target, never by an inequality. `ofNat 0` is its own negation and closes
/// the same way trivially. This is why the lemma needs no `n ≠ 0` hypothesis,
/// unlike [`super::division::declare_emod_nonneg`]/`declare_emod_lt_of_pos`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod_neg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.emod_neg, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let aa = args[0];
            let nn = args[1];
            let neg_n = d.ineg(nn);
            let lhs = d.iemod(aa, neg_n);
            let rhs = d.iemod(aa, nn);
            d.ieq(lhs, rhs)
        };
        let stmt = statement(d, &[a, n]);
        let proof = case_split(d, &[a, n], &statement, &|d, branches| {
            let (a_shape, am) = branches[0];
            let (n_shape, nm) = branches[1];
            match n_shape {
                // `neg (negSucc nm)` is `ofNat (succ nm)`; both
                // `emod a (ofNat (succ nm))` and `emod a (negSucc nm)`
                // compute (for either shape of `a`) to the same term, since
                // both rows read off the shared `succ nm`.
                Shape::NegSucc => {
                    let target = negsucc_target(d, a_shape, am, nm);
                    d.irefl(target)
                }
                // `n = ofNat nm`: `neg (ofNat nm)` does not reduce on a
                // free `nm` (it unfolds to `negOfNat nm`, itself stuck), so
                // an inner `Nat.rec` on `nm` is unavoidable — mirrors
                // `nat_abs_neg_of_nat`'s own zero/succ split for exactly the
                // same reason.
                Shape::OfNat => {
                    // `neg (ofNat nm)` unfolds to `negOfNat nm`, which is
                    // itself a `Nat.rec` stuck on a free `nm` — so the goal
                    // (as a function of `nm`) needs its own induction here,
                    // against the SAME `statement` closure the outer theorem
                    // uses, so the two can never drift apart.
                    let a_term = d.branch_term((a_shape, am));
                    let motive = |d: &mut IntDev<'_>, x: ExprId| {
                        let ofnat_x = d.of_nat(x);
                        statement(d, &[a_term, ofnat_x])
                    };
                    let base = |d: &mut IntDev<'_>| {
                        let target = zero_target(d, a_shape, am);
                        d.irefl(target)
                    };
                    let step = |d: &mut IntDev<'_>, j: ExprId, _ih: ExprId| {
                        let target = negsucc_target(d, a_shape, am, j);
                        d.irefl(target)
                    };
                    d.induct(&motive, &base, &step, nm)
                }
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// The shared value both `emod a (ofNat (succ k))` and `emod a (negSucc k)`
/// compute to, for a given shape of `a` — see [`declare_emod_neg`]'s doc.
fn negsucc_target(d: &mut IntDev<'_>, a_shape: Shape, am: ExprId, k: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    match a_shape {
        Shape::OfNat => {
            let r = NatOps::modulo(d, am, succ_k);
            d.of_nat(r)
        }
        Shape::NegSucc => {
            let r = NatOps::modulo(d, am, succ_k);
            let sr = d.succ(r);
            d.sub_nat_nat(succ_k, sr)
        }
    }
}

/// The shared value both `emod a (neg (ofNat 0))` and `emod a (ofNat 0)`
/// compute to (both are literally `emod a (ofNat 0)`, since `neg (ofNat 0)`
/// unfolds to `ofNat 0`), for a given shape of `a`.
fn zero_target(d: &mut IntDev<'_>, a_shape: Shape, am: ExprId) -> ExprId {
    let zero = d.zero();
    match a_shape {
        Shape::OfNat => {
            let r = NatOps::modulo(d, am, zero);
            d.of_nat(r)
        }
        Shape::NegSucc => {
            let r = NatOps::modulo(d, am, zero);
            let sr = d.succ(r);
            d.sub_nat_nat(zero, sr)
        }
    }
}

/// `Int.modEq_of_neg_modulus : ∀ n a b, ModEq (neg n) a b → ModEq n a b`.
///
/// The `mp` half of the ledger's `Int.modEq_neg` row
/// (`a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n]`) — there is no `Iff` in this kernel,
/// so it is split, matching [`declare_modeq_neg_modulus`] for the `mpr` half.
/// Both are direct rewrites along [`declare_emod_neg`], applied once per side
/// of the congruence.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_of_neg_modulus(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_of_neg_modulus, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let neg_n = d.ineg(n);
        let modeq_neg = super::modeq::imodeq(d, neg_n, a, b);
        let modeq_pos = super::modeq::imodeq(d, n, a, b);
        let stmt = d.arrow(modeq_neg, modeq_pos);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // h : emod a (neg n) = emod b (neg n)
        let emod_a_negn = d.iemod(a, neg_n);
        let emod_b_negn = d.iemod(b, neg_n);
        let emod_a_n = d.iemod(a, n);
        let emod_b_n = d.iemod(b, n);

        let lemma_a = d.const_app(p.emod_neg, &[a, n]);
        let lemma_b = d.const_app(p.emod_neg, &[b, n]);

        // emod a n = emod a (neg n) = emod b (neg n) = emod b n
        let lemma_a_rev = d.isymm(emod_a_negn, emod_a_n, lemma_a);
        let (_, proof) = d.ichain(
            emod_a_n,
            &[
                (emod_a_negn, lemma_a_rev),
                (emod_b_negn, h),
                (emod_b_n, lemma_b),
            ],
        );

        let with_h = d.lam_fv(h_fv, modeq_neg, proof);
        (stmt, with_h)
    })?;
    Ok(())
}

/// `Int.modEq_neg_modulus : ∀ n a b, ModEq n a b → ModEq (neg n) a b`.
///
/// The `mpr` half — see [`declare_modeq_of_neg_modulus`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_neg_modulus(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_neg_modulus, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let neg_n = d.ineg(n);
        let modeq_pos = super::modeq::imodeq(d, n, a, b);
        let modeq_neg = super::modeq::imodeq(d, neg_n, a, b);
        let stmt = d.arrow(modeq_pos, modeq_neg);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // h : emod a n = emod b n
        let emod_a_negn = d.iemod(a, neg_n);
        let emod_b_negn = d.iemod(b, neg_n);
        let emod_a_n = d.iemod(a, n);
        let emod_b_n = d.iemod(b, n);

        let lemma_a = d.const_app(p.emod_neg, &[a, n]);
        let lemma_b = d.const_app(p.emod_neg, &[b, n]);
        let lemma_b_rev = d.isymm(emod_b_negn, emod_b_n, lemma_b);

        // emod a (neg n) = emod a n = emod b n = emod b (neg n)
        let (_, proof) = d.ichain(
            emod_a_negn,
            &[
                (emod_a_n, lemma_a),
                (emod_b_n, h),
                (emod_b_negn, lemma_b_rev),
            ],
        );

        let with_h = d.lam_fv(h_fv, modeq_pos, proof);
        (stmt, with_h)
    })?;
    Ok(())
}

/// `Int.modEq_one : ∀ a b, ModEq one a b`.
///
/// Every integer is congruent mod `1`: `1 ∣ (b - a)` unconditionally
/// (witness `b - a` itself, via `Int.one_mul`), and `0 < 1`
/// ([`super::order`]'s `zero_lt_one`) is already proved, so the *existing*
/// positive-divisor bridge ([`super::modeq::declare_modeq_iff_dvd`]) applies
/// directly — no generalization needed, because the modulus here is the
/// concrete literal `1`, not a free variable that could be zero or negative.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_one, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let one = d.ione();
        let stmt = super::modeq::imodeq(d, one, a, b);

        let pos1 = d.const_app(p.zero_lt_one, &[]);
        let sub_ba = d.isub(b, a);

        // (b - a) = 1 * (b - a), via `Int.one_mul`, reversed.
        let one_mul_ba = d.const_app(p.one_mul, &[sub_ba]);
        let product = d.imul(one, sub_ba);
        let witness_eq = d.isymm(product, sub_ba, one_mul_ba);

        let int_ty = d.int_ty();
        let one_level = d.level_one();
        let dvd_ty = super::dvd::idvd(d, one, sub_ba);
        let pred = super::dvd::dvd_predicate(d, one, sub_ba);
        let intro_name = d.int().logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one_level]);
        let dvd_proof = d.apply(intro, &[int_ty, pred, sub_ba, witness_eq]);

        let iff_ab = d.const_app(p.mod_eq_iff_dvd, &[one, a, b, pos1]);
        let mpr = d.const_app(p.logic.iff_mpr, &[stmt, dvd_ty, iff_ab]);
        let proof = d.apply(mpr, &[dvd_proof]);
        (stmt, proof)
    })?;
    Ok(())
}
