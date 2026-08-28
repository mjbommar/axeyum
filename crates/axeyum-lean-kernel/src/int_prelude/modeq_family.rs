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

// ---------------------------------------------------------------------------
// The UNCONDITIONAL `ModEq` shift family: `Int.modEq_add_mul_left` and its
// five direct corollaries.
// ---------------------------------------------------------------------------
//
// `int_prelude/modeq.rs`'s whole additive/multiplicative congruence family is
// gated at `0 < n`, because its only bridge to `Int.dvd`
// ([`super::modeq::declare_modeq_iff_dvd`]) needs `Int.emod_lt_of_pos`, the
// only proved bound on `emod`'s magnitude, and that bound only holds for a
// positive divisor. But eleven Mathlib `Int.ModEq` ledger rows are
// UNCONDITIONAL identities with no hypothesis to combine at all — the
// producer that finds combinator shapes (refl/symm/trans/comm over an
// existing hypothesis) declines every one of them with `TerminalNotClosed`,
// because there is no hypothesis to find a congruence step over.
//
// The fix is not to weaken `modEq_iff_dvd`'s hypothesis (its positivity
// requirement is real: `Int.emod`'s magnitude bound genuinely has no proved
// analogue for a negative modulus). It is to observe that these eleven
// facts do not actually NEED the positivity-gated bridge at every modulus:
// they only need it at a modulus of KNOWN sign, and every modulus in this
// kernel's `Int` is either `0`, or `ofNat (succ k)` (positive, `0 < n` is
// [`crate::nat_prelude::NatOps::zero_lt_succ`] applied to `k`), or `negSucc k`
// (negative, reducible to the positive case via the ALREADY-unconditional
// [`declare_modeq_neg_modulus`]/[`declare_emod_neg`] pair this module already
// proved). `Int.emod _ 0` being the identity (`division.rs`'s own zero
// convention) handles the third leg for free, so a `case_split` on the
// modulus alone closes all three legs without ever needing a magnitude bound
// at a non-positive modulus.
//
// [`declare_modeq_add_mul_left`] is the one genuinely new piece of work:
// `∀ n a q, ModEq n (add (mul n q) a) a` — "adding any multiple of the
// modulus does not change the residue" — proved exactly this way. Every
// other declaration below is a specialization of it (`q := 1`, or
// `q := ediv a n` via [`super::division::declare_ediv_add_emod`]) plus a
// rewrite, not new case-split work.

/// `Eq Int (add a (neg (add x a))) (neg x)` — `a - (x + a) = -x`, for any
/// `x`. Derived from [`super::modeq::cancel_common_addend`] applied to
/// `(0+a) - (x+a) = 0 - x`, rewritten at both ends via `Int.add_comm`/
/// `Int.add_zero`. [`declare_modeq_add_mul_left`]'s positive-modulus branch
/// needs exactly this shape (`x := mul n q`).
fn sub_add_self_left(d: &mut IntDev<'_>, a: ExprId, x: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let neg_x = d.ineg(x);

    let za = d.iadd(zero, a);
    let cc = super::modeq::cancel_common_addend(d, zero, x, a);
    // cc : Eq(add(za, neg(add(x,a))), add(zero, neg_x))

    let a_zero = d.iadd(a, zero);
    let zero_add_a = {
        let comm = d.const_app(p.add_comm, &[zero, a]);
        let add_zero_a = d.const_app(p.add_zero, &[a]);
        d.itrans(za, a_zero, a, comm, add_zero_a)
    };

    let target_rhs0 = d.iadd(zero, neg_x);
    let negx_zero = d.iadd(neg_x, zero);
    let zero_add_negx = {
        let comm = d.const_app(p.add_comm, &[zero, neg_x]);
        let add_zero_negx = d.const_app(p.add_zero, &[neg_x]);
        d.itrans(target_rhs0, negx_zero, neg_x, comm, add_zero_negx)
    };

    let xa_raw = d.iadd(x, a);
    let neg_xa = d.ineg(xa_raw);
    let full_lhs = d.iadd(za, neg_xa);
    let a_form = d.iadd(a, neg_xa);
    let step1 = d.icongr(za, a, zero_add_a, &|d, t| d.iadd(t, neg_xa));
    // step1 : Eq(full_lhs, a_form)
    let step1_rev = d.isymm(full_lhs, a_form, step1);
    // step1_rev : Eq(a_form, full_lhs)

    let (_, chained) = d.ichain(
        a_form,
        &[
            (full_lhs, step1_rev),
            (target_rhs0, cc),
            (neg_x, zero_add_negx),
        ],
    );
    chained
}

/// `Eq Int (mul (neg m) q) (neg (mul m q))` — the mirror distributivity of
/// [`super::super::sub` — i.e. `Int.mul_neg`] (`m * (-q) = -(m*q)`), derived
/// from it plus `Int.mul_comm` rather than declared separately: no case
/// split, exactly the style `int_prelude/gcd.rs`'s own private `neg_mul`
/// helper uses.
fn local_neg_mul(d: &mut IntDev<'_>, m: ExprId, q: ExprId) -> ExprId {
    let p = d.int();
    let neg_m = d.ineg(m);
    let start = d.imul(neg_m, q);

    let q_negm = d.imul(q, neg_m);
    let comm1 = d.const_app(p.mul_comm, &[neg_m, q]);

    let mq = d.imul(q, m);
    let neg_mq = d.ineg(mq);
    let mn = d.const_app(p.mul_neg, &[q, m]);

    let mq2 = d.imul(m, q);
    let neg_mq2 = d.ineg(mq2);
    let comm2 = d.const_app(p.mul_comm, &[q, m]);
    let congr2 = d.icongr(mq, mq2, comm2, &|d, x| d.ineg(x));

    let (_, chained) = d.ichain(start, &[(q_negm, comm1), (neg_mq, mn), (neg_mq2, congr2)]);
    chained
}

/// `Int.ModEq (ofNat (succ k)) (add x a) a`, given a witness `c` and a proof
/// that `x = mul (ofNat (succ k)) c` — the positive-modulus leg
/// [`declare_modeq_add_mul_left`]'s `case_split` needs, generalized over an
/// arbitrary already-known multiple `x` (not just `mul m q` literally) so the
/// `negSucc` leg can reuse it at a differently-shaped `x` too.
///
/// Route: [`super::modeq::declare_modeq_iff_dvd`]'s `mpr`, at
/// `h_pos := `[`crate::nat_prelude::NatOps::zero_lt_succ`]` k` (which IS
/// `Int.lt zero (ofNat (succ k))` up to defeq, since `Int.lt` on two `ofNat`s
/// reduces to `Nat.lt`), with divisibility witness `neg c`:
/// `a - (x+a) = -x = -(m*c) = m*(-c)` via [`sub_add_self_left`] and
/// `Int.mul_neg`.
fn modeq_shift_pos(
    d: &mut IntDev<'_>,
    k: ExprId,
    a: ExprId,
    x: ExprId,
    c: ExprId,
    x_eq_mc: ExprId,
) -> ExprId {
    let p = d.int();
    let succ_k = d.succ(k);
    let m = d.of_nat(succ_k);
    let xa = d.iadd(x, a);
    let modeq_ty = super::modeq::imodeq(d, m, xa, a);

    let h_pos = d.zero_lt_succ(k);

    let mc = d.imul(m, c);
    let neg_x = d.ineg(x);
    let neg_mc = d.ineg(mc);
    let neg_c = d.ineg(c);
    let m_negc = d.imul(m, neg_c);

    // neg_x = neg(mul m c), via congrArg neg on x_eq_mc.
    let step_a = d.icongr(x, mc, x_eq_mc, &|d, t| d.ineg(t));
    // neg(mul m c) = mul m (neg c), via symm(Int.mul_neg m c).
    let mul_neg_mc = d.const_app(p.mul_neg, &[m, c]);
    let step_b = d.isymm(m_negc, neg_mc, mul_neg_mc);
    let neg_x_eq_m_negc = d.itrans(neg_x, neg_mc, m_negc, step_a, step_b);

    let diff_eq = sub_add_self_left(d, a, x);
    // diff_eq : Eq(add(a, neg(xa)), neg_x)
    let sub_am = d.isub(a, xa);
    let witness_eq = d.itrans(sub_am, neg_x, m_negc, diff_eq, neg_x_eq_m_negc);

    let dvd_ty = super::dvd::idvd(d, m, sub_am);
    let pred = super::dvd::dvd_predicate(d, m, sub_am);
    let int_ty = d.int_ty();
    let one_level = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one_level]);
    let dvd_proof = d.apply(intro, &[int_ty, pred, neg_c, witness_eq]);

    let iff_ma = d.const_app(p.mod_eq_iff_dvd, &[m, xa, a, h_pos]);
    let mpr = d.const_app(p.logic.iff_mpr, &[modeq_ty, dvd_ty, iff_ma]);
    d.apply(mpr, &[dvd_proof])
}

/// `Int.modEq_add_mul_left : ∀ n a q, ModEq n (add (mul n q) a) a`.
///
/// Unconditional in `n`: `case_split` on `n` alone (`a`, `q` stay symbolic
/// throughout — only the modulus's sign matters).
///
/// - `n = ofNat 0`: `mul zero q = zero` (`Int.mul_comm` + `Int.mul_zero`),
///   then `add zero a = a` (`Int.add_comm` + `Int.add_zero`) closes by
///   `Eq.refl` after the rewrite.
/// - `n = ofNat (succ k)`: [`modeq_shift_pos`] at `x := mul n q`, `c := q`,
///   `x_eq_mc := Eq.refl`.
/// - `n = negSucc k`: [`modeq_shift_pos`] for the POSITIVE modulus
///   `m := ofNat (succ k)` at `x := mul m (neg q)`, `c := neg q` (so
///   `x_eq_mc` is again `Eq.refl`), then [`declare_modeq_neg_modulus`] to
///   cross to modulus `neg m` — which IS `negSucc k` up to defeq — followed
///   by one [`super::ops::IntDev::int_eq_rewrite`] to turn `mul m (neg q)`
///   into `mul (neg m) q` (via [`local_neg_mul`] and `Int.mul_neg`), which
///   the case-split's own goal needs literally (`mul (negSucc k) q`, not
///   `mul m (neg q)`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_add_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_mul_left, 3, &|d, v| {
        let (n, a, q) = (v[0], v[1], v[2]);
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let nn = args[0];
            let nq = d.imul(nn, q);
            let shifted = d.iadd(nq, a);
            super::modeq::imodeq(d, nn, shifted, a)
        };
        let stmt = statement(d, &[n]);
        let proof = case_split(d, &[n], &statement, &|d, branches| {
            let (n_shape, nm) = branches[0];
            match n_shape {
                Shape::OfNat => {
                    let motive = |d: &mut IntDev<'_>, x: ExprId| {
                        let ofnat_x = d.of_nat(x);
                        statement(d, &[ofnat_x])
                    };
                    let base = |d: &mut IntDev<'_>| {
                        let zero = d.zero();
                        let n0 = d.of_nat(zero);
                        let n0q = d.imul(n0, q);
                        let izero = d.izero();

                        // n0*q = izero, via Int.mul_comm then Int.mul_zero.
                        let comm = d.const_app(p.mul_comm, &[n0, q]);
                        let q_n0 = d.imul(q, n0);
                        let mz = d.const_app(p.mul_zero, &[q]);
                        let n0q_eq_zero = d.itrans(n0q, q_n0, izero, comm, mz);

                        let shifted = d.iadd(n0q, a);
                        let zero_a = d.iadd(izero, a);
                        let step1 = d.icongr(n0q, izero, n0q_eq_zero, &|d, t| d.iadd(t, a));

                        // izero + a = a, via Int.add_comm then Int.add_zero.
                        let a_zero = d.iadd(a, izero);
                        let comm2 = d.const_app(p.add_comm, &[izero, a]);
                        let az = d.const_app(p.add_zero, &[a]);
                        let step2 = d.itrans(zero_a, a_zero, a, comm2, az);

                        let (_, chained) = d.ichain(shifted, &[(zero_a, step1), (a, step2)]);
                        // chained : Eq(shifted, a) — lift into `emod(_, n0)`
                        // directly; `Int.ModEq n0 shifted a` unfolds
                        // (`Definition`, `ModEq n a b := emod a n = emod b n`)
                        // to exactly `Eq(emod shifted n0, emod a n0)`, the
                        // same idiom `declare_modeq_refl` uses.
                        d.icongr(shifted, a, chained, &|d, t| d.iemod(t, n0))
                    };
                    let step = |d: &mut IntDev<'_>, k: ExprId, _ih: ExprId| {
                        let succ_k = d.succ(k);
                        let m = d.of_nat(succ_k);
                        let x = d.imul(m, q);
                        let x_eq_mc = d.irefl(x);
                        modeq_shift_pos(d, k, a, x, q, x_eq_mc)
                    };
                    d.induct(&motive, &base, &step, nm)
                }
                Shape::NegSucc => {
                    let k = nm;
                    let succ_k = d.succ(k);
                    let m = d.of_nat(succ_k);
                    let neg_q = d.ineg(q);
                    let x_for_m = d.imul(m, neg_q);
                    let x_eq_mc = d.irefl(x_for_m);
                    let pos_proof = modeq_shift_pos(d, k, a, x_for_m, neg_q, x_eq_mc);
                    let neg_m = d.ineg(m);
                    let xa_for_m = d.iadd(x_for_m, a);
                    let neg_result = {
                        let name = p.mod_eq_neg_modulus;
                        d.const_app(name, &[m, xa_for_m, a, pos_proof])
                    };
                    // Rewrite `mul m (neg q)` into `mul (neg m) q` (defeq
                    // `mul (negSucc k) q`, which is what the branch's own
                    // goal literally names).
                    let negm_q = d.imul(neg_m, q);
                    let bridge = {
                        let mul_neg_mq = d.const_app(p.mul_neg, &[m, q]);
                        // mul m (neg q) = neg (mul m q)
                        let mq = d.imul(m, q);
                        let neg_mq = d.ineg(mq);
                        let nm_step = local_neg_mul(d, m, q);
                        // mul (neg m) q = neg (mul m q)
                        let nm_step_rev = d.isymm(negm_q, neg_mq, nm_step);
                        d.itrans(x_for_m, neg_mq, negm_q, mul_neg_mq, nm_step_rev)
                    };
                    let motive = |d: &mut IntDev<'_>, t: ExprId| {
                        let shifted = d.iadd(t, a);
                        super::modeq::imodeq(d, neg_m, shifted, a)
                    };
                    d.int_eq_rewrite(x_for_m, negm_q, bridge, neg_result, &motive)
                }
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.add_modEq_left : ∀ n a, ModEq n (add n a) a` — Mathlib's
/// `Int.add_modEq_left`. [`declare_modeq_add_mul_left`] at `q := 1`, rewritten
/// `mul n 1 -> n` via `Int.mul_one`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_add_modeq_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_mod_eq_left, 2, &|d, v| {
        let (n, a) = (v[0], v[1]);
        let na = d.iadd(n, a);
        let stmt = super::modeq::imodeq(d, n, na, a);

        let one = d.ione();
        let core = d.const_app(p.mod_eq_add_mul_left, &[n, a, one]);

        let n1 = d.imul(n, one);
        let n1_eq_n = d.const_app(p.mul_one, &[n]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let shifted = d.iadd(t, a);
            super::modeq::imodeq(d, n, shifted, a)
        };
        let proof = d.int_eq_rewrite(n1, n, n1_eq_n, core, &motive);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.add_modEq_right : ∀ n a, ModEq n (add a n) a` — Mathlib's
/// `Int.add_modEq_right`. [`declare_add_modeq_left`] rewritten via
/// `Int.add_comm`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_add_modeq_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_mod_eq_right, 2, &|d, v| {
        let (n, a) = (v[0], v[1]);
        let an = d.iadd(a, n);
        let stmt = super::modeq::imodeq(d, n, an, a);

        let na = d.iadd(n, a);
        let left = d.const_app(p.add_mod_eq_left, &[n, a]);
        let comm = d.const_app(p.add_comm, &[n, a]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| super::modeq::imodeq(d, n, t, a);
        let proof = d.int_eq_rewrite(na, an, comm, left, &motive);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.mod_modEq : ∀ a n, ModEq n (emod a n) a` — Mathlib's `Int.mod_modEq`
/// (`a % n ≡ a [ZMOD n]`). [`declare_modeq_add_mul_left`] at
/// `a := emod a n`, `q := ediv a n`, rewritten via
/// [`super::division::declare_ediv_add_emod`] and flipped with
/// `Int.ModEq.symm`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_modeq(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_mod_eq, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let r = d.iemod(a, n);
        let stmt = super::modeq::imodeq(d, n, r, a);

        let q = d.iediv(a, n);
        let core = d.const_app(p.mod_eq_add_mul_left, &[n, r, q]);
        // core : ModEq n (add (mul n q) r) r

        let nq = d.imul(n, q);
        let sum = d.iadd(nq, r);
        let ediv_add_emod = d.const_app(p.ediv_add_emod, &[a, n]);
        // ediv_add_emod : Eq(sum, a)
        let motive = |d: &mut IntDev<'_>, t: ExprId| super::modeq::imodeq(d, n, t, r);
        let flipped = d.int_eq_rewrite(sum, a, ediv_add_emod, core, &motive);
        // flipped : ModEq n a r

        let symm_name = p.mod_eq_symm;
        let proof = d.const_app(symm_name, &[n, a, r, flipped]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.modulus_modEq_zero : ∀ n, ModEq n n zero` (`n ≡ 0 [ZMOD n]`).
/// [`declare_modeq_add_mul_left`] at `a := 0`, `q := 1`, rewritten via
/// `Int.mul_one`/`Int.add_zero`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modulus_modeq_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.modulus_mod_eq_zero, 1, &|d, v| {
        let n = v[0];
        let zero = d.izero();
        let stmt = super::modeq::imodeq(d, n, n, zero);

        let one = d.ione();
        let core = d.const_app(p.mod_eq_add_mul_left, &[n, zero, one]);
        // core : ModEq n (add (mul n one) zero) zero

        let n1 = d.imul(n, one);
        let n1_eq_n = d.const_app(p.mul_one, &[n]);
        let shifted = d.iadd(n1, zero);
        let n_zero = d.iadd(n, zero);
        let step1 = d.icongr(n1, n, n1_eq_n, &|d, t| d.iadd(t, zero));

        let n_zero_eq_n = d.const_app(p.add_zero, &[n]);
        let (_, chained) = d.ichain(shifted, &[(n_zero, step1), (n, n_zero_eq_n)]);

        let motive = |d: &mut IntDev<'_>, t: ExprId| super::modeq::imodeq(d, n, t, zero);
        let proof = d.int_eq_rewrite(shifted, n, chained, core, &motive);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.modEq_sub : ∀ a b, ModEq (sub a b) a b` (`a ≡ b [ZMOD a - b]`).
/// [`declare_modeq_add_mul_left`] at `n := sub a b`, `a := b`, `q := 1`,
/// rewritten via `Int.mul_one` and [`super::modeq::cancel_neg_add`]
/// (`(a-b)+b = a`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_sub(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_sub, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let diff = d.isub(a, b);
        let stmt = super::modeq::imodeq(d, diff, a, b);

        let one = d.ione();
        let core = d.const_app(p.mod_eq_add_mul_left, &[diff, b, one]);
        // core : ModEq diff (add (mul diff one) b) b

        let diff1 = d.imul(diff, one);
        let diff1_eq_diff = d.const_app(p.mul_one, &[diff]);
        let shifted = d.iadd(diff1, b);
        let diff_b = d.iadd(diff, b);
        let step1 = d.icongr(diff1, diff, diff1_eq_diff, &|d, t| d.iadd(t, b));

        // (a-b)+b = a.
        let diff_b_eq_a = super::modeq::cancel_neg_add(d, a, b);
        let (_, chained) = d.ichain(shifted, &[(diff_b, step1), (a, diff_b_eq_a)]);

        let motive = |d: &mut IntDev<'_>, t: ExprId| super::modeq::imodeq(d, diff, t, b);
        let proof = d.int_eq_rewrite(shifted, a, chained, core, &motive);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.of_mul_right : ∀ n a b m, ModEq (n*m) a b → ModEq n a b`,
/// UNCONDITIONAL in `n` and `m`.
///
/// The mirror of [`super::modeq::declare_modeq_of_mul_left`] at the other
/// divisibility witness: `Int.dvd_mul_right n m : dvd n (n*m)` instead of
/// `Int.dvd_mul_left n m : dvd n (m*n)`. Both are the same special case of
/// [`super::modeq::declare_modeq_of_dvd`], which is already unconditional, so
/// neither needs the `natAbs` bound this module's header explains is absent.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_of_mul_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_of_mul_right, 4, &|d, v| {
        let (n, a, b, m) = (v[0], v[1], v[2], v[3]);
        let nm = d.imul(n, m);
        let modeq_nm = super::modeq::imodeq(d, nm, a, b);
        let modeq_n = super::modeq::imodeq(d, n, a, b);
        let stmt = d.arrow(modeq_nm, modeq_n);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let dvd_n_nm = d.const_app(p.dvd_mul_right, &[n, m]); // dvd n (n*m)
        let of_dvd = d.const_app(p.mod_eq_of_dvd, &[n, nm, a, b, dvd_n_nm]);
        let body = d.apply(of_dvd, &[h]);

        let proof = d.lam_fv(h_fv, modeq_nm, body);
        (stmt, proof)
    })?;
    Ok(())
}
