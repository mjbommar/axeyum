//! **Fermat's theorem on sums of two squares**, assembled by strong induction
//! over the descent shelf (W3-10, third and final slice, ADR-1650).
//!
//! ## What this module is, and what it is not
//!
//! Everything hard about Euler's descent had already landed when this module
//! was written. [`two_squares.rs`](super::two_squares) carries the algebraic
//! half (`Int.descentStep`) and the congruence half
//! (`Int.modEq_descent_cross_terms`);
//! [`order_squares.rs`](super::order_squares) carries the ordering half — the
//! centered representative, the strict decrease, the termination certificate
//! `Int.descentMultiplierBounds`, and the entry point
//! `Int.exists_small_multiple_of_sq_add_one`. ADR-1647 sized what was left as
//! four pieces, and this module is exactly those four:
//!
//! 1. [`declare_exists_next_multiplier`] — from `m·p = a²+b²` and centered
//!    `c ≡ a`, `e ≡ b (mod m)`, the norm `c²+e²` is again a multiple of `m`.
//! 2. [`declare_dvd_of_degenerate_descent`] and
//!    [`declare_not_dvd_of_nat_of_prime_of_lt`] — the `q ≠ 0` argument, split
//!    at the point where primality enters.
//! 3. [`declare_exists_sum_of_two_squares_of_multiple`] — the descent itself,
//!    by `Nat.strongInduction` on the multiplier.
//! 4. [`declare_fermat_two_squares`] — the theorem.
//!
//! ## Why the descent is indexed by a `Nat`, not by an `Int`
//!
//! The multiplier is an `Int`, but the recursion has to be well-founded, and
//! the only well-founded relation this kernel has a named recursor for is
//! `Nat.lt` (`Nat.strongInduction`, ADR-1614). Two spellings were available:
//! quantify over an `Int m` and carry a bridge hypothesis `natAbs m = n`, or
//! quantify over `Int.ofNat n` directly. **This module takes the second.**
//!
//! It is the cheaper one, and not marginally. With `m := ofNat n` every bound
//! the descent states about the multiplier is a bound between two `ofNat`s,
//! and `Int.le`/`Int.lt` at two `ofNat`s is *definitionally* the corresponding
//! `Nat` relation ([`super::order_coercion`]) — so `0 < m`, `m < p` and
//! `1 < m` all come from the `Nat` hypotheses by
//! [`declare_lt_of_nat_of_lt`], whose proof is the hypothesis itself. The
//! bridge-hypothesis spelling would have needed each of those three
//! transported through `of_nat_nat_abs_of_nonneg` instead, and would have had
//! to re-establish `natAbs (ofNat n) = n` at the recursive call anyway.
//!
//! The one place the *other* direction is needed is the recursive call, where
//! the new multiplier `q` arrives as an `Int` with `0 ≤ q < m`; there
//! `Int.of_nat_nat_abs_of_nonneg` names `natAbs q` and
//! `Int.lt_of_ofNat_lt_ofNat` drops the two bounds back into `Nat`. That is
//! one transport, once, rather than three at every level.
//!
//! ## Where primality is consumed, and where it is not
//!
//! Exactly one step needs `p` prime:
//! [`declare_not_dvd_of_nat_of_prime_of_lt`]. Everything else — the
//! representative, the bounds, the composition identity, the entry point —
//! needs only `0 < m < p`. That is why the two halves of the `q ≠ 0` argument
//! are separate declarations: [`declare_dvd_of_degenerate_descent`] is a pure
//! statement about ℤ (a vanishing new multiplier forces `m ∣ p`) with no
//! primality anywhere, and the contradiction lives alone in the lemma that
//! reads the primality condition.
//!
//! The primality condition is the inline one this prelude uses everywhere
//! (`super::wilson::prime_condition`): `2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`.
//! There is no `Prime` name over either carrier here, and
//! `Int.firstSupplementaryLawResidue` states its hypothesis in exactly this
//! shape, so the theorem composes with the residue half without a translation.
//!
//! ## What is deliberately NOT declared here
//!
//! `Nat.sum_four_squares`, `Nat.Prime.sum_four_squares`,
//! `Int.lt_of_sum_four_squares_eq_mul`, `Int.exists_least_of_bdd` and
//! `Int.exists_greatest_of_bdd` are rows of the **held-out**
//! `descent-and-well-ordering` family; `Nat.sq_add_sq_mul` and
//! `Int.sq_ne_two_mod_four` are rows of the held-out
//! `power-and-square-decompositions` family
//! (`artifacts/autogenesis/nursery-v2-extension.json` carries the partition,
//! and it — not any fact file — is the split authority). **None of them is
//! declared, and no lemma here is stated in their shape.** The descent below
//! is a statement about one specific predicate over ℤ, not a well-ordering
//! principle for an arbitrary `P : ℤ → Prop`; Mathlib's `Nat.Prime.sq_add_sq`,
//! which IS this theorem, is in neither family.

use super::euler::{int_exists_elim, int_exists_intro};
use super::ops::IntDev;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ============================================================================
// local plumbing
// ============================================================================

/// `fun (h : ty) => body(h)`.
fn with_hyp(
    d: &mut IntDev<'_>,
    ty: ExprId,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fv = d.fresh_fvar();
    let h = d.kernel().fvar(fv);
    let inner = body(d, h);
    d.lam_fv(fv, ty, inner)
}

/// `And.intro left right hl hr : And left right`.
fn and_intro(d: &mut IntDev<'_>, left: ExprId, right: ExprId, hl: ExprId, hr: ExprId) -> ExprId {
    let name = d.int().logic.and_intro;
    d.const_app(name, &[left, right, hl, hr])
}

/// `Iff.mpr left right h_iff h_right : left`.
fn iff_mpr(d: &mut IntDev<'_>, left: ExprId, right: ExprId, h_iff: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.iff_mpr;
    d.const_app(name, &[left, right, h_iff, h])
}

/// `add (mul c c) (mul e e)` — the descent's measure, spelled the same way
/// `order_squares.rs` spells it so the two compose without a rewrite.
fn measure(d: &mut IntDev<'_>, c: ExprId, e: ExprId) -> ExprId {
    let cc = d.imul(c, c);
    let ee = d.imul(e, e);
    d.iadd(cc, ee)
}

/// `fun (b : Int) => Eq Int lhs (add (mul a a) (mul b b))`.
fn norm_inner(d: &mut IntDev<'_>, lhs: ExprId, a: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let body = {
        let sum = measure(d, a, b);
        d.ieq(lhs, sum)
    };
    d.lam_fv(b_fv, int_ty, body)
}

/// `fun (a : Int) => ∃ b, Eq Int lhs (add (mul a a) (mul b b))` — the shape
/// the descent carries as its hypothesis at every level.
fn norm_outer(d: &mut IntDev<'_>, lhs: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let inner = norm_inner(d, lhs, a);
    let body = super::two_squares::int_exists(d, inner);
    d.lam_fv(a_fv, int_ty, body)
}

/// `∃ a, ∃ b, Eq Int lhs (add (mul a a) (mul b b))`.
fn exists_norm(d: &mut IntDev<'_>, lhs: ExprId) -> ExprId {
    let outer = norm_outer(d, lhs);
    super::two_squares::int_exists(d, outer)
}

/// `fun (q : Int) => Eq Int (mul m q) (add (mul c c) (mul e e))` — the body of
/// [`declare_exists_next_multiplier`]'s existential.
fn multiplier_predicate(d: &mut IntDev<'_>, m: ExprId, c: ExprId, e: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let body = {
        let mq = d.imul(m, q);
        let s = measure(d, c, e);
        d.ieq(mq, s)
    };
    d.lam_fv(q_fv, int_ty, body)
}

// ============================================================================
// divisibility from a vanishing congruence
// ============================================================================

/// `Int.dvd_zero : ∀ a, dvd a zero`.
///
/// The witness is `zero` and the equation is `Int.mul_zero` read backwards.
/// `Nat.dvd_zero` exists; the `Int` sibling did not (`shape_search --ns Int
/// --concl Int.dvd --arity 1` finds only `Int.dvd_refl`).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_dvd_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_zero, 1, &|d, v| {
        let a = v[0];
        let zero = d.izero();
        let stmt = super::dvd::idvd(d, a, zero);
        let a_zero = d.imul(a, zero);
        let forward = d.const_app(p.mul_zero, &[a]);
        let equation = d.isymm(a_zero, zero, forward);
        let predicate = super::dvd::dvd_predicate(d, a, zero);
        let proof = int_exists_intro(d, predicate, zero, equation);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.dvd_of_modEq_zero : ∀ n a, ModEq n a zero → dvd n a`.
///
/// Through `Int.ModEq.dvd_iff` rather than `Int.modEq_iff_dvd`: the latter is
/// scoped to `0 < n` and produces `n ∣ (b − a)`, which would need a
/// `sub_zero` this prelude does not have and which `ring::int` declines (a
/// normal form with a trailing zero numeral — ADR-1633). `dvd_iff` is
/// unconditional in the modulus and lands on `n ∣ a` directly.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_dvd_of_modeq_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_of_mod_eq_zero, 2, &|d, v| {
        let (n, a) = (v[0], v[1]);
        let zero = d.izero();
        let hyp = super::modeq::imodeq(d, n, a, zero);
        let concl = super::dvd::idvd(d, n, a);
        let stmt = d.arrow(hyp, concl);

        let proof = with_hyp(d, hyp, &|d, h| {
            let zero = d.izero();
            let dvd_na = super::dvd::idvd(d, n, a);
            let dvd_n0 = super::dvd::idvd(d, n, zero);
            let bridge = d.const_app(p.mod_eq_dvd_iff, &[n, a, zero, h]);
            let base = d.const_app(p.dvd_zero, &[n]);
            iff_mpr(d, dvd_na, dvd_n0, bridge, base)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.mul_modEq_zero : ∀ m x, ModEq m (mul m x) zero`.
///
/// `Int.modulus_modEq_zero` says `m ≡ 0`; multiplying both sides by `x`
/// through the unconditional `Int.mod_eq_mul_general` gives `m·x ≡ 0·x`, and
/// `0·x` collapses through `mul_comm`/`mul_zero` (this prelude has no
/// `Int.zero_mul`).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_mul_modeq_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mul_mod_eq_zero, 2, &|d, v| {
        let (m, x) = (v[0], v[1]);
        let zero = d.izero();
        let mx = d.imul(m, x);
        let stmt = super::modeq::imodeq(d, m, mx, zero);

        let modulus = d.const_app(p.modulus_mod_eq_zero, &[m]);
        let same = d.const_app(p.mod_eq_refl, &[m, x]);
        let scaled = d.const_app(p.mod_eq_mul_general, &[m, m, zero, x, x, modulus, same]);

        // `0*x = x*0 = 0`.
        let zero_x = d.imul(zero, x);
        let x_zero = d.imul(x, zero);
        let commute = d.const_app(p.mul_comm, &[zero, x]);
        let collapse = d.const_app(p.mul_zero, &[x]);
        let vanishes = d.itrans(zero_x, x_zero, zero, commute, collapse);
        let proof = d.int_eq_rewrite(zero_x, zero, vanishes, scaled, &|d, z| {
            let mx = d.imul(m, x);
            super::modeq::imodeq(d, m, mx, z)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.sq_add_sq_modEq_of_modEq : ∀ m a b c e, ModEq m c a → ModEq m e b →`
/// `  ModEq m (add (mul c c) (mul e e)) (add (mul a a) (mul b b))`.
///
/// Two applications of the unconditional `Int.mod_eq_mul_general` (the
/// modulus-positivity-free two-sided multiplicative congruence) and one of
/// `Int.mod_eq_add`. `Int.ModEq.mul_left`, which
/// `Int.modEq_descent_cross_terms` uses, would have dragged a `0 < m`
/// hypothesis in for no reason.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sq_add_sq_modeq_of_modeq(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.sq_add_sq_mod_eq_of_mod_eq, 5, &|d, v| {
        let (m, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let hc_ty = super::modeq::imodeq(d, m, c, a);
        let he_ty = super::modeq::imodeq(d, m, e, b);
        let source = measure(d, c, e);
        let target = measure(d, a, b);
        let concl = super::modeq::imodeq(d, m, source, target);
        let stmt = {
            let tail = d.arrow(he_ty, concl);
            d.arrow(hc_ty, tail)
        };

        let proof = with_hyp(d, hc_ty, &|d, hc| {
            let he_ty = super::modeq::imodeq(d, m, e, b);
            with_hyp(d, he_ty, &|d, he| {
                let cc = d.imul(c, c);
                let aa = d.imul(a, a);
                let ee = d.imul(e, e);
                let bb = d.imul(b, b);
                let first = d.const_app(p.mod_eq_mul_general, &[m, c, a, c, a, hc, hc]);
                let second = d.const_app(p.mod_eq_mul_general, &[m, e, b, e, b, he, he]);
                d.const_app(p.mod_eq_add, &[m, cc, aa, ee, bb, first, second])
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.exists_next_multiplier : ∀ m p a b c e,`
/// `  Eq Int (mul m p) (add (mul a a) (mul b b)) → ModEq m c a → ModEq m e b →`
/// `  ∃ q, Eq Int (mul m q) (add (mul c c) (mul e e))`
/// — **the first of ADR-1647's four remaining pieces**: the descent's next
/// multiplier exists.
///
/// `c² + e² ≡ a² + b² = m·p ≡ 0 (mod m)`, so `m ∣ c² + e²`, and `Int.dvd`'s
/// own existential IS the `q`. Positivity of `m` is not needed anywhere on
/// this leg — every congruence used is unconditional in the modulus — so it is
/// not a hypothesis; the caller has `0 < m` in hand for
/// `Int.descentMultiplierBounds` and does not have to thread it through here.
///
/// The conclusion is stated as `m·q = c²+e²` rather than `Int.dvd`'s own
/// `c²+e² = m·q` so that it matches `Int.descentMultiplierBounds`'s and
/// `Int.descentStep`'s second hypothesis **verbatim**; the `symm` happens once,
/// here, instead of at both call sites.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_exists_next_multiplier(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.exists_next_multiplier, 6, &|d, v| {
        let (m, pp, a, b) = (v[0], v[1], v[2], v[3]);
        let (c, e) = (v[4], v[5]);
        let mp = d.imul(m, pp);
        let norm = measure(d, a, b);
        let hfact_ty = d.ieq(mp, norm);
        let hc_ty = super::modeq::imodeq(d, m, c, a);
        let he_ty = super::modeq::imodeq(d, m, e, b);
        let predicate = multiplier_predicate(d, m, c, e);
        let concl = super::two_squares::int_exists(d, predicate);
        let stmt = {
            let t3 = d.arrow(he_ty, concl);
            let t2 = d.arrow(hc_ty, t3);
            d.arrow(hfact_ty, t2)
        };

        let proof = with_hyp(d, hfact_ty, &|d, hfact| {
            let hc_ty = super::modeq::imodeq(d, m, c, a);
            with_hyp(d, hc_ty, &|d, hc| {
                let he_ty = super::modeq::imodeq(d, m, e, b);
                with_hyp(d, he_ty, &|d, he| {
                    let zero = d.izero();
                    let source = measure(d, c, e);
                    let norm = measure(d, a, b);
                    let mp = d.imul(m, pp);

                    // `c²+e² ≡ a²+b²`.
                    let congruent =
                        d.const_app(p.sq_add_sq_mod_eq_of_mod_eq, &[m, a, b, c, e, hc, he]);
                    // `a²+b² = m·p ≡ 0`.
                    let multiple = d.const_app(p.mul_mod_eq_zero, &[m, pp]);
                    let vanishes = d.int_eq_rewrite(mp, norm, hfact, multiple, &|d, z| {
                        let zero = d.izero();
                        super::modeq::imodeq(d, m, z, zero)
                    });
                    let chained = d.const_app(
                        p.mod_eq_trans,
                        &[m, source, norm, zero, congruent, vanishes],
                    );
                    let divides = d.const_app(p.dvd_of_mod_eq_zero, &[m, source, chained]);

                    // Turn `Int.dvd`'s `c²+e² = m·q` into `m·q = c²+e²`.
                    let dvd_pred = super::dvd::dvd_predicate(d, m, source);
                    let predicate = multiplier_predicate(d, m, c, e);
                    let target = super::two_squares::int_exists(d, predicate);
                    let int_ty = d.int_ty();
                    let minor = {
                        let q_fv = d.fresh_fvar();
                        let q = d.kernel().fvar(q_fv);
                        let mq = d.imul(m, q);
                        let heq_ty = d.ieq(source, mq);
                        let body = with_hyp(d, heq_ty, &|d, heq| {
                            let mq = d.imul(m, q);
                            let source = measure(d, c, e);
                            let flipped = d.isymm(source, mq, heq);
                            let predicate = multiplier_predicate(d, m, c, e);
                            int_exists_intro(d, predicate, q, flipped)
                        });
                        d.lam_fv(q_fv, int_ty, body)
                    };
                    int_exists_elim(d, dvd_pred, target, divides, minor)
                })
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// the degenerate branch: a vanishing multiplier forces `m ∣ p`
// ============================================================================

/// `Int.sq_mul_add_sq_mul : ∀ m u v,`
/// `  Eq Int (add (mul (mul m u) (mul m u)) (mul (mul m v) (mul m v)))`
/// `         (mul m (mul m (add (mul u u) (mul v v))))`. `ring::int`.
///
/// The factor `m²` is spelled `mul m (mul m …)` rather than
/// `mul (mul m m) …` because the cancellation that consumes it,
/// `Int.mul_left_cancel_of_ne_zero`, cancels ONE factor at a time and takes
/// `m ≠ 0` — not `m² ≠ 0`, which would have needed `Int.mul_ne_zero` first.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the emitted term does not check, or
/// `UnknownConst` if the ring producer declined.
fn declare_sq_mul_add_sq_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.sq_mul_add_sq_mul, 3, &|d, v| {
        let (m, u, w) = (v[0], v[1], v[2]);
        let mu = d.imul(m, u);
        let mw = d.imul(m, w);
        let lhs = measure(d, mu, mw);
        let inner = measure(d, u, w);
        let scaled = d.imul(m, inner);
        let rhs = d.imul(m, scaled);
        d.ieq(lhs, rhs)
    })?;
    Ok(())
}

/// `Int.dvd_of_degenerate_descent : ∀ m p a b c e, Not (Eq Int m zero) →`
/// `  Eq Int (mul m p) (add (mul a a) (mul b b)) → ModEq m c a → ModEq m e b →`
/// `  Eq Int (add (mul c c) (mul e e)) zero → dvd m p`
/// — **the second of ADR-1647's four pieces**, its primality-free half.
///
/// If the new multiplier vanishes then so does the measure, and
/// `Int.eq_zero_of_sq_add_sq_eq_zero` squeezes both representatives to zero.
/// A representative congruent to `a` that is itself `0` says `m ∣ a`; the same
/// for `b`; so `m·p = m²(u²+v²)` and one cancellation gives `m ∣ p`.
///
/// **No primality anywhere.** This is a true statement about any nonzero `m`,
/// and separating it from the contradiction is what keeps
/// [`declare_not_dvd_of_nat_of_prime_of_lt`] the single place primality is
/// consumed.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_dvd_of_degenerate_descent(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_of_degenerate_descent, 6, &|d, v| {
        let (m, pp, a, b) = (v[0], v[1], v[2], v[3]);
        let (c, e) = (v[4], v[5]);
        let zero = d.izero();
        let m_zero = d.ieq(m, zero);
        let hm_ty = d.not(m_zero);
        let mp = d.imul(m, pp);
        let norm = measure(d, a, b);
        let hfact_ty = d.ieq(mp, norm);
        let hc_ty = super::modeq::imodeq(d, m, c, a);
        let he_ty = super::modeq::imodeq(d, m, e, b);
        let source = measure(d, c, e);
        let hz_ty = d.ieq(source, zero);
        let concl = super::dvd::idvd(d, m, pp);
        let stmt = {
            let t5 = d.arrow(hz_ty, concl);
            let t4 = d.arrow(he_ty, t5);
            let t3 = d.arrow(hc_ty, t4);
            let t2 = d.arrow(hfact_ty, t3);
            d.arrow(hm_ty, t2)
        };

        let proof = with_hyp(d, hm_ty, &|d, hm| {
            let mp = d.imul(m, pp);
            let norm = measure(d, a, b);
            let hfact_ty = d.ieq(mp, norm);
            with_hyp(d, hfact_ty, &|d, hfact| {
                let hc_ty = super::modeq::imodeq(d, m, c, a);
                with_hyp(d, hc_ty, &|d, hc| {
                    let he_ty = super::modeq::imodeq(d, m, e, b);
                    with_hyp(d, he_ty, &|d, he| {
                        let zero = d.izero();
                        let source = measure(d, c, e);
                        let hz_ty = d.ieq(source, zero);
                        with_hyp(d, hz_ty, &|d, hz| {
                            degenerate_body(d, p, m, pp, a, b, c, e, hm, hfact, hc, he, hz)
                        })
                    })
                })
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// The body of [`declare_dvd_of_degenerate_descent`] once every hypothesis is
/// named. Split out because it is five binders deep before the mathematics
/// starts and clippy's argument budget is the lesser evil.
#[allow(clippy::too_many_arguments)]
fn degenerate_body(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    m: ExprId,
    pp: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
    hm: ExprId,
    hfact: ExprId,
    hc: ExprId,
    he: ExprId,
    hz: ExprId,
) -> ExprId {
    let zero = d.izero();

    // `c = 0` and `e = 0`.
    let both = d.const_app(p.eq_zero_of_sq_add_sq_eq_zero, &[c, e, hz]);
    let c_zero = d.ieq(c, zero);
    let e_zero = d.ieq(e, zero);
    let hc0 = d.and_left(c_zero, e_zero, both);
    let he0 = d.and_right(c_zero, e_zero, both);

    // `m ∣ a` and `m ∣ b`.
    let hda = dvd_from_vanishing_representative(d, p, m, a, c, hc, hc0);
    let hdb = dvd_from_vanishing_representative(d, p, m, b, e, he, he0);

    // Open both witnesses and finish.
    let target = super::dvd::idvd(d, m, pp);
    let pred_a = super::dvd::dvd_predicate(d, m, a);
    let int_ty = d.int_ty();
    let minor_a = {
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let mu = d.imul(m, u);
        let ha_ty = d.ieq(a, mu);
        let body = with_hyp(d, ha_ty, &|d, ha| {
            let pred_b = super::dvd::dvd_predicate(d, m, b);
            let target = super::dvd::idvd(d, m, pp);
            let minor_b = {
                let w_fv = d.fresh_fvar();
                let w = d.kernel().fvar(w_fv);
                let mw = d.imul(m, w);
                let hb_ty = d.ieq(b, mw);
                let inner = with_hyp(d, hb_ty, &|d, hb| {
                    degenerate_cancel(d, p, m, pp, a, b, u, w, hm, hfact, ha, hb)
                });
                d.lam_fv(w_fv, int_ty, inner)
            };
            int_exists_elim(d, pred_b, target, hdb, minor_b)
        });
        d.lam_fv(u_fv, int_ty, body)
    };
    int_exists_elim(d, pred_a, target, hda, minor_a)
}

/// From `hmod : ModEq m c a` and `hc0 : c = 0`, derive `m ∣ a`.
fn dvd_from_vanishing_representative(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    m: ExprId,
    a: ExprId,
    c: ExprId,
    hmod: ExprId,
    hc0: ExprId,
) -> ExprId {
    let zero = d.izero();
    let shifted = d.int_eq_rewrite(c, zero, hc0, hmod, &|d, z| super::modeq::imodeq(d, m, z, a));
    let flipped = d.const_app(p.mod_eq_symm, &[m, zero, a, shifted]);
    d.const_app(p.dvd_of_mod_eq_zero, &[m, a, flipped])
}

/// The cancellation at the bottom of [`degenerate_body`]: from `m·p = a²+b²`,
/// `a = m·u` and `b = m·w`, conclude `m ∣ p`.
#[allow(clippy::too_many_arguments)]
fn degenerate_cancel(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    m: ExprId,
    pp: ExprId,
    a: ExprId,
    b: ExprId,
    u: ExprId,
    w: ExprId,
    hm: ExprId,
    hfact: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let mp = d.imul(m, pp);
    let mu = d.imul(m, u);
    let mw = d.imul(m, w);

    // `m·p = a²+b² = (m·u)² + b² = (m·u)² + (m·w)²`.
    let step_a = d.int_eq_rewrite(a, mu, ha, hfact, &|d, z| {
        let mp = d.imul(m, pp);
        let sum = measure(d, z, b);
        d.ieq(mp, sum)
    });
    let step_b = d.int_eq_rewrite(b, mw, hb, step_a, &|d, z| {
        let mp = d.imul(m, pp);
        let mu = d.imul(m, u);
        let sum = measure(d, mu, z);
        d.ieq(mp, sum)
    });

    // `= m·(m·(u²+w²))`.
    let scaled = measure(d, mu, mw);
    let inner = measure(d, u, w);
    let once = d.imul(m, inner);
    let twice = d.imul(m, once);
    let identity = d.const_app(p.sq_mul_add_sq_mul, &[m, u, w]);
    let cancellable = d.itrans(mp, scaled, twice, step_b, identity);

    let quotient = d.const_app(
        p.mul_left_cancel_of_ne_zero,
        &[m, pp, once, hm, cancellable],
    );
    let predicate = super::dvd::dvd_predicate(d, m, pp);
    int_exists_intro(d, predicate, inner, quotient)
}

// ============================================================================
// the coercion bridges
// ============================================================================

/// `Int.lt_ofNat_of_lt : ∀ (a b : Nat), Nat.lt a b → lt (ofNat a) (ofNat b)`.
///
/// The `Nat → Int` direction of `Int.lt_of_ofNat_lt_ofNat`, whose absence
/// `shape_search --ns Int --concl Int.lt --hyp Nat.lt` confirms. `Int.lt` at
/// two `ofNat`s reduces straight to the `Nat` comparison, so — exactly as in
/// [`super::order_coercion`] — the proof is the hypothesis itself.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_lt_of_nat_of_lt(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let lhs = d.of_nat(a);
    let rhs = d.of_nat(b);
    let hyp_ty = d.lt(a, b);
    let concl = d.ilt(lhs, rhs);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let inner_ty = d.arrow(hyp_ty, concl);
    let inner_value = d.lam_fv(h_fv, hyp_ty, h);
    let ty = {
        let with_b = d.pi_fv(b_fv, nat, inner_ty);
        d.pi_fv(a_fv, nat, with_b)
    };
    let value = {
        let with_b = d.lam_fv(b_fv, nat, inner_value);
        d.lam_fv(a_fv, nat, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lt_of_nat_of_lt,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

/// `Int.le_two_of_nat_le_two : ∀ (k : Nat), Nat.le 2 k → le (add one one) (ofNat k)`.
///
/// `Int.exists_small_multiple_of_sq_add_one` states its width hypothesis as
/// `1 + 1 ≤ p`, and a primality condition's first conjunct is `2 ≤ p` over
/// `Nat`. `Int.one` is `ofNat 1` and `Int.add` on two `ofNat`s is `ofNat` of
/// the `Nat` sum, so the two are the same proposition and this is again the
/// hypothesis itself — but stated once, by name, so that a change to either
/// spelling fails HERE rather than inside Fermat's proof term.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_le_two_of_nat_le_two(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let two_nat = d.num(2);
    let hyp_ty = d.le(two_nat, k);
    let one = d.ione();
    let two_int = d.iadd(one, one);
    let coerced = d.of_nat(k);
    let concl = d.ile(two_int, coerced);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let inner_ty = d.arrow(hyp_ty, concl);
    let inner_value = d.lam_fv(h_fv, hyp_ty, h);
    let ty = d.pi_fv(k_fv, nat, inner_ty);
    let value = d.lam_fv(k_fv, nat, inner_value);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_two_of_nat_le_two,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

// ============================================================================
// the only step that consumes primality
// ============================================================================

/// `Int.not_dvd_ofNat_of_prime_of_lt : ∀ (p n : Nat), <p prime> →`
/// `  Nat.lt 1 n → Nat.lt n p → Not (dvd (ofNat n) (ofNat p))`
/// — **the second of ADR-1647's four pieces**, its primality half, and the
/// ONLY declaration in this module that reads a primality condition.
///
/// `Int.nat_abs_dvd_nat_abs_of_dvd` drops the divisibility to `Nat`, where
/// `natAbs (ofNat n)` iota-reduces to `n`; the primality condition then leaves
/// `n = 1` or `n = p`, and each contradicts one of the two strict bounds
/// through `Nat.lt_irrefl`.
///
/// The primality condition is `super::wilson::prime_condition`'s inline shape
/// — the one `Int.firstSupplementaryLawResidue` also takes — because this
/// prelude has no `Prime` predicate over either carrier.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_not_dvd_of_nat_of_prime_of_lt(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.not_dvd_of_nat_of_prime_of_lt, 2, &|d, v| {
        let (pn, n) = (v[0], v[1]);
        let one_nat = d.num(1);
        let prime_ty = super::wilson::prime_condition(d, pn);
        let hgt_ty = d.lt(one_nat, n);
        let hlt_ty = d.lt(n, pn);
        let coerced_n = d.of_nat(n);
        let coerced_p = d.of_nat(pn);
        let dvd_ty = super::dvd::idvd(d, coerced_n, coerced_p);
        let concl = d.not(dvd_ty);
        let stmt = {
            let t3 = d.arrow(hlt_ty, concl);
            let t2 = d.arrow(hgt_ty, t3);
            d.arrow(prime_ty, t2)
        };

        let proof = with_hyp(d, prime_ty, &|d, hprime| {
            let one_nat = d.num(1);
            let hgt_ty = d.lt(one_nat, n);
            with_hyp(d, hgt_ty, &|d, hgt| {
                let hlt_ty = d.lt(n, pn);
                with_hyp(d, hlt_ty, &|d, hlt| {
                    let coerced_n = d.of_nat(n);
                    let coerced_p = d.of_nat(pn);
                    let dvd_ty = super::dvd::idvd(d, coerced_n, coerced_p);
                    with_hyp(d, dvd_ty, &|d, hdvd| {
                        prime_contradiction(d, p, pn, n, hprime, hgt, hlt, hdvd)
                    })
                })
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// The body of [`declare_not_dvd_of_nat_of_prime_of_lt`]: `False`.
#[allow(clippy::too_many_arguments)]
fn prime_contradiction(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    pn: ExprId,
    n: ExprId,
    hprime: ExprId,
    hgt: ExprId,
    hlt: ExprId,
    hdvd: ExprId,
) -> ExprId {
    let np = d.prelude();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let coerced_n = d.of_nat(n);
    let coerced_p = d.of_nat(pn);

    // `natAbs (ofNat n) ∣ natAbs (ofNat p)`, which is `n ∣ p` after iota.
    let dropped = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[coerced_n, coerced_p, hdvd]);

    // The primality condition's divisor clause, at `n`.
    let two_le = d.le(two_nat, pn);
    let divisor_clause = {
        let nat = d.nat_ty();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hyp = d.dvd(x, pn);
        let is_one = d.eq(x, one_nat);
        let is_whole = d.eq(x, pn);
        let disjunction = d.or(is_one, is_whole);
        let inner = d.arrow(hyp, disjunction);
        d.pi_fv(x_fv, nat, inner)
    };
    let clause = d.and_right(two_le, divisor_clause, hprime);
    let split = d.apply(clause, &[n, dropped]);

    let is_one = d.eq(n, one_nat);
    let is_whole = d.eq(n, pn);
    let false_ty = d.false_ty();
    d.or_elim(
        is_one,
        is_whole,
        false_ty,
        split,
        &|d, heq| {
            // `n = 1` contradicts `1 < n`.
            let one_nat = d.num(1);
            let degenerate = d.nat_rewrite(n, one_nat, heq, hgt, &|d, z| {
                let one_nat = d.num(1);
                d.lt(one_nat, z)
            });
            let irrefl = d.const_app(np.lt_irrefl, &[one_nat]);
            d.apply(irrefl, &[degenerate])
        },
        &|d, heq| {
            // `n = p` contradicts `n < p`.
            let degenerate = d.nat_rewrite(n, pn, heq, hlt, &|d, z| d.lt(z, pn));
            let irrefl = d.const_app(np.lt_irrefl, &[pn]);
            d.apply(irrefl, &[degenerate])
        },
    )
}

// ============================================================================
// registration
// ============================================================================

/// Declare every theorem in this module.
///
/// # Errors
///
/// Returns the trusted gate's rejection, or `UnknownConst` if a ring-producer
/// search declined.
pub(super) fn declare_fermat_two_squares_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    // Declaration ORDER is load-bearing: `dvd_of_modEq_zero` consumes
    // `dvd_zero`; `exists_next_multiplier` consumes `mul_modEq_zero`,
    // `sq_add_sq_modEq_of_modEq` and `dvd_of_modEq_zero`;
    // `dvd_of_degenerate_descent` consumes `sq_mul_add_sq_mul` and
    // `dvd_of_modEq_zero`.
    declare_dvd_zero(d)?;
    declare_dvd_of_modeq_zero(d)?;
    declare_mul_modeq_zero(d)?;
    declare_sq_add_sq_modeq_of_modeq(d)?;
    declare_exists_next_multiplier(d)?;
    declare_sq_mul_add_sq_mul(d)?;
    declare_dvd_of_degenerate_descent(d)?;
    declare_lt_of_nat_of_lt(d)?;
    declare_le_two_of_nat_le_two(d)?;
    declare_not_dvd_of_nat_of_prime_of_lt(d)?;
    Ok(())
}
