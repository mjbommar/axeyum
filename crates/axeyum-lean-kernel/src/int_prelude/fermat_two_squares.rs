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

/// The two conjuncts of `super::wilson::prime_condition` at `pn`, separately:
/// `Nat.le 2 pn` and `∀ x, x ∣ pn → x = 1 ∨ x = pn`.
///
/// `prime_condition` returns only the `And`, and both halves are consumed
/// individually here — the width bound by [`declare_fermat_two_squares`] and
/// the divisor clause by [`declare_not_dvd_of_nat_of_prime_of_lt`]. Building
/// them in ONE place means the two `And.left`/`And.right` projections cannot
/// disagree with each other about the shape.
fn prime_parts(d: &mut IntDev<'_>, pn: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let two_le = d.le(two_nat, pn);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hyp = d.dvd(x, pn);
    let is_one = d.eq(x, one_nat);
    let is_whole = d.eq(x, pn);
    let disjunction = d.or(is_one, is_whole);
    let inner = d.arrow(hyp, disjunction);
    let clause = d.pi_fv(x_fv, nat, inner);
    (two_le, clause)
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
    let coerced_n = d.of_nat(n);
    let coerced_p = d.of_nat(pn);

    // `natAbs (ofNat n) ∣ natAbs (ofNat p)`, which is `n ∣ p` after iota.
    let dropped = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[coerced_n, coerced_p, hdvd]);

    // The primality condition's divisor clause, at `n`.
    let (two_le, divisor_clause) = prime_parts(d, pn);
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
// the descent
// ============================================================================

/// `And (ModEq m c a) (And (le (neg m) (add c c)) (le (add c c) m))` — the
/// body of `Int.exists_centered_representative`'s existential.
///
/// Rebuilt here rather than widening `order_squares.rs`'s own private copy to
/// `pub(super)`: that file is one another lane may be editing, and this is
/// eight lines — the same reason `two_squares.rs` re-derives `int_exists`
/// rather than importing `euler.rs`'s. `centered_predicate` IS re-used (it is
/// already `pub(super)`), so the two cannot silently drift apart: the
/// `Exists.rec` below would stop type-checking.
fn centered_body(d: &mut IntDev<'_>, a: ExprId, m: ExprId, c: ExprId) -> ExprId {
    let congruent = super::two_squares::imodeq(d, m, c, a);
    let double = d.iadd(c, c);
    let neg_m = d.ineg(m);
    let low = d.ile(neg_m, double);
    let high = d.ile(double, m);
    let bounds = d.and(low, high);
    d.and(congruent, bounds)
}

/// `Nat.lt 0 n → Nat.lt n p → (∃ a b, (ofNat n)·(ofNat p) = a²+b²) →`
/// `  IsSumOfTwoSquares (ofNat p)` — the motive
/// [`declare_exists_sum_of_two_squares_of_multiple`] runs
/// `Nat.strongInduction` at.
///
/// Every bound in it is between two `Nat`s and the multiplier appears only as
/// `Int.ofNat n`; see this module's header for why that spelling and not a
/// `natAbs m = n` bridge hypothesis.
fn descent_motive(d: &mut IntDev<'_>, pn: ExprId, n: ExprId) -> ExprId {
    let zero_nat = d.num(0);
    let positive = d.lt(zero_nat, n);
    let below = d.lt(n, pn);
    let m = d.of_nat(n);
    let pp = d.of_nat(pn);
    let mp = d.imul(m, pp);
    let hypothesis = exists_norm(d, mp);
    let concl = super::two_squares::is_sum_of_two_squares(d, pp);
    let tail = d.arrow(hypothesis, concl);
    let middle = d.arrow(below, tail);
    d.arrow(positive, middle)
}

/// Everything the descent's inductive case holds once both centered
/// representatives have been named — bundled so the functions below take one
/// argument instead of sixteen.
#[derive(Clone, Copy)]
struct Descent {
    /// The prime, as a `Nat`.
    pn: ExprId,
    /// The current multiplier's magnitude, as a `Nat`.
    n: ExprId,
    /// The primality condition, `super::wilson::prime_condition` at `pn`.
    hprime: ExprId,
    /// `∀ k, Nat.lt k n → <motive k>` — `Nat.strongInduction`'s recursive
    /// argument.
    ih: ExprId,
    /// `Nat.lt n pn`.
    hbelow: ExprId,
    /// `Nat.lt 1 n` — the inductive branch's discriminator.
    hgt: ExprId,
    /// `Int.lt zero (ofNat n)`.
    hm_pos: ExprId,
    /// `Not (Eq Int (ofNat n) zero)`.
    hm_ne: ExprId,
    /// The two squares of the current multiple.
    a: ExprId,
    /// The second square of the current multiple.
    b: ExprId,
    /// The centered representative of `a` modulo `ofNat n`.
    c: ExprId,
    /// The centered representative of `b` modulo `ofNat n`.
    e: ExprId,
    /// `Eq Int (mul (ofNat n) (ofNat pn)) (add (mul a a) (mul b b))`.
    hfact: ExprId,
    /// `ModEq (ofNat n) c a`.
    hca: ExprId,
    /// `ModEq (ofNat n) e b`.
    heb: ExprId,
    /// The four band hypotheses, in `Int.descentMultiplierBounds`'s order:
    /// `−m ≤ c+c`, `c+c ≤ m`, `−m ≤ e+e`, `e+e ≤ m`.
    bands: [ExprId; 4],
}

/// The base case `n = 1`: the multiple IS the prime, so its two squares are
/// the prime's.
fn descent_base_case(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    pn: ExprId,
    n: ExprId,
    hex: ExprId,
    heq: ExprId,
) -> ExprId {
    let m = d.of_nat(n);
    let pp = d.of_nat(pn);
    let mp = d.imul(m, pp);
    let target = super::two_squares::is_sum_of_two_squares(d, pp);
    let int_ty = d.int_ty();
    let outer = norm_outer(d, mp);
    let minor = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let inner = norm_inner(d, mp, a);
        let hb_ty = super::two_squares::int_exists(d, inner);
        let body = with_hyp(d, hb_ty, &|d, hb| {
            let inner = norm_inner(d, mp, a);
            let target = super::two_squares::is_sum_of_two_squares(d, pp);
            let int_ty = d.int_ty();
            let minor_b = {
                let b_fv = d.fresh_fvar();
                let b = d.kernel().fvar(b_fv);
                let sum = measure(d, a, b);
                let heq2_ty = d.ieq(mp, sum);
                let leaf = with_hyp(d, heq2_ty, &|d, heq2| {
                    // `ofNat 1 = ofNat n`, so `p = 1·p = n·p = a²+b²`.
                    let one_nat = d.num(1);
                    let coerced_one = d.of_nat(one_nat);
                    let lifted = d.nat_eq_to_int(one_nat, n, heq, &|d, z| d.of_nat(z));
                    let scaled = d.icongr(coerced_one, m, lifted, &|d, z| d.imul(z, pp));
                    let one_pp = d.imul(coerced_one, pp);
                    let collapse = d.const_app(p.one_mul, &[pp]);
                    let expand = d.isymm(one_pp, pp, collapse);
                    let to_multiple = d.itrans(pp, one_pp, mp, expand, scaled);
                    let sum = measure(d, a, b);
                    let equation = d.itrans(pp, mp, sum, to_multiple, heq2);
                    d.const_app(p.is_sum_of_two_squares_intro, &[pp, a, b, equation])
                });
                d.lam_fv(b_fv, int_ty, leaf)
            };
            int_exists_elim(d, inner, target, hb, minor_b)
        });
        d.lam_fv(a_fv, int_ty, body)
    };
    int_exists_elim(d, outer, target, hex, minor)
}

/// The inductive case `1 < n`, once the two squares are named: choose centered
/// representatives for both and hand off to [`descent_next_multiplier`].
#[allow(clippy::too_many_arguments)]
fn descent_with_squares(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    pn: ExprId,
    n: ExprId,
    hprime: ExprId,
    ih: ExprId,
    hbelow: ExprId,
    hgt: ExprId,
    hm_pos: ExprId,
    hm_ne: ExprId,
    a: ExprId,
    b: ExprId,
    hfact: ExprId,
) -> ExprId {
    let m = d.of_nat(n);
    let pp = d.of_nat(pn);
    let target = super::two_squares::is_sum_of_two_squares(d, pp);
    let int_ty = d.int_ty();

    let rep_a = d.const_app(p.exists_centered_representative, &[a, m, hm_pos]);
    let pred_a = super::order_squares::centered_predicate(d, a, m);
    let minor_a = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hc_ty = centered_body(d, a, m, c);
        let body = with_hyp(d, hc_ty, &|d, hc| {
            let m = d.of_nat(n);
            let pp = d.of_nat(pn);
            let target = super::two_squares::is_sum_of_two_squares(d, pp);
            let int_ty = d.int_ty();
            let rep_b = d.const_app(p.exists_centered_representative, &[b, m, hm_pos]);
            let pred_b = super::order_squares::centered_predicate(d, b, m);
            let minor_b = {
                let e_fv = d.fresh_fvar();
                let e = d.kernel().fvar(e_fv);
                let he_ty = centered_body(d, b, m, e);
                let leaf = with_hyp(d, he_ty, &|d, he| {
                    let context = unpack_representatives(
                        d, m, pn, n, hprime, ih, hbelow, hgt, hm_pos, hm_ne, a, b, c, e, hfact, hc,
                        he,
                    );
                    descent_next_multiplier(d, p, context)
                });
                d.lam_fv(e_fv, int_ty, leaf)
            };
            int_exists_elim(d, pred_b, target, rep_b, minor_b)
        });
        d.lam_fv(c_fv, int_ty, body)
    };
    int_exists_elim(d, pred_a, target, rep_a, minor_a)
}

/// Split both centered-representative certificates into their leaves and pack
/// the whole inductive-case state into a [`Descent`].
#[allow(clippy::too_many_arguments)]
fn unpack_representatives(
    d: &mut IntDev<'_>,
    m: ExprId,
    pn: ExprId,
    n: ExprId,
    hprime: ExprId,
    ih: ExprId,
    hbelow: ExprId,
    hgt: ExprId,
    hm_pos: ExprId,
    hm_ne: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
    hfact: ExprId,
    hc: ExprId,
    he: ExprId,
) -> Descent {
    let (hca, low_c, high_c) = split_certificate(d, m, a, c, hc);
    let (heb, low_e, high_e) = split_certificate(d, m, b, e, he);
    Descent {
        pn,
        n,
        hprime,
        ih,
        hbelow,
        hgt,
        hm_pos,
        hm_ne,
        a,
        b,
        c,
        e,
        hfact,
        hca,
        heb,
        bands: [low_c, high_c, low_e, high_e],
    }
}

/// `hc : ModEq m c a ∧ (−m ≤ c+c ∧ c+c ≤ m)` split into its three leaves.
fn split_certificate(
    d: &mut IntDev<'_>,
    m: ExprId,
    a: ExprId,
    c: ExprId,
    hc: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let congruent = super::two_squares::imodeq(d, m, c, a);
    let double = d.iadd(c, c);
    let neg_m = d.ineg(m);
    let low_ty = d.ile(neg_m, double);
    let high_ty = d.ile(double, m);
    let bounds_ty = d.and(low_ty, high_ty);
    let modular = d.and_left(congruent, bounds_ty, hc);
    let band = d.and_right(congruent, bounds_ty, hc);
    let low = d.and_left(low_ty, high_ty, band);
    let high = d.and_right(low_ty, high_ty, band);
    (modular, low, high)
}

/// Produce the next multiplier and eliminate its witness.
fn descent_next_multiplier(d: &mut IntDev<'_>, p: super::IntPrelude, x: Descent) -> ExprId {
    let m = d.of_nat(x.n);
    let pp = d.of_nat(x.pn);
    let target = super::two_squares::is_sum_of_two_squares(d, pp);
    let int_ty = d.int_ty();
    let witness = d.const_app(
        p.exists_next_multiplier,
        &[m, pp, x.a, x.b, x.c, x.e, x.hfact, x.hca, x.heb],
    );
    let predicate = multiplier_predicate(d, m, x.c, x.e);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let mq = d.imul(m, q);
        let s = measure(d, x.c, x.e);
        let hq_ty = d.ieq(mq, s);
        let body = with_hyp(d, hq_ty, &|d, hq| descent_at_multiplier(d, p, x, q, hq));
        d.lam_fv(q_fv, int_ty, body)
    };
    int_exists_elim(d, predicate, target, witness, minor)
}

/// The heart of the descent: `0 ≤ q < m`, then `q ≠ 0` by primality, then the
/// induction hypothesis at `natAbs q`.
fn descent_at_multiplier(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    x: Descent,
    q: ExprId,
    hq: ExprId,
) -> ExprId {
    let m = d.of_nat(x.n);
    let zero = d.izero();

    // `0 ≤ q` and `q < m`, read off the factorisation.
    let bounds = d.const_app(
        p.descent_multiplier_bounds,
        &[
            m, q, x.c, x.e, x.hm_pos, hq, x.bands[0], x.bands[1], x.bands[2], x.bands[3],
        ],
    );
    let nonneg_ty = d.ile(zero, q);
    let below_ty = d.ilt(q, m);
    let hq_nonneg = d.and_left(nonneg_ty, below_ty, bounds);
    let hq_below = d.and_right(nonneg_ty, below_ty, bounds);

    // `q ≠ 0`: otherwise both representatives vanish, `m ∣ p` follows, and
    // primality refutes that for `1 < m < p`. The ONLY use of `hprime`.
    let zero_eq_q = d.ieq(zero, q);
    let hq_ne = with_hyp(d, zero_eq_q, &|d, hz| {
        degenerate_refutation(d, p, x, q, hq, hz)
    });
    let hq_pos = d.const_app(p.lt_of_le_of_ne, &[zero, q, hq_nonneg, hq_ne]);

    descent_recurse(d, p, x, q, hq, hq_nonneg, hq_below, hq_pos)
}

/// `0 = q` is impossible: it forces `m ∣ p` against `1 < m < p` prime.
fn degenerate_refutation(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    x: Descent,
    q: ExprId,
    hq: ExprId,
    hz: ExprId,
) -> ExprId {
    let m = d.of_nat(x.n);
    let pp = d.of_nat(x.pn);
    let zero = d.izero();
    let mq = d.imul(m, q);
    let s = measure(d, x.c, x.e);

    // `c²+e² = m·q = m·0 = 0`.
    let flipped = d.isymm(zero, q, hz);
    let m_zero = d.imul(m, zero);
    let shifted = d.icongr(q, zero, flipped, &|d, z| d.imul(m, z));
    let collapse = d.const_app(p.mul_zero, &[m]);
    let vanishes = d.itrans(mq, m_zero, zero, shifted, collapse);
    let reversed = d.isymm(mq, s, hq);
    let measure_zero = d.itrans(s, mq, zero, reversed, vanishes);

    let divides = d.const_app(
        p.dvd_of_degenerate_descent,
        &[
            m,
            pp,
            x.a,
            x.b,
            x.c,
            x.e,
            x.hm_ne,
            x.hfact,
            x.hca,
            x.heb,
            measure_zero,
        ],
    );
    let refutation = d.const_app(
        p.not_dvd_of_nat_of_prime_of_lt,
        &[x.pn, x.n, x.hprime, x.hgt, x.hbelow],
    );
    d.apply(refutation, &[divides])
}

/// Drop `q` back into `Nat` as `natAbs q`, build the recursive call's
/// hypothesis with `Int.descentStep`, and apply the induction hypothesis.
#[allow(clippy::too_many_arguments)]
fn descent_recurse(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    x: Descent,
    q: ExprId,
    hq: ExprId,
    hq_nonneg: ExprId,
    hq_below: ExprId,
    hq_pos: ExprId,
) -> ExprId {
    let np = d.prelude();
    let m = d.of_nat(x.n);
    let pp = d.of_nat(x.pn);
    let zero = d.izero();

    // `natAbs q` is the recursion's measure, and `ofNat (natAbs q) = q`.
    let magnitude = d.const_app(p.nat_abs, &[q]);
    let coerced = d.of_nat(magnitude);
    let named = d.const_app(p.of_nat_nat_abs_of_nonneg, &[q, hq_nonneg]);
    let backwards = d.isymm(coerced, q, named);

    // `natAbs q < n` and `0 < natAbs q`, both through `Int.lt_of_ofNat_lt_ofNat`.
    let lifted_below = d.int_eq_rewrite(q, coerced, backwards, hq_below, &|d, z| {
        let m = d.of_nat(x.n);
        d.ilt(z, m)
    });
    let below = d.const_app(p.lt_of_ofnat_lt_ofnat, &[magnitude, x.n, lifted_below]);
    let lifted_pos = d.int_eq_rewrite(q, coerced, backwards, hq_pos, &|d, z| {
        let zero = d.izero();
        d.ilt(zero, z)
    });
    let zero_nat = d.num(0);
    let positive = d.const_app(p.lt_of_ofnat_lt_ofnat, &[zero_nat, magnitude, lifted_pos]);

    // `natAbs q < p`, from `natAbs q < n < p` (this prelude has no
    // `Nat.lt_trans`, so the step up goes through `Nat.le_succ`).
    let successor = d.succ(x.n);
    let step_up = d.const_app(np.le_succ, &[x.n]);
    let n_le_pn = d.const_app(np.le_trans, &[x.n, successor, x.pn, step_up, x.hbelow]);
    let under_prime = d.const_app(np.lt_of_lt_of_le, &[magnitude, x.n, x.pn, below, n_le_pn]);

    // `a²+b² ≡ 0 (mod m)`, the cross-term lemma's last hypothesis.
    let mp = d.imul(m, pp);
    let norm = measure(d, x.a, x.b);
    let multiple = d.const_app(p.mul_mod_eq_zero, &[m, pp]);
    let vanishing = d.int_eq_rewrite(mp, norm, x.hfact, multiple, &|d, z| {
        let m = d.of_nat(x.n);
        let zero = d.izero();
        super::two_squares::imodeq(d, m, z, zero)
    });
    let cross = d.const_app(
        p.mod_eq_descent_cross_terms,
        &[m, x.a, x.b, x.c, x.e, x.hm_pos, x.hca, x.heb, vanishing],
    );
    let ac = d.imul(x.a, x.c);
    let be = d.imul(x.b, x.e);
    let first = d.iadd(ac, be);
    let ae = d.imul(x.a, x.e);
    let bc = d.imul(x.b, x.c);
    let second = d.isub(ae, bc);
    let left_ty = super::two_squares::imodeq(d, m, first, zero);
    let right_ty = super::two_squares::imodeq(d, m, second, zero);
    let cross_one = d.and_left(left_ty, right_ty, cross);
    let cross_two = d.and_right(left_ty, right_ty, cross);
    let dvd_one = d.const_app(p.dvd_of_mod_eq_zero, &[m, first, cross_one]);
    let dvd_two = d.const_app(p.dvd_of_mod_eq_zero, &[m, second, cross_two]);

    // Name both quotients and close with `Int.descentStep` plus the IH.
    let target = super::two_squares::is_sum_of_two_squares(d, pp);
    let pred_one = super::dvd::dvd_predicate(d, m, first);
    let int_ty = d.int_ty();
    let minor_one = {
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let mu = d.imul(m, u);
        let hu_ty = d.ieq(first, mu);
        let body = with_hyp(d, hu_ty, &|d, hu| {
            let m = d.of_nat(x.n);
            let pp = d.of_nat(x.pn);
            let target = super::two_squares::is_sum_of_two_squares(d, pp);
            let pred_two = super::dvd::dvd_predicate(d, m, second);
            let int_ty = d.int_ty();
            let minor_two = {
                let w_fv = d.fresh_fvar();
                let w = d.kernel().fvar(w_fv);
                let mw = d.imul(m, w);
                let hw_ty = d.ieq(second, mw);
                let leaf = with_hyp(d, hw_ty, &|d, hw| {
                    descent_apply_ih(
                        d,
                        p,
                        x,
                        q,
                        hq,
                        magnitude,
                        coerced,
                        backwards,
                        below,
                        positive,
                        under_prime,
                        first,
                        second,
                        u,
                        w,
                        hu,
                        hw,
                    )
                });
                d.lam_fv(w_fv, int_ty, leaf)
            };
            int_exists_elim(d, pred_two, target, dvd_two, minor_two)
        });
        d.lam_fv(u_fv, int_ty, body)
    };
    int_exists_elim(d, pred_one, target, dvd_one, minor_one)
}

/// The last leaf: `Int.descentStep` at the two named quotients gives
/// `q·p = u²+w²`; re-index it at `ofNat (natAbs q)` and feed the induction
/// hypothesis.
#[allow(clippy::too_many_arguments)]
fn descent_apply_ih(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    x: Descent,
    q: ExprId,
    hq: ExprId,
    magnitude: ExprId,
    coerced: ExprId,
    backwards: ExprId,
    below: ExprId,
    positive: ExprId,
    under_prime: ExprId,
    first: ExprId,
    second: ExprId,
    u: ExprId,
    w: ExprId,
    hu: ExprId,
    hw: ExprId,
) -> ExprId {
    let m = d.of_nat(x.n);
    let pp = d.of_nat(x.pn);
    let mu = d.imul(m, u);
    let mw = d.imul(m, w);
    let hu_flipped = d.isymm(first, mu, hu);
    let hw_flipped = d.isymm(second, mw, hw);

    let stepped = d.const_app(
        p.descent_step,
        &[
            m, pp, q, x.a, x.b, x.c, x.e, u, w, x.hm_ne, x.hfact, hq, hu_flipped, hw_flipped,
        ],
    );
    let reindexed = d.int_eq_rewrite(q, coerced, backwards, stepped, &|d, z| {
        let pp = d.of_nat(x.pn);
        let scaled = d.imul(z, pp);
        let sum = measure(d, u, w);
        d.ieq(scaled, sum)
    });

    let lhs = d.imul(coerced, pp);
    let inner = norm_inner(d, lhs, u);
    let with_w = int_exists_intro(d, inner, w, reindexed);
    let outer = norm_outer(d, lhs);
    let packaged = int_exists_intro(d, outer, u, with_w);
    d.apply(x.ih, &[magnitude, below, positive, under_prime, packaged])
}

/// `fun n ih => <the case split>` — `Nat.strongInduction`'s step argument.
fn descent_step_term(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    pn: ExprId,
    hprime: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let ih_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(k, n);
        let at_k = descent_motive(d, pn, k);
        let with_hk = d.arrow(hk_ty, at_k);
        d.pi_fv(k_fv, nat, with_hk)
    };
    let ih_fv = d.fresh_fvar();
    let ih = d.kernel().fvar(ih_fv);

    let zero_nat = d.num(0);
    let pos_ty = d.lt(zero_nat, n);
    let body = with_hyp(d, pos_ty, &|d, hpos| {
        let below_ty = d.lt(n, pn);
        with_hyp(d, below_ty, &|d, hbelow| {
            let m = d.of_nat(n);
            let pp = d.of_nat(pn);
            let mp = d.imul(m, pp);
            let hex_ty = exists_norm(d, mp);
            with_hyp(d, hex_ty, &|d, hex| {
                descent_case_split(d, p, pn, n, hprime, ih, hpos, hbelow, hex)
            })
        })
    });

    let with_ih = d.lam_fv(ih_fv, ih_ty, body);
    d.lam_fv(n_fv, nat, with_ih)
}

/// `1 ≤ n` splits into `1 < n` and `1 = n` — the descent's two branches.
///
/// `hpos : Nat.lt 0 n` IS `Nat.le 1 n` (`Nat.lt a b := Nat.le (succ a) b`, and
/// `1` is `succ zero`), so `Nat.lt_or_eq_of_le` applies to it directly with no
/// intervening step.
#[allow(clippy::too_many_arguments)]
fn descent_case_split(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    pn: ExprId,
    n: ExprId,
    hprime: ExprId,
    ih: ExprId,
    hpos: ExprId,
    hbelow: ExprId,
    hex: ExprId,
) -> ExprId {
    let np = d.prelude();
    let one_nat = d.num(1);
    let pp = d.of_nat(pn);
    let target = super::two_squares::is_sum_of_two_squares(d, pp);
    let split = d.const_app(np.lt_or_eq_of_le, &[one_nat, n, hpos]);
    let left = d.lt(one_nat, n);
    let right = d.eq(one_nat, n);
    d.or_elim(
        left,
        right,
        target,
        split,
        &|d, hgt| descent_inductive_case(d, p, pn, n, hprime, ih, hpos, hbelow, hgt, hex),
        &|d, heq| descent_base_case(d, p, pn, n, hex, heq),
    )
}

/// The `1 < n` branch: name the two squares of the current multiple, then
/// descend.
#[allow(clippy::too_many_arguments)]
fn descent_inductive_case(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    pn: ExprId,
    n: ExprId,
    hprime: ExprId,
    ih: ExprId,
    hpos: ExprId,
    hbelow: ExprId,
    hgt: ExprId,
    hex: ExprId,
) -> ExprId {
    let m = d.of_nat(n);
    let pp = d.of_nat(pn);
    let mp = d.imul(m, pp);
    let zero_nat = d.num(0);
    let hm_pos = d.const_app(p.lt_of_nat_of_lt, &[zero_nat, n, hpos]);
    let hm_ne = d.const_app(p.ne_zero_of_pos, &[m, hm_pos]);
    let target = super::two_squares::is_sum_of_two_squares(d, pp);
    let int_ty = d.int_ty();
    let outer = norm_outer(d, mp);
    let minor = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let inner = norm_inner(d, mp, a);
        let hb_ty = super::two_squares::int_exists(d, inner);
        let body = with_hyp(d, hb_ty, &|d, hb| {
            let inner = norm_inner(d, mp, a);
            let pp = d.of_nat(pn);
            let target = super::two_squares::is_sum_of_two_squares(d, pp);
            let int_ty = d.int_ty();
            let minor_b = {
                let b_fv = d.fresh_fvar();
                let b = d.kernel().fvar(b_fv);
                let sum = measure(d, a, b);
                let hfact_ty = d.ieq(mp, sum);
                let leaf = with_hyp(d, hfact_ty, &|d, hfact| {
                    descent_with_squares(
                        d, p, pn, n, hprime, ih, hbelow, hgt, hm_pos, hm_ne, a, b, hfact,
                    )
                });
                d.lam_fv(b_fv, int_ty, leaf)
            };
            int_exists_elim(d, inner, target, hb, minor_b)
        });
        d.lam_fv(a_fv, int_ty, body)
    };
    int_exists_elim(d, outer, target, hex, minor)
}

/// `Int.exists_sum_of_two_squares_of_multiple : ∀ (p : Nat), <p prime> →`
/// `  ∀ (n : Nat), Nat.lt 0 n → Nat.lt n p →`
/// `  (∃ a, ∃ b, Eq Int (mul (ofNat n) (ofNat p)) (add (mul a a) (mul b b))) →`
/// `  IsSumOfTwoSquares (ofNat p)`
/// — **Euler's descent**, the third of ADR-1647's four pieces.
///
/// `Nat.strongInduction` (ADR-1614) at a `Prop` motive, the same shape
/// `Nat.Hall.hall_sufficient` uses — but with no `refl`-generalisation needed,
/// because the measure IS the index: the multiplier is quantified as
/// `Int.ofNat n` rather than as an `Int` carrying a bridge hypothesis.
///
/// Base case `n = 1`: the multiple is the prime itself
/// ([`descent_base_case`]). Inductive case `1 < n`: centre both squares
/// modulo `m` ([`super::order_squares`]), produce the next multiplier
/// ([`declare_exists_next_multiplier`]), bound it
/// (`Int.descentMultiplierBounds`), rule out `q = 0`
/// ([`declare_dvd_of_degenerate_descent`] plus
/// [`declare_not_dvd_of_nat_of_prime_of_lt`]), and hand `Int.descentStep`'s
/// output to the induction hypothesis at `natAbs q`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_exists_sum_of_two_squares_of_multiple(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.exists_sum_of_two_squares_of_multiple, 1, &|d, v| {
        let pn = v[0];
        let nat = d.nat_ty();
        let prime_ty = super::wilson::prime_condition(d, pn);
        let stmt = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = descent_motive(d, pn, n);
            let with_n = d.pi_fv(n_fv, nat, body);
            d.arrow(prime_ty, with_n)
        };

        let proof = with_hyp(d, prime_ty, &|d, hprime| {
            let nat = d.nat_ty();
            let np = d.prelude();
            let motive = {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let body = descent_motive(d, pn, n);
                d.lam_fv(n_fv, nat, body)
            };
            let step = descent_step_term(d, p, pn, hprime);
            let zero_lvl = d.kernel().level_zero();
            let recursor = d.kernel().const_(np.strong_induction, vec![zero_lvl]);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let applied = d.apply(recursor, &[motive, step, n]);
            d.lam_fv(n_fv, nat, applied)
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// Fermat's theorem
// ============================================================================

/// `And (Eq Int (mul k p) (add (mul c c) (mul one one)))`
/// `    (And (lt zero k) (lt k p))` — the body of
/// `Int.exists_small_multiple_of_sq_add_one`'s inner existential.
///
/// Rebuilt here for the same reason [`centered_body`] is: `order_squares.rs`'s
/// own copy is private and that file belongs to another lane's history.
/// `small_multiple_outer` IS re-used, so a drift would be caught by the
/// `Exists.rec` below rather than passing silently.
fn small_multiple_body(d: &mut IntDev<'_>, modulus: ExprId, k: ExprId, c: ExprId) -> ExprId {
    let zero = d.izero();
    let kp = d.imul(k, modulus);
    let one = d.ione();
    let cc = d.imul(c, c);
    let one_one = d.imul(one, one);
    let sum = d.iadd(cc, one_one);
    let equation = d.ieq(kp, sum);
    let positive = d.ilt(zero, k);
    let below = d.ilt(k, modulus);
    let bounds = d.and(positive, below);
    d.and(equation, bounds)
}

/// `fun (c : Int) => <`[`small_multiple_body`]`>`.
fn small_multiple_inner(d: &mut IntDev<'_>, modulus: ExprId, k: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let body = small_multiple_body(d, modulus, k, c);
    d.lam_fv(c_fv, int_ty, body)
}

/// `Int.fermatTwoSquares : ∀ (m : Nat),`
/// `  (2 ≤ succ (2·m) ∧ ∀ d, d ∣ succ (2·m) → d = 1 ∨ d = succ (2·m)) →`
/// `  Nat.Even m → IsSumOfTwoSquares (ofNat (succ (2·m)))`
/// — **Fermat's theorem on sums of two squares**, and the last of ADR-1647's
/// four pieces.
///
/// The hypotheses are stated exactly as `Int.firstSupplementaryLawResidue`
/// states them — an odd prime written `p = 2m+1` with `m` EVEN, which is
/// `p ≡ 1 (mod 4)` — rather than as `p mod 4 = 1`, for the reason
/// `first_supplementary.rs` records: `Nat.mod` is stuck at symbolic arguments
/// while `Nat.Even`'s witness is an equation the sign lemma consumes directly.
///
/// Three lines of proof, each already a named theorem:
/// `Int.firstSupplementaryLawResidue` gives an `x` with `x² ≡ −1 (mod p)`;
/// `Int.exists_small_multiple_of_sq_add_one` turns that into `k` and `c` with
/// `k·p = c² + 1²` and `0 < k < p`; and
/// [`declare_exists_sum_of_two_squares_of_multiple`] descends from that
/// multiple to `p` itself. The only glue is the `Nat` bridge ADR-1647 sized:
/// `0 < p` from `p = succ _`, and `1 + 1 ≤ p` from the primality condition's
/// own first conjunct through [`declare_le_two_of_nat_le_two`].
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_fermat_two_squares(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.fermat_two_squares, 1, &|d, v| {
        let m = v[0];
        let np = d.prelude();
        let two_nat = d.num(2);
        let doubled = d.mul(two_nat, m);
        let pn = d.succ(doubled);
        let pp = d.of_nat(pn);

        let prime_ty = super::wilson::prime_condition(d, pn);
        let even_ty = d.const_app(np.even, &[m]);
        let concl = super::two_squares::is_sum_of_two_squares(d, pp);
        let stmt = {
            let tail = d.arrow(even_ty, concl);
            d.arrow(prime_ty, tail)
        };

        let proof = with_hyp(d, prime_ty, &|d, hprime| {
            let np = d.prelude();
            let even_ty = d.const_app(np.even, &[m]);
            with_hyp(d, even_ty, &|d, heven| {
                fermat_from_residue(d, p, m, hprime, heven)
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// The body of [`declare_fermat_two_squares`]: open the residue witness, enter
/// the descent, and descend.
fn fermat_from_residue(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    m: ExprId,
    hprime: ExprId,
    heven: ExprId,
) -> ExprId {
    let two_nat = d.num(2);
    let doubled = d.mul(two_nat, m);
    let pn = d.succ(doubled);
    let pp = d.of_nat(pn);
    let one = d.ione();
    let neg_one = d.ineg(one);
    let target = super::two_squares::is_sum_of_two_squares(d, pp);
    let int_ty = d.int_ty();

    // `−1 IS a quadratic residue mod p`, i.e. `∃ x, x·x ≡ −1 (mod p)`.
    let residue = d.const_app(p.first_supplementary_law_residue, &[m, hprime, heven]);
    let predicate = super::euler::residue_predicate(d, pp, neg_one);
    let minor = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let xx = d.imul(x, x);
        let hx_ty = super::two_squares::imodeq(d, pp, xx, neg_one);
        let body = with_hyp(d, hx_ty, &|d, hx| {
            fermat_from_witness(d, p, m, hprime, x, hx)
        });
        d.lam_fv(x_fv, int_ty, body)
    };
    super::euler::int_exists_elim(d, predicate, target, residue, minor)
}

/// From a square root of `−1` modulo `p`, enter the descent at
/// `Int.exists_small_multiple_of_sq_add_one` and open its double existential.
fn fermat_from_witness(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    m: ExprId,
    hprime: ExprId,
    x: ExprId,
    hx: ExprId,
) -> ExprId {
    let two_nat = d.num(2);
    let doubled = d.mul(two_nat, m);
    let pn = d.succ(doubled);
    let pp = d.of_nat(pn);
    let target = super::two_squares::is_sum_of_two_squares(d, pp);
    let int_ty = d.int_ty();

    // `0 < p` because `p` is a successor; `1 + 1 ≤ p` is the primality
    // condition's own first conjunct, coerced.
    let zero_nat = d.num(0);
    let positive_nat = d.zero_lt_succ(doubled);
    let hp_pos = d.const_app(p.lt_of_nat_of_lt, &[zero_nat, pn, positive_nat]);
    let (two_le_ty, divisor_ty) = prime_parts(d, pn);
    let two_le = d.and_left(two_le_ty, divisor_ty, hprime);
    let hp_two = d.const_app(p.le_two_of_nat_le_two, &[pn, two_le]);

    let entry = d.const_app(
        p.exists_small_multiple_of_sq_add_one,
        &[pp, x, hp_pos, hp_two, hx],
    );
    let outer = super::order_squares::small_multiple_outer(d, pp);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let inner = small_multiple_inner(d, pp, k);
        let hk_ty = super::two_squares::int_exists(d, inner);
        let body = with_hyp(d, hk_ty, &|d, hk| {
            let pp = d.of_nat(pn);
            let target = super::two_squares::is_sum_of_two_squares(d, pp);
            let inner = small_multiple_inner(d, pp, k);
            let int_ty = d.int_ty();
            let minor_c = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let payload_ty = small_multiple_body(d, pp, k, c);
                let leaf = with_hyp(d, payload_ty, &|d, payload| {
                    fermat_descend(d, p, pn, hprime, k, c, payload)
                });
                d.lam_fv(c_fv, int_ty, leaf)
            };
            super::euler::int_exists_elim(d, inner, target, hk, minor_c)
        });
        d.lam_fv(k_fv, int_ty, body)
    };
    super::euler::int_exists_elim(d, outer, target, entry, minor)
}

/// The last step: re-index the entry point's multiple at `natAbs k` and call
/// [`declare_exists_sum_of_two_squares_of_multiple`].
fn fermat_descend(
    d: &mut IntDev<'_>,
    p: super::IntPrelude,
    pn: ExprId,
    hprime: ExprId,
    k: ExprId,
    c: ExprId,
    payload: ExprId,
) -> ExprId {
    let pp = d.of_nat(pn);
    let zero = d.izero();
    let one = d.ione();

    // Unpack `k·p = c² + 1²` and `0 < k < p`.
    let kp = d.imul(k, pp);
    let cc = d.imul(c, c);
    let one_one = d.imul(one, one);
    let sum = d.iadd(cc, one_one);
    let equation_ty = d.ieq(kp, sum);
    let positive_ty = d.ilt(zero, k);
    let below_ty = d.ilt(k, pp);
    let bounds_ty = d.and(positive_ty, below_ty);
    let equation = d.and_left(equation_ty, bounds_ty, payload);
    let bounds = d.and_right(equation_ty, bounds_ty, payload);
    let hk_pos = d.and_left(positive_ty, below_ty, bounds);
    let hk_below = d.and_right(positive_ty, below_ty, bounds);

    // Name `natAbs k` and drop both bounds into `Nat`.
    let magnitude = d.const_app(p.nat_abs, &[k]);
    let coerced = d.of_nat(magnitude);
    let nonneg = d.const_app(p.le_of_lt, &[zero, k, hk_pos]);
    let named = d.const_app(p.of_nat_nat_abs_of_nonneg, &[k, nonneg]);
    let backwards = d.isymm(coerced, k, named);
    let lifted_pos = d.int_eq_rewrite(k, coerced, backwards, hk_pos, &|d, z| {
        let zero = d.izero();
        d.ilt(zero, z)
    });
    let zero_nat = d.num(0);
    let nk_pos = d.const_app(p.lt_of_ofnat_lt_ofnat, &[zero_nat, magnitude, lifted_pos]);
    let lifted_below = d.int_eq_rewrite(k, coerced, backwards, hk_below, &|d, z| {
        let pp = d.of_nat(pn);
        d.ilt(z, pp)
    });
    let nk_below = d.const_app(p.lt_of_ofnat_lt_ofnat, &[magnitude, pn, lifted_below]);

    // `(ofNat (natAbs k))·p = c² + 1²`, packaged as the descent's hypothesis.
    let reindexed = d.int_eq_rewrite(k, coerced, backwards, equation, &|d, z| {
        let pp = d.of_nat(pn);
        let scaled = d.imul(z, pp);
        let one = d.ione();
        let cc = d.imul(c, c);
        let one_one = d.imul(one, one);
        let sum = d.iadd(cc, one_one);
        d.ieq(scaled, sum)
    });
    let lhs = d.imul(coerced, pp);
    let inner = norm_inner(d, lhs, c);
    let with_one = int_exists_intro(d, inner, one, reindexed);
    let outer = norm_outer(d, lhs);
    let packaged = int_exists_intro(d, outer, c, with_one);

    d.const_app(
        p.exists_sum_of_two_squares_of_multiple,
        &[pn, hprime, magnitude, nk_pos, nk_below, packaged],
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
    declare_exists_sum_of_two_squares_of_multiple(d)?;
    declare_fermat_two_squares(d)?;
    Ok(())
}
