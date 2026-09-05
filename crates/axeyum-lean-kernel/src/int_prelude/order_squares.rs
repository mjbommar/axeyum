//! **The ℤ order shelf Fermat's descent needs**: two-sided square
//! monotonicity, halving, the centered remainder, and the strict decrease
//! (W3-10, second slice, ADR-1647).
//!
//! ## What was actually missing
//!
//! `two_squares.rs`'s module doc (2026-09-05) records the obstruction as "this
//! prelude has no `Int` absolute-value order lemmas at all: `natAbs_le_iff`,
//! `mul_le_mul` over ℤ and `sq_le_sq` do not [exist]". **Two thirds of that is
//! stale.** Measured here with a freshly built `shape_search`
//! (`declarations=3236`, positive control `Int.descentStep` FOUND):
//!
//! - `Int.nat_abs_le_iff_mul_self_le : natAbs a ≤ natAbs b ↔ a*a ≤ b*b` and its
//!   `<` and `=` siblings landed on 2026-09-01 in `nat_abs_mirrors.rs`;
//! - `Int.mul_le_mul_of_nonneg_left`, `Int.add_le_add`, `Int.add_le_add_iff_left`
//!   /`_right`, `Int.le_total`, `Int.le_antisymm`, `Int.lt_of_le_of_ne`,
//!   `Int.mul_pos`, `Int.sq_nonneg`, `Int.emod_nonneg` and
//!   `Int.emod_lt_of_pos` were all already declared.
//!
//! What was genuinely absent is the *shape* of the bound, not the algebra:
//! nothing turned a two-sided bound `−m ≤ x ≤ m` into `x² ≤ m²`, nothing
//! produced a representative of `a mod m` inside that band, and nothing halved
//! an inequality. Those are this module.
//!
//! ## Why `x + x` and not `2 * x`
//!
//! Every bound here is stated with `Int.add c c`, never `Int.mul (ofNat 2) c`.
//! The two are equal and the `mul` form reads closer to the textbook, but the
//! `add` form is the one the existing shelf can *move*: doubling an inequality
//! is then literally `Int.add_le_add h h`, with no `0 ≤ 2` side condition and
//! no numeral for `ring::int` to normalise. Every lemma below that would
//! otherwise have needed `Int.mul_le_mul_of_nonneg_left` at the constant `2`
//! needs nothing at all in this form.
//!
//! **This is not a weakening.** `2·|c| ≤ m` and `−m ≤ c+c ≤ m` are the same
//! statement about `c`; the second is the one that composes here.
//!
//! ## What is deliberately NOT declared here
//!
//! `Int.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg` and its three sign
//! siblings, and `Int.mul_le_mul_of_natAbs_le`, are rows of the **held-out**
//! `integer-natcast` family (`artifacts/autogenesis/nursery-v2-extension.json`
//! carries the partition), and `Int.lt_of_sum_four_squares_eq_mul` is a row of
//! the held-out `descent-and-well-ordering` family. None of them is declared,
//! and no lemma here is stated in their shape: [`declare_sq_le_sq_of_neg_le_of_le`]
//! takes `−b ≤ a ≤ b` in ONE variable pair, which is a different proposition
//! from any four-variable product bound. `Int.natAbs_le_iff_mul_self_le` IS a
//! held-out row, but its family (`integer-absolute-value`) was drawn and scored
//! on 2026-09-01, so it is already in the environment; nothing here re-proves
//! it.

use super::euler::int_exists_intro;
use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ============================================================================
// local plumbing
// ============================================================================

/// `Iff.mp left right h_iff h_left : right`.
fn iff_mp(d: &mut IntDev<'_>, left: ExprId, right: ExprId, h_iff: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.iff_mp;
    d.const_app(name, &[left, right, h_iff, h])
}

/// `And.intro left right h_left h_right : And left right`.
fn and_intro(d: &mut IntDev<'_>, left: ExprId, right: ExprId, hl: ExprId, hr: ExprId) -> ExprId {
    let name = d.int().logic.and_intro;
    d.const_app(name, &[left, right, hl, hr])
}

/// `Int.le_trans a b c h1 h2 : le a c`.
fn le_trans(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
    let name = d.int().le_trans;
    d.const_app(name, &[a, b, c, h1, h2])
}

/// `Int.lt_irrefl a h : False`, from `h : lt a a`.
fn lt_irrefl_absurd(d: &mut IntDev<'_>, a: ExprId, h: ExprId) -> ExprId {
    let name = d.int().lt_irrefl;
    let head = d.const_app(name, &[a]);
    d.apply(head, &[h])
}

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

/// `Int.le_total a b : Or (le a b) (le b a)`, eliminated into `target`.
fn by_le_total(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    target: ExprId,
    on_le: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    on_ge: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let name = d.int().le_total;
    let witness = d.const_app(name, &[a, b]);
    let left = d.ile(a, b);
    let right = d.ile(b, a);
    d.or_elim(left, right, target, witness, on_le, on_ge)
}

// ============================================================================
// sign and negation
// ============================================================================

/// `Int.ne_zero_of_pos : ∀ k, lt zero k → Not (Eq Int k zero)`.
///
/// The side condition every cancellation lemma in this file wants, in exactly
/// the form `Int.mul_left_cancel_of_ne_zero` and `Int.emod_nonneg` state it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_ne_zero_of_pos(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.ne_zero_of_pos, 1, &|d, v| {
        let k = v[0];
        let zero = d.izero();
        let pos = d.ilt(zero, k);
        let eq_zero = d.ieq(k, zero);
        let ne = d.not(eq_zero);
        let stmt = d.arrow(pos, ne);

        let proof = with_hyp(d, pos, &|d, hk| {
            let eq_zero = {
                let zero = d.izero();
                d.ieq(k, zero)
            };
            with_hyp(d, eq_zero, &|d, heq| {
                let zero = d.izero();
                let bad = d.int_eq_rewrite(k, zero, heq, hk, &|d, x| {
                    let zero = d.izero();
                    d.ilt(zero, x)
                });
                lt_irrefl_absurd(d, zero, bad)
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.neg_nonpos_of_nonneg : ∀ a, le zero a → le (neg a) zero`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_neg_nonpos_of_nonneg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.neg_nonpos_of_nonneg, 1, &|d, v| {
        let a = v[0];
        let zero = d.izero();
        let neg_a = d.ineg(a);
        let hyp = d.ile(zero, a);
        let concl = d.ile(neg_a, zero);
        let stmt = d.arrow(hyp, concl);

        let proof = with_hyp(d, hyp, &|d, h| {
            let zero = d.izero();
            let neg_a = d.ineg(a);
            // `le (0 + (-a)) (a + (-a))`.
            let step = d.const_app(p.add_le_add_right, &[zero, a, neg_a, h]);
            let zero_neg = d.iadd(zero, neg_a);
            let a_neg = d.iadd(a, neg_a);
            let left = d.const_app(p.zero_add, &[neg_a]);
            let moved = d.int_eq_rewrite(zero_neg, neg_a, left, step, &|d, x| {
                let neg_a = d.ineg(a);
                let a_neg = d.iadd(a, neg_a);
                d.ile(x, a_neg)
            });
            let right = d.const_app(p.add_neg, &[a]);
            d.int_eq_rewrite(a_neg, zero, right, moved, &|d, x| {
                let neg_a = d.ineg(a);
                d.ile(neg_a, x)
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.neg_nonneg_of_nonpos : ∀ a, le a zero → le zero (neg a)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_neg_nonneg_of_nonpos(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.neg_nonneg_of_nonpos, 1, &|d, v| {
        let a = v[0];
        let zero = d.izero();
        let neg_a = d.ineg(a);
        let hyp = d.ile(a, zero);
        let concl = d.ile(zero, neg_a);
        let stmt = d.arrow(hyp, concl);

        let proof = with_hyp(d, hyp, &|d, h| {
            let zero = d.izero();
            let neg_a = d.ineg(a);
            // `le (a + (-a)) (0 + (-a))`.
            let step = d.const_app(p.add_le_add_right, &[a, zero, neg_a, h]);
            let a_neg = d.iadd(a, neg_a);
            let zero_neg = d.iadd(zero, neg_a);
            let left = d.const_app(p.add_neg, &[a]);
            let moved = d.int_eq_rewrite(a_neg, zero, left, step, &|d, x| {
                let zero = d.izero();
                let neg_a = d.ineg(a);
                let zero_neg = d.iadd(zero, neg_a);
                d.ile(x, zero_neg)
            });
            let right = d.const_app(p.zero_add, &[neg_a]);
            d.int_eq_rewrite(zero_neg, neg_a, right, moved, &|d, x| {
                let zero = d.izero();
                d.ile(zero, x)
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.neg_le_of_neg_le : ∀ a b, le (neg b) a → le (neg a) b`.
///
/// The half of a two-sided bound that flips: `−b ≤ a` says exactly `−a ≤ b`,
/// and the descent's lower bound arrives in one orientation and is consumed in
/// the other.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_neg_le_of_neg_le(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.neg_le_of_neg_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let neg_a = d.ineg(a);
        let neg_b = d.ineg(b);
        let hyp = d.ile(neg_b, a);
        let concl = d.ile(neg_a, b);
        let stmt = d.arrow(hyp, concl);

        let proof = with_hyp(d, hyp, &|d, h| {
            let zero = d.izero();
            let neg_a = d.ineg(a);
            let neg_b = d.ineg(b);
            // `le ((-b) + b) (a + b)`, then `(-b) + b = 0`.
            let step = d.const_app(p.add_le_add_right, &[neg_b, a, b, h]);
            let negb_b = d.iadd(neg_b, b);
            let a_b = d.iadd(a, b);
            let cancel = d.const_app(p.add_left_neg, &[b]);
            let zero_le = d.int_eq_rewrite(negb_b, zero, cancel, step, &|d, x| {
                let a_b = d.iadd(a, b);
                d.ile(x, a_b)
            });
            // `0 = (-a) + a` and `a + b = b + a`, so the left side of
            // `add_le_add_iff_right` matches.
            let nega_a = d.iadd(neg_a, a);
            let cancel_a = d.const_app(p.add_left_neg, &[a]);
            let cancel_a_rev = d.isymm(nega_a, zero, cancel_a);
            let shifted = d.int_eq_rewrite(zero, nega_a, cancel_a_rev, zero_le, &|d, x| {
                let a_b = d.iadd(a, b);
                d.ile(x, a_b)
            });
            let b_a = d.iadd(b, a);
            let comm = d.const_app(p.add_comm, &[a, b]);
            let ready = d.int_eq_rewrite(a_b, b_a, comm, shifted, &|d, x| {
                let neg_a = d.ineg(a);
                let nega_a = d.iadd(neg_a, a);
                d.ile(nega_a, x)
            });
            let iff = d.const_app(p.add_le_add_iff_right, &[neg_a, b, a]);
            let left = d.ile(nega_a, b_a);
            let right = d.ile(neg_a, b);
            iff_mp(d, left, right, iff, ready)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.add_nonneg : ∀ a b, le zero a → le zero b → le zero (add a b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_add_nonneg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_nonneg, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let h1_ty = d.ile(zero, a);
        let h2_ty = d.ile(zero, b);
        let sum = d.iadd(a, b);
        let concl = d.ile(zero, sum);
        let stmt = {
            let tail = d.arrow(h2_ty, concl);
            d.arrow(h1_ty, tail)
        };

        let proof = with_hyp(d, h1_ty, &|d, h1| {
            let h2_ty = {
                let zero = d.izero();
                d.ile(zero, b)
            };
            with_hyp(d, h2_ty, &|d, h2| {
                let zero = d.izero();
                let step = d.const_app(p.add_le_add, &[zero, a, zero, b, h1, h2]);
                let zero_zero = d.iadd(zero, zero);
                let collapse = d.const_app(p.add_zero, &[zero]);
                d.int_eq_rewrite(zero_zero, zero, collapse, step, &|d, x| {
                    let sum = d.iadd(a, b);
                    d.ile(x, sum)
                })
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.sub_nonpos_of_le : ∀ a b, le a b → le (sub a b) zero`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sub_nonpos_of_le(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.sub_nonpos_of_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let diff = d.isub(a, b);
        let hyp = d.ile(a, b);
        let concl = d.ile(diff, zero);
        let stmt = d.arrow(hyp, concl);

        let proof = with_hyp(d, hyp, &|d, h| {
            let zero = d.izero();
            let diff = d.isub(a, b);
            // `a = (a-b) + b` and `b = 0 + b`, backwards, so `h` becomes the
            // left side of `add_le_add_iff_right`.
            let diff_b = d.iadd(diff, b);
            let cancel = d.const_app(p.add_sub_cancel_right, &[a, b]);
            let cancel_rev = d.isymm(diff_b, a, cancel);
            let step1 = d.int_eq_rewrite(a, diff_b, cancel_rev, h, &|d, x| d.ile(x, b));
            let zero_b = d.iadd(zero, b);
            let zadd = d.const_app(p.zero_add, &[b]);
            let zadd_rev = d.isymm(zero_b, b, zadd);
            let step2 = d.int_eq_rewrite(b, zero_b, zadd_rev, step1, &|d, x| {
                let diff = d.isub(a, b);
                let diff_b = d.iadd(diff, b);
                d.ile(diff_b, x)
            });
            let iff = d.const_app(p.add_le_add_iff_right, &[diff, zero, b]);
            let left = d.ile(diff_b, zero_b);
            let right = d.ile(diff, zero);
            iff_mp(d, left, right, iff, step2)
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// halving and cancellation
// ============================================================================

/// `Int.le_of_add_le_add_self : ∀ a b, le (add a a) (add b b) → le a b`.
///
/// **Halving an inequality**, which is what makes the `x + x` spelling of the
/// bounds pay for itself: the descent produces `4(c²+e²) ≤ 2m²` and needs
/// `2(c²+e²) ≤ m²`, and this is the only step that divides.
///
/// Not by cancelling `2`: by `le_total`. In the `b ≤ a` branch,
/// `b + a ≤ a + a ≤ b + b`, and `add_le_add_iff_left` peels the shared `b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_le_of_add_le_add_self(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.le_of_add_le_add_self, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let aa = d.iadd(a, a);
        let bb = d.iadd(b, b);
        let hyp = d.ile(aa, bb);
        let concl = d.ile(a, b);
        let stmt = d.arrow(hyp, concl);

        let proof = with_hyp(d, hyp, &|d, h| {
            let concl = d.ile(a, b);
            by_le_total(d, a, b, concl, &|_d, hab| hab, &|d, hba| {
                let aa = d.iadd(a, a);
                let bb = d.iadd(b, b);
                let ba = d.iadd(b, a);
                let step = d.const_app(p.add_le_add_right, &[b, a, a, hba]);
                let chained = le_trans(d, ba, aa, bb, step, h);
                let iff = d.const_app(p.add_le_add_iff_left, &[b, a, b]);
                let left = d.ile(ba, bb);
                let right = d.ile(a, b);
                iff_mp(d, left, right, iff, chained)
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.le_of_mul_le_mul_left : ∀ k a b, lt zero k → le (mul k a) (mul k b) → le a b`.
///
/// Cancellation on the left of a product, by `le_total` and
/// `Int.mul_left_cancel_of_ne_zero`: in the `b ≤ a` branch the two bounds are
/// antisymmetric, so `k*a = k*b`, so `a = b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_le_of_mul_le_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.le_of_mul_le_mul_left, 3, &|d, v| {
        let (k, a, b) = (v[0], v[1], v[2]);
        let zero = d.izero();
        let pos = d.ilt(zero, k);
        let ka = d.imul(k, a);
        let kb = d.imul(k, b);
        let bound = d.ile(ka, kb);
        let concl = d.ile(a, b);
        let stmt = {
            let tail = d.arrow(bound, concl);
            d.arrow(pos, tail)
        };

        let proof = with_hyp(d, pos, &|d, hk| {
            let bound = {
                let ka = d.imul(k, a);
                let kb = d.imul(k, b);
                d.ile(ka, kb)
            };
            with_hyp(d, bound, &|d, h| {
                let concl = d.ile(a, b);
                by_le_total(d, a, b, concl, &|_d, hab| hab, &|d, hba| {
                    let zero = d.izero();
                    let ka = d.imul(k, a);
                    let kb = d.imul(k, b);
                    let hk0 = d.const_app(p.le_of_lt, &[zero, k, hk]);
                    let flipped = d.const_app(p.mul_le_mul_of_nonneg_left, &[k, b, a, hk0, hba]);
                    let equal = d.const_app(p.le_antisymm, &[ka, kb, h, flipped]);
                    let kne = d.const_app(p.ne_zero_of_pos, &[k, hk]);
                    let ab = d.const_app(p.mul_left_cancel_of_ne_zero, &[k, a, b, kne, equal]);
                    let refl = d.const_app(p.le_refl, &[a]);
                    d.int_eq_rewrite(a, b, ab, refl, &|d, x| d.ile(a, x))
                })
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// squares under a two-sided bound
// ============================================================================

/// `Int.neg_mul_neg : ∀ a, Eq Int (mul (neg a) (neg a)) (mul a a)`. Emitted by
/// `ring::int` (ADR-1582), never written by hand.
///
/// # Errors
///
/// The trusted gate's rejection, or `UnknownConst` if the ring search declined.
fn declare_neg_mul_neg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.neg_mul_neg, 1, &|d, v| {
        let a = v[0];
        let neg_a = d.ineg(a);
        let lhs = d.imul(neg_a, neg_a);
        let rhs = d.imul(a, a);
        d.ieq(lhs, rhs)
    })
}

/// `Int.neg_add_self_self : ∀ m, Eq Int (add (neg m) (add m m)) m`. `ring::int`.
///
/// # Errors
///
/// As [`declare_neg_mul_neg`].
fn declare_neg_add_self_self(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.neg_add_self_self, 1, &|d, v| {
        let m = v[0];
        let neg_m = d.ineg(m);
        let mm = d.iadd(m, m);
        let lhs = d.iadd(neg_m, mm);
        d.ieq(lhs, m)
    })
}

/// `Int.add_sub_add_sub : ∀ r m,`
/// `  Eq Int (add (sub r m) (sub r m)) (sub (add r r) (add m m))`. `ring::int`.
///
/// # Errors
///
/// As [`declare_neg_mul_neg`].
fn declare_add_sub_add_sub(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.add_sub_add_sub, 2, &|d, v| {
        let (r, m) = (v[0], v[1]);
        let diff = d.isub(r, m);
        let lhs = d.iadd(diff, diff);
        let rr = d.iadd(r, r);
        let mm = d.iadd(m, m);
        let rhs = d.isub(rr, mm);
        d.ieq(lhs, rhs)
    })
}

/// `Int.sq_double_add_sq_double : ∀ c e,`
/// `  Eq Int (add (mul (add c c) (add c c)) (mul (add e e) (add e e)))`
/// `         (add (add S S) (add S S))`, with `S := c*c + e*e`. `ring::int`.
///
/// Both sides are `4c² + 4e²`; the point is that the right one is the measure
/// `S` doubled twice, which is exactly the shape
/// [`declare_le_of_add_le_add_self`] halves.
///
/// # Errors
///
/// As [`declare_neg_mul_neg`].
fn declare_sq_double_add_sq_double(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.sq_double_add_sq_double, 2, &|d, v| {
        let (c, e) = (v[0], v[1]);
        let cc2 = d.iadd(c, c);
        let ee2 = d.iadd(e, e);
        let left = d.imul(cc2, cc2);
        let right = d.imul(ee2, ee2);
        let lhs = d.iadd(left, right);
        let cc = d.imul(c, c);
        let ee = d.imul(e, e);
        let s = d.iadd(cc, ee);
        let ss = d.iadd(s, s);
        let rhs = d.iadd(ss, ss);
        d.ieq(lhs, rhs)
    })
}

/// `Int.sq_le_sq_of_nonneg : ∀ a b, le zero a → le a b → le (mul a a) (mul b b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sq_le_sq_of_nonneg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.sq_le_sq_of_nonneg, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let h0_ty = d.ile(zero, a);
        let hab_ty = d.ile(a, b);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let concl = d.ile(aa, bb);
        let stmt = {
            let tail = d.arrow(hab_ty, concl);
            d.arrow(h0_ty, tail)
        };

        let proof = with_hyp(d, h0_ty, &|d, h0| {
            let hab_ty = d.ile(a, b);
            with_hyp(d, hab_ty, &|d, hab| {
                let zero = d.izero();
                let aa = d.imul(a, a);
                let ab = d.imul(a, b);
                let ba = d.imul(b, a);
                let bb = d.imul(b, b);
                let h0b = le_trans(d, zero, a, b, h0, hab);
                let s1 = d.const_app(p.mul_le_mul_of_nonneg_left, &[a, a, b, h0, hab]);
                let s2 = d.const_app(p.mul_le_mul_of_nonneg_left, &[b, a, b, h0b, hab]);
                let comm = d.const_app(p.mul_comm, &[a, b]);
                let s1_moved = d.int_eq_rewrite(ab, ba, comm, s1, &|d, x| {
                    let aa = d.imul(a, a);
                    d.ile(aa, x)
                });
                le_trans(d, aa, ba, bb, s1_moved, s2)
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.sq_le_sq_of_neg_le_of_le : ∀ a b, le (neg b) a → le a b →`
/// `  le (mul a a) (mul b b)` — **the two-sided square bound**, the piece the
/// two-squares lane sized as missing.
///
/// `le_total zero a` splits it: the non-negative half is
/// [`declare_sq_le_sq_of_nonneg`] outright, and the non-positive half is the
/// same lemma at `−a` (whose square `ring::int` identifies with `a`'s).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sq_le_sq_of_neg_le_of_le(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.sq_le_sq_of_neg_le_of_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let neg_b = d.ineg(b);
        let low_ty = d.ile(neg_b, a);
        let high_ty = d.ile(a, b);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let concl = d.ile(aa, bb);
        let stmt = {
            let tail = d.arrow(high_ty, concl);
            d.arrow(low_ty, tail)
        };

        let proof = with_hyp(d, low_ty, &|d, hlow| {
            let high_ty = d.ile(a, b);
            with_hyp(d, high_ty, &|d, hhigh| {
                let zero = d.izero();
                let aa = d.imul(a, a);
                let bb = d.imul(b, b);
                let target = d.ile(aa, bb);
                by_le_total(
                    d,
                    zero,
                    a,
                    target,
                    &|d, hpos| d.const_app(p.sq_le_sq_of_nonneg, &[a, b, hpos, hhigh]),
                    &|d, hneg| {
                        let neg_a = d.ineg(a);
                        let nn = d.imul(neg_a, neg_a);
                        let hn0 = d.const_app(p.neg_nonneg_of_nonpos, &[a, hneg]);
                        let hnb = d.const_app(p.neg_le_of_neg_le, &[a, b, hlow]);
                        let base = d.const_app(p.sq_le_sq_of_nonneg, &[neg_a, b, hn0, hnb]);
                        let eqn = d.const_app(p.neg_mul_neg, &[a]);
                        let aa = d.imul(a, a);
                        d.int_eq_rewrite(nn, aa, eqn, base, &|d, x| {
                            let bb = d.imul(b, b);
                            d.ile(x, bb)
                        })
                    },
                )
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// the centered remainder
// ============================================================================

/// `fun (c : Int) => And (ModEq m c a) (And (le (neg m) (add c c)) (le (add c c) m))`
/// — the body of [`declare_exists_centered_representative`]'s existential.
fn centered_predicate(d: &mut IntDev<'_>, a: ExprId, m: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let body = centered_body(d, a, m, c);
    d.lam_fv(c_fv, int_ty, body)
}

/// `And (ModEq m c a) (And (le (neg m) (add c c)) (le (add c c) m))`.
fn centered_body(d: &mut IntDev<'_>, a: ExprId, m: ExprId, c: ExprId) -> ExprId {
    let congruent = super::two_squares::imodeq(d, m, c, a);
    let double = d.iadd(c, c);
    let neg_m = d.ineg(m);
    let low = d.ile(neg_m, double);
    let high = d.ile(double, m);
    let bounds = d.and(low, high);
    d.and(congruent, bounds)
}

/// `Int.exists_centered_representative : ∀ a m, lt zero m →`
/// `  ∃ c, ModEq m c a ∧ (neg m ≤ c + c ∧ c + c ≤ m)`
/// — **the bounded choice of representative** the descent needs, and the piece
/// `two_squares.rs` names as its first missing ingredient.
///
/// The witness is `a % m` when `(a%m) + (a%m) ≤ m`, and `a % m − m` otherwise.
/// Only `Int.emod_nonneg`, `Int.emod_lt_of_pos`, `Int.ediv_add_emod` and
/// `Int.modEq_add_mul_left` are used — no decidable `if`, because
/// `Int.le_total` supplies the split as an `Or` and both branches build a
/// witness.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_exists_centered_representative(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.exists_centered_representative, 2, &|d, v| {
        let (a, m) = (v[0], v[1]);
        let zero = d.izero();
        let pos = d.ilt(zero, m);
        let predicate = centered_predicate(d, a, m);
        let concl = super::two_squares::int_exists(d, predicate);
        let stmt = d.arrow(pos, concl);

        let proof = with_hyp(d, pos, &|d, hm| {
            let zero = d.izero();
            let hm0 = d.const_app(p.le_of_lt, &[zero, m, hm]);
            let hmne = d.const_app(p.ne_zero_of_pos, &[m, hm]);
            let r = d.iemod(a, m);
            let hr0 = d.const_app(p.emod_nonneg, &[a, m, hmne]);
            let hrm = d.const_app(p.emod_lt_of_pos, &[a, m, hm]);
            let hrm_le = d.const_app(p.le_of_lt, &[r, m, hrm]);

            // `ModEq m r a`, from `m*(a/m) + r = a` and `modEq_add_mul_left`.
            let q = d.iediv(a, m);
            let core = d.const_app(p.mod_eq_add_mul_left, &[m, r, q]);
            let mq = d.imul(m, q);
            let mq_r = d.iadd(mq, r);
            let split = d.const_app(p.ediv_add_emod, &[a, m]);
            let modeq_a_r = d.int_eq_rewrite(mq_r, a, split, core, &|d, x| {
                super::two_squares::imodeq(d, m, x, r)
            });
            let hmod = d.const_app(p.mod_eq_symm, &[m, a, r, modeq_a_r]);

            let rr = d.iadd(r, r);
            let predicate = centered_predicate(d, a, m);
            let target = super::two_squares::int_exists(d, predicate);
            by_le_total(
                d,
                rr,
                m,
                target,
                &|d, hup| {
                    // `c := r`. The lower bound is `-m <= 0 <= r + r`.
                    let zero = d.izero();
                    let r = d.iemod(a, m);
                    let rr = d.iadd(r, r);
                    let neg_m = d.ineg(m);
                    let neg_nonpos = d.const_app(p.neg_nonpos_of_nonneg, &[m, hm0]);
                    let rr_nonneg = d.const_app(p.add_nonneg, &[r, r, hr0, hr0]);
                    let low = le_trans(d, neg_m, zero, rr, neg_nonpos, rr_nonneg);
                    let low_ty = d.ile(neg_m, rr);
                    let high_ty = d.ile(rr, m);
                    let bounds = and_intro(d, low_ty, high_ty, low, hup);
                    let congruent = super::two_squares::imodeq(d, m, r, a);
                    let bounds_ty = d.and(low_ty, high_ty);
                    let payload = and_intro(d, congruent, bounds_ty, hmod, bounds);
                    let predicate = centered_predicate(d, a, m);
                    int_exists_intro(d, predicate, r, payload)
                },
                &|d, hlow| {
                    // `c := r - m`.
                    let zero = d.izero();
                    let r = d.iemod(a, m);
                    let c = d.isub(r, m);
                    let neg_m = d.ineg(m);

                    // `ModEq m (r - m) r`: `modEq_add_mul_left m r (-1)` gives
                    // `ModEq m (m*(-1) + r) r`, and `m*(-1) + r = r - m`.
                    let one = d.ione();
                    let neg_one = d.ineg(one);
                    let core2 = d.const_app(p.mod_eq_add_mul_left, &[m, r, neg_one]);
                    let m_neg_one = d.imul(m, neg_one);
                    let neg_one_m = d.imul(neg_one, m);
                    let comm = d.const_app(p.mul_comm, &[m, neg_one]);
                    let nom = d.const_app(p.neg_one_mul, &[m]);
                    let to_neg_m = d.itrans(m_neg_one, neg_one_m, neg_m, comm, nom);
                    let step_a = d.int_eq_rewrite(m_neg_one, neg_m, to_neg_m, core2, &|d, x| {
                        let sum = d.iadd(x, r);
                        super::two_squares::imodeq(d, m, sum, r)
                    });
                    let negm_r = d.iadd(neg_m, r);
                    let r_negm = d.iadd(r, neg_m);
                    let comm2 = d.const_app(p.add_comm, &[neg_m, r]);
                    let fold = d.const_app(p.add_neg_eq_sub, &[r, m]);
                    let to_sub = d.itrans(negm_r, r_negm, c, comm2, fold);
                    let step_b = d.int_eq_rewrite(negm_r, c, to_sub, step_a, &|d, x| {
                        super::two_squares::imodeq(d, m, x, r)
                    });
                    let hmod2 = d.const_app(p.mod_eq_trans, &[m, c, r, a, step_b, hmod]);

                    // The bounds, through `(r-m) + (r-m) = (r+r) - (m+m)`.
                    let cc = d.iadd(c, c);
                    let rr = d.iadd(r, r);
                    let mm = d.iadd(m, m);
                    let diff = d.isub(rr, mm);
                    let dbl = d.const_app(p.add_sub_add_sub, &[r, m]);

                    // upper: `(r+r) - (m+m) <= 0 <= m`.
                    let rr_mm = d.const_app(p.add_le_add, &[r, m, r, m, hrm_le, hrm_le]);
                    let nonpos = d.const_app(p.sub_nonpos_of_le, &[rr, mm, rr_mm]);
                    let up0 = le_trans(d, diff, zero, m, nonpos, hm0);
                    let dbl_rev = d.isymm(diff, cc, dbl);
                    let high = d.int_eq_rewrite(diff, cc, dbl_rev, up0, &|d, x| d.ile(x, m));

                    // lower: `-m <= (r+r) - (m+m)`, from `m <= r + r` shifted by
                    // `m+m` through `add_le_add_iff_right`.
                    let negm_mm = d.iadd(neg_m, mm);
                    let collapse = d.const_app(p.neg_add_self_self, &[m]);
                    let collapse_rev = d.isymm(negm_mm, m, collapse);
                    let shifted = d.int_eq_rewrite(m, negm_mm, collapse_rev, hlow, &|d, x| {
                        let r = d.iemod(a, m);
                        let rr = d.iadd(r, r);
                        d.ile(x, rr)
                    });
                    let diff_mm = d.iadd(diff, mm);
                    let restore = d.const_app(p.add_sub_cancel_right, &[rr, mm]);
                    let restore_rev = d.isymm(diff_mm, rr, restore);
                    let ready = d.int_eq_rewrite(rr, diff_mm, restore_rev, shifted, &|d, x| {
                        let neg_m = d.ineg(m);
                        let mm = d.iadd(m, m);
                        let negm_mm = d.iadd(neg_m, mm);
                        d.ile(negm_mm, x)
                    });
                    let iff = d.const_app(p.add_le_add_iff_right, &[neg_m, diff, mm]);
                    let iff_left = d.ile(negm_mm, diff_mm);
                    let iff_right = d.ile(neg_m, diff);
                    let low0 = iff_mp(d, iff_left, iff_right, iff, ready);
                    let low = d.int_eq_rewrite(diff, cc, dbl_rev, low0, &|d, x| {
                        let neg_m = d.ineg(m);
                        d.ile(neg_m, x)
                    });

                    let low_ty = d.ile(neg_m, cc);
                    let high_ty = d.ile(cc, m);
                    let bounds = and_intro(d, low_ty, high_ty, low, high);
                    let congruent = super::two_squares::imodeq(d, m, c, a);
                    let bounds_ty = d.and(low_ty, high_ty);
                    let payload = and_intro(d, congruent, bounds_ty, hmod2, bounds);
                    let predicate = centered_predicate(d, a, m);
                    int_exists_intro(d, predicate, c, payload)
                },
            )
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// the strict decrease
// ============================================================================

/// `Int.two_mul_sq_add_sq_le_sq : ∀ m c e,`
/// `  le (neg m) (add c c) → le (add c c) m →`
/// `  le (neg m) (add e e) → le (add e e) m →`
/// `  le (add S S) (mul m m)`, with `S := c*c + e*e`
/// — the **multiplied-through** form of `c² + e² ≤ m²/2`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_two_mul_sq_add_sq_le_sq(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.two_mul_sq_add_sq_le_sq, 3, &|d, v| {
        let (m, c, e) = (v[0], v[1], v[2]);
        let (stmt, hyp_tys, concl) = bounded_statement(d, m, c, e, &|d, m, c, e| {
            let s = measure(d, c, e);
            let ss = d.iadd(s, s);
            let mm = d.imul(m, m);
            d.ile(ss, mm)
        });

        let proof = with_hypotheses(d, &hyp_tys, &|d, h| {
            let cc2 = d.iadd(c, c);
            let ee2 = d.iadd(e, e);
            let sq_c = d.imul(cc2, cc2);
            let sq_e = d.imul(ee2, ee2);
            let mm = d.imul(m, m);
            let a = d.const_app(p.sq_le_sq_of_neg_le_of_le, &[cc2, m, h[0], h[1]]);
            let b = d.const_app(p.sq_le_sq_of_neg_le_of_le, &[ee2, m, h[2], h[3]]);
            let both = d.const_app(p.add_le_add, &[sq_c, mm, sq_e, mm, a, b]);
            let sum_sq = d.iadd(sq_c, sq_e);
            let s = measure(d, c, e);
            let ss = d.iadd(s, s);
            let ssss = d.iadd(ss, ss);
            let expand = d.const_app(p.sq_double_add_sq_double, &[c, e]);
            let folded = d.int_eq_rewrite(sum_sq, ssss, expand, both, &|d, x| {
                let mm = d.imul(m, m);
                let doubled = d.iadd(mm, mm);
                d.ile(x, doubled)
            });
            d.const_app(p.le_of_add_le_add_self, &[ss, mm, folded])
        });
        let _ = concl;
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.sq_add_sq_lt_sq_of_bounds : ∀ m c e, lt zero m → (the four bounds) →`
/// `  lt (add (mul c c) (mul e e)) (mul m m)`
/// — **the strict decrease**. `0 < m` is the only positivity needed; `1 < m` is
/// not required, because the strictness comes from the halving and not from a
/// gap between `m` and `1`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sq_add_sq_lt_sq_of_bounds(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.sq_add_sq_lt_sq_of_bounds, 3, &|d, v| {
        let (m, c, e) = (v[0], v[1], v[2]);
        let zero = d.izero();
        let pos = d.ilt(zero, m);
        let (inner, hyp_tys, _) = bounded_statement(d, m, c, e, &|d, m, c, e| {
            let s = measure(d, c, e);
            let mm = d.imul(m, m);
            d.ilt(s, mm)
        });
        let stmt = d.arrow(pos, inner);

        let proof = with_hyp(d, pos, &|d, hm| {
            with_hypotheses(d, &hyp_tys, &|d, h| {
                let s = measure(d, c, e);
                let ss = d.iadd(s, s);
                let mm = d.imul(m, m);
                let hss = d.const_app(
                    p.two_mul_sq_add_sq_le_sq,
                    &[m, c, e, h[0], h[1], h[2], h[3]],
                );
                let cc = d.imul(c, c);
                let ee = d.imul(e, e);
                let hcc = d.const_app(p.sq_nonneg, &[c]);
                let hee = d.const_app(p.sq_nonneg, &[e]);
                let hs0 = d.const_app(p.add_nonneg, &[cc, ee, hcc, hee]);

                // `S <= S + S <= m*m`.
                let zero = d.izero();
                let grow = d.const_app(p.add_le_add_left, &[zero, s, s, hs0]);
                let s_zero = d.iadd(s, zero);
                let drop = d.const_app(p.add_zero, &[s]);
                let s_le_ss = d.int_eq_rewrite(s_zero, s, drop, grow, &|d, x| {
                    let s = measure(d, c, e);
                    let ss = d.iadd(s, s);
                    d.ile(x, ss)
                });
                let hle = le_trans(d, s, ss, mm, s_le_ss, hss);

                // `S != m*m`: otherwise `S + S <= S`, so `S <= 0`, so `S = 0`,
                // so `m*m = 0`, contradicting `0 < m*m`.
                let eq_ty = d.ieq(s, mm);
                let hne = with_hyp(d, eq_ty, &|d, heq| {
                    let zero = d.izero();
                    let s = measure(d, c, e);
                    let ss = d.iadd(s, s);
                    let mm = d.imul(m, m);
                    let heq_rev = d.isymm(s, mm, heq);
                    let t1 = d.int_eq_rewrite(mm, s, heq_rev, hss, &|d, x| {
                        let s = measure(d, c, e);
                        let ss = d.iadd(s, s);
                        d.ile(ss, x)
                    });
                    let s_zero = d.iadd(s, zero);
                    let drop = d.const_app(p.add_zero, &[s]);
                    let drop_rev = d.isymm(s_zero, s, drop);
                    let t2 = d.int_eq_rewrite(s, s_zero, drop_rev, t1, &|d, x| {
                        let s = measure(d, c, e);
                        let ss = d.iadd(s, s);
                        d.ile(ss, x)
                    });
                    let iff = d.const_app(p.add_le_add_iff_left, &[s, s, zero]);
                    let iff_left = d.ile(ss, s_zero);
                    let iff_right = d.ile(s, zero);
                    let t3 = iff_mp(d, iff_left, iff_right, iff, t2);
                    let s_zero_eq = d.const_app(p.le_antisymm, &[s, zero, t3, hs0]);
                    let positive = d.const_app(p.mul_pos, &[m, m, hm, hm]);
                    let p1 = d.int_eq_rewrite(mm, s, heq_rev, positive, &|d, x| {
                        let zero = d.izero();
                        d.ilt(zero, x)
                    });
                    let p2 = d.int_eq_rewrite(s, zero, s_zero_eq, p1, &|d, x| {
                        let zero = d.izero();
                        d.ilt(zero, x)
                    });
                    lt_irrefl_absurd(d, zero, p2)
                });
                d.const_app(p.lt_of_le_of_ne, &[s, mm, hle, hne])
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.lt_of_add_le_of_nonneg : ∀ m q, lt zero m → le zero q → le (add q q) m →`
/// `  lt q m` — the descent's termination step: a non-negative `q` whose double
/// fits under a positive `m` is strictly below `m`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_lt_of_add_le_of_nonneg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.lt_of_add_le_of_nonneg, 2, &|d, v| {
        let (m, q) = (v[0], v[1]);
        let zero = d.izero();
        let pos = d.ilt(zero, m);
        let nonneg = d.ile(zero, q);
        let qq = d.iadd(q, q);
        let bound = d.ile(qq, m);
        let concl = d.ilt(q, m);
        let stmt = {
            let t3 = d.arrow(bound, concl);
            let t2 = d.arrow(nonneg, t3);
            d.arrow(pos, t2)
        };

        let proof = with_hyp(d, pos, &|d, hm| {
            let nonneg = {
                let zero = d.izero();
                d.ile(zero, q)
            };
            with_hyp(d, nonneg, &|d, hq0| {
                let bound = {
                    let qq = d.iadd(q, q);
                    d.ile(qq, m)
                };
                with_hyp(d, bound, &|d, h| {
                    let zero = d.izero();
                    let qq = d.iadd(q, q);
                    let grow = d.const_app(p.add_le_add_left, &[zero, q, q, hq0]);
                    let q_zero = d.iadd(q, zero);
                    let drop = d.const_app(p.add_zero, &[q]);
                    let q_le_qq = d.int_eq_rewrite(q_zero, q, drop, grow, &|d, x| {
                        let qq = d.iadd(q, q);
                        d.ile(x, qq)
                    });
                    let hle = le_trans(d, q, qq, m, q_le_qq, h);

                    let eq_ty = d.ieq(q, m);
                    let hne = with_hyp(d, eq_ty, &|d, heq| {
                        let zero = d.izero();
                        let mm = d.iadd(m, m);
                        let t1 = d.int_eq_rewrite(q, m, heq, h, &|d, x| {
                            let doubled = d.iadd(x, x);
                            d.ile(doubled, m)
                        });
                        let m_zero = d.iadd(m, zero);
                        let drop = d.const_app(p.add_zero, &[m]);
                        let drop_rev = d.isymm(m_zero, m, drop);
                        let t2 = d.int_eq_rewrite(m, m_zero, drop_rev, t1, &|d, x| {
                            let mm = d.iadd(m, m);
                            d.ile(mm, x)
                        });
                        let iff = d.const_app(p.add_le_add_iff_left, &[m, m, zero]);
                        let iff_left = d.ile(mm, m_zero);
                        let iff_right = d.ile(m, zero);
                        let t3 = iff_mp(d, iff_left, iff_right, iff, t2);
                        let bad = d.const_app(p.lt_of_lt_of_le, &[zero, m, zero, hm, t3]);
                        lt_irrefl_absurd(d, zero, bad)
                    });
                    d.const_app(p.lt_of_le_of_ne, &[q, m, hle, hne])
                })
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// shared shapes
// ============================================================================

/// `mul c c + mul e e` — the descent's measure.
fn measure(d: &mut IntDev<'_>, c: ExprId, e: ExprId) -> ExprId {
    let cc = d.imul(c, c);
    let ee = d.imul(e, e);
    d.iadd(cc, ee)
}

/// The four-hypothesis telescope
/// `−m ≤ c+c → c+c ≤ m → −m ≤ e+e → e+e ≤ m → concl`, together with the
/// hypothesis types in order and the conclusion.
fn bounded_statement(
    d: &mut IntDev<'_>,
    m: ExprId,
    c: ExprId,
    e: ExprId,
    concl: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
) -> (ExprId, Vec<ExprId>, ExprId) {
    let neg_m = d.ineg(m);
    let cc = d.iadd(c, c);
    let ee = d.iadd(e, e);
    let h0 = d.ile(neg_m, cc);
    let h1 = d.ile(cc, m);
    let h2 = d.ile(neg_m, ee);
    let h3 = d.ile(ee, m);
    let target = concl(d, m, c, e);
    let mut stmt = target;
    for &hyp in [h3, h2, h1, h0].iter() {
        stmt = d.arrow(hyp, stmt);
    }
    (stmt, vec![h0, h1, h2, h3], target)
}

/// `fun (h_0 : tys[0]) … (h_{n-1} : tys[n-1]) => body(h_0, …)`.
fn with_hypotheses(
    d: &mut IntDev<'_>,
    tys: &[ExprId],
    body: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> ExprId {
    let fvs: Vec<u64> = (0..tys.len()).map(|_| d.fresh_fvar()).collect();
    let hypotheses: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let mut term = body(d, &hypotheses);
    for (index, &fv) in fvs.iter().enumerate().rev() {
        term = d.lam_fv(fv, tys[index], term);
    }
    term
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
pub(super) fn declare_order_squares_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_ne_zero_of_pos(d)?;
    declare_neg_nonpos_of_nonneg(d)?;
    declare_neg_nonneg_of_nonpos(d)?;
    declare_neg_le_of_neg_le(d)?;
    declare_add_nonneg(d)?;
    declare_sub_nonpos_of_le(d)?;
    declare_le_of_add_le_add_self(d)?;
    declare_le_of_mul_le_mul_left(d)?;
    declare_neg_mul_neg(d)?;
    declare_neg_add_self_self(d)?;
    declare_add_sub_add_sub(d)?;
    declare_sq_double_add_sq_double(d)?;
    declare_sq_le_sq_of_nonneg(d)?;
    declare_sq_le_sq_of_neg_le_of_le(d)?;
    declare_exists_centered_representative(d)?;
    declare_two_mul_sq_add_sq_le_sq(d)?;
    declare_sq_add_sq_lt_sq_of_bounds(d)?;
    declare_lt_of_add_le_of_nonneg(d)?;
    Ok(())
}
