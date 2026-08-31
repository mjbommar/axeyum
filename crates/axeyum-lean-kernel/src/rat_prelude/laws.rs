//! The **22 ordered-commutative-ring laws** over `ℚ`, and the bridges they run
//! on.
//!
//! Every law here is one of two shapes:
//!
//! - an **order** law, which unfolds to an `Int.le`/`Int.lt` between
//!   cross-products. Scale by the third denominator, permute the factors, apply
//!   the corresponding `Int` law, cancel the common positive factor. The
//!   cancellation is what makes this faithful rather than merely suggestive:
//!   `Rat.le` is *defined* by cross-multiplication, so the reverse direction has
//!   to be available or the definition would be one-way.
//! - a **ring** law, which is an equation between two `Rat.normalize` calls, and
//!   therefore an application of [`super::core`]'s `normalize_congr` or
//!   `eq_of_cross` to an identity in the constructed `ℤ`.
//!
//! Nothing here is definitional. `Rat.add` and `Rat.mul` renormalise, so even
//! `add_comm` — whose two sides differ only by `Int.add_comm` and `Nat.mul_comm`
//! — has to be routed through the uniqueness of the reduced representative.

use super::RatPrelude;
use super::ops::{
    den, den_pos, den_z, int_eq_to_nat, iregroup3, normalize, num, radd, rat_theorem, rchain,
    rcongr, req, rle, rlt, rmul, rzero,
};
use super::statements;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, Shape, case_split};
use crate::nat_prelude::NatOps;

/// The two small `ℤ` facts and the two `Rat`/`ℤ` bridges the laws below need.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bridges(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;

    // int_right_distrib : (a+b)*c = a*c + b*c.
    //
    // `Int.add_mul` (`int_prelude/add_basics.rs`) states this identical
    // proposition -- same chain, `mul_comm` thrice plus `left_distrib` once --
    // and was an independent re-derivation of it, reported as a NEW duplicate
    // group by `shape_search --duplicates` the first time
    // `scripts/check-shape-duplicates.py` was ever run automatically
    // (2026-08-31, ADR-1170). This name stays because 20 call sites across
    // `rat_prelude/` and `creal/sqrt.rs` reference it, but the proof term is
    // now shared rather than duplicated: one proof, two names.
    d.int_theorem(p.int_right_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let sum = d.iadd(a, b);
        let left = d.imul(sum, c);
        let first = d.imul(a, c);
        let second = d.imul(b, c);
        let right = d.iadd(first, second);
        let stmt = d.ieq(left, right);
        let proof = d.lemma(int.add_mul, &[a, b, c]);
        (stmt, proof)
    })?;

    // int_zero_mul : Int.zero * a = Int.zero.
    d.int_theorem(p.int_zero_mul, 1, &|d, v| {
        let a = v[0];
        let zero = d.izero();
        let left = d.imul(zero, a);
        let stmt = d.ieq(left, zero);
        let flipped = d.imul(a, zero);
        let commute = d.lemma(int.mul_comm, &[zero, a]);
        let collapse = d.lemma(int.mul_zero, &[a]);
        let (_, proof) = d.ichain(left, &[(flipped, commute), (zero, collapse)]);
        (stmt, proof)
    })?;

    // eq_zero_of_num_zero : num q = 0 → q = 0.
    // `Rat.zero` has numerator `ofNat 0` and denominator `1`, so the cross
    // equation is `num q * 1 = 0 * den q`, i.e. `num q = 0` on both sides.
    rat_theorem(d, p.eq_zero_of_num_zero, 1, &|d, v| {
        let q = v[0];
        let numerator = num(d, q);
        let zero = d.izero();
        let hypothesis = d.ieq(numerator, zero);
        let target = rzero(d, p);
        let conclusion = req(d, q, target);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let unit = d.ione();
        let scaled = d.imul(numerator, unit);
        let unscale = d.lemma(int.mul_one, &[numerator]);
        let (_, left_side) = d.ichain(scaled, &[(numerator, unscale), (zero, h)]);
        let denominator = den_z(d, q);
        let right_scaled = d.imul(zero, denominator);
        let right_side = d.lemma(p.int_zero_mul, &[denominator]);
        let cross = {
            let back = d.isymm(right_scaled, zero, right_side);
            d.itrans(scaled, zero, right_scaled, left_side, back)
        };
        let body = d.const_app(p.eq_of_cross, &[q, target, cross]);
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })?;

    // The two directions of "0 ≤ q iff 0 ≤ num q".
    // `Rat.le 0 q` unfolds to `Int.le (0 · den q) (num q · 1)`; the two sides
    // collapse by `int_zero_mul` and `Int.mul_one`.
    let bridge = |d: &mut IntDev<'_>, name, forward: bool| -> Result<(), KernelError> {
        rat_theorem(d, name, 1, &|d, v| {
            let q = v[0];
            let numerator = num(d, q);
            let zero = d.izero();
            let unit = d.ione();
            let denominator = den_z(d, q);
            let rational = {
                let target = rzero(d, p);
                rle(d, p, target, q)
            };
            let integral = d.ile(zero, numerator);
            let stmt = if forward {
                d.arrow(rational, integral)
            } else {
                d.arrow(integral, rational)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            // `0 · den q = 0` and `num q · 1 = num q`.
            let left_collapse = d.lemma(p.int_zero_mul, &[denominator]);
            let right_collapse = d.lemma(int.mul_one, &[numerator]);
            let left_scaled = d.imul(zero, denominator);
            let right_scaled = d.imul(numerator, unit);
            let body = if forward {
                let at_left = d.int_eq_rewrite(left_scaled, zero, left_collapse, h, &|d, x| {
                    d.ile(x, right_scaled)
                });
                d.int_eq_rewrite(right_scaled, numerator, right_collapse, at_left, &|d, x| {
                    d.ile(zero, x)
                })
            } else {
                let back_left = d.isymm(left_scaled, zero, left_collapse);
                let back_right = d.isymm(right_scaled, numerator, right_collapse);
                let at_left =
                    d.int_eq_rewrite(zero, left_scaled, back_left, h, &|d, x| d.ile(x, numerator));
                d.int_eq_rewrite(numerator, right_scaled, back_right, at_left, &|d, x| {
                    d.ile(left_scaled, x)
                })
            };
            let hypothesis = if forward { rational } else { integral };
            let proof = d.lam_fv(h_fv, hypothesis, body);
            (stmt, proof)
        })
    };
    bridge(d, p.int_nonneg_of_nonneg, true)?;
    bridge(d, p.nonneg_of_int_nonneg, false)
}

/// `natAbs x = 0 → x = 0`, instantiated at a specific `x`.
///
/// Not interned as its own theorem: [`declare_order_laws`]'s `mul_eq_zero` is
/// its only call site, applied once to `num a` and once to `num b`. Case-split
/// on `x`'s sign — `natAbs (ofNat n)` **is** `n` by computation, so the
/// `ofNat` branch is congruence on the hypothesis; `natAbs (negSucc n)` **is**
/// `succ n`, so the `negSucc` branch's hypothesis is `succ n = 0`, refuted by
/// `Nat.succ_ne_zero`.
fn int_eq_zero_of_nat_abs_eq_zero(d: &mut IntDev<'_>, x: ExprId, h: ExprId) -> ExprId {
    let int = d.int();
    let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
        let y = args[0];
        let magnitude = d.const_app(int.nat_abs, &[y]);
        let zero_nat = d.zero();
        let hypothesis = d.eq(magnitude, zero_nat);
        let zero_int = d.izero();
        let conclusion = d.ieq(y, zero_int);
        d.arrow(hypothesis, conclusion)
    };
    let implication = case_split(d, &[x], &statement, &|d, b| {
        let n = b[0].1;
        match b[0].0 {
            Shape::OfNat => {
                let h_fv = d.fresh_fvar();
                let hh = d.kernel().fvar(h_fv);
                let zero_nat = d.zero();
                let hyp_ty = d.eq(n, zero_nat);
                let lifted = d.nat_eq_to_int(n, zero_nat, hh, &|d, t| d.of_nat(t));
                d.lam_fv(h_fv, hyp_ty, lifted)
            }
            Shape::NegSucc => {
                let h_fv = d.fresh_fvar();
                let hh = d.kernel().fvar(h_fv);
                let succ_n = d.succ(n);
                let zero_nat = d.zero();
                let hyp_ty = d.eq(succ_n, zero_nat);
                let value = d.neg_succ(n);
                let zero_int = d.izero();
                let goal = d.ieq(value, zero_int);
                let ne = d.lemma(int.nat.succ_ne_zero, &[n]);
                let false_proof = d.apply(ne, &[hh]);
                let body = d.absurd(goal, false_proof);
                d.lam_fv(h_fv, hyp_ty, body)
            }
        }
    });
    d.apply(implication, &[h])
}

/// The order laws: reflexivity, irreflexivity, the four transitivity shapes,
/// weakening, and `0 < 1`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_order_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_bridges(d, p)?;
    let int = p.int;

    // The cross-product `num a · ofNat (den b)` that `Rat.le a b` compares.
    let cross = |d: &mut IntDev<'_>, a: ExprId, b: ExprId| -> ExprId {
        let numerator = num(d, a);
        let scale = den_z(d, b);
        d.imul(numerator, scale)
    };

    rat_theorem(d, p.le_refl, 1, &|d, v| {
        let stmt = statements::le_refl(d, p, v);
        let side = cross(d, v[0], v[0]);
        let proof = d.lemma(int.le_refl, &[side]);
        (stmt, proof)
    })?;

    rat_theorem(d, p.lt_irrefl, 1, &|d, v| {
        let stmt = statements::lt_irrefl(d, p, v);
        let side = cross(d, v[0], v[0]);
        let proof = d.lemma(int.lt_irrefl, &[side]);
        (stmt, proof)
    })?;

    rat_theorem(d, p.le_of_lt, 2, &|d, v| {
        let stmt = statements::le_of_lt(d, p, v);
        let left = cross(d, v[0], v[1]);
        let right = cross(d, v[1], v[0]);
        let proof = d.lemma(int.le_of_lt, &[left, right]);
        (stmt, proof)
    })?;

    rat_theorem(d, p.zero_lt_one, 0, &|d, v| {
        let stmt = statements::zero_lt_one(d, p, v);
        // `0/1 < 1/1` unfolds to `Int.lt (ofNat 0 · ofNat 1) (ofNat 1 · ofNat 1)`,
        // and both products COMPUTE: `Int.zero < Int.one`.
        let proof = d.kernel().const_(int.zero_lt_one, vec![]);
        (stmt, proof)
    })?;

    // The four transitivity shapes, all the same argument: scale each
    // hypothesis by the denominator it is missing, permute the three factors so
    // the two scaled bounds share a middle term, chain, then cancel `den b`.
    let transitive = |d: &mut IntDev<'_>,
                      name,
                      statement: &dyn Fn(&mut IntDev<'_>, RatPrelude, &[ExprId]) -> ExprId,
                      strict_first: bool,
                      strict_second: bool|
     -> Result<(), KernelError> {
        rat_theorem(d, name, 3, &|d, v| {
            let (a, b, c) = (v[0], v[1], v[2]);
            let stmt = statement(d, p, v);
            let na = num(d, a);
            let nb = num(d, b);
            let nc = num(d, c);
            let scale_a = den_z(d, a);
            let scale_b = den_z(d, b);
            let scale_c = den_z(d, c);
            let raw_a = den(d, a);
            let raw_b = den(d, b);
            let raw_c = den(d, c);
            let positive_a = den_pos(d, a);
            let positive_b = den_pos(d, b);
            let positive_c = den_pos(d, c);

            let first_ty = {
                let left = d.imul(na, scale_b);
                let right = d.imul(nb, scale_a);
                if strict_first {
                    d.ilt(left, right)
                } else {
                    d.ile(left, right)
                }
            };
            let second_ty = {
                let left = d.imul(nb, scale_c);
                let right = d.imul(nc, scale_b);
                if strict_second {
                    d.ilt(left, right)
                } else {
                    d.ile(left, right)
                }
            };
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let ab = d.imul(na, scale_b);
            let ba = d.imul(nb, scale_a);
            let bc = d.imul(nb, scale_c);
            let cb = d.imul(nc, scale_b);
            let scaled_first = if strict_first {
                d.lemma(p.int_mul_lt_mul_right, &[ab, ba, raw_c, positive_c, h1])
            } else {
                d.lemma(p.int_mul_le_mul_right, &[ab, ba, raw_c, h1])
            };
            let scaled_second = if strict_second {
                d.lemma(p.int_mul_lt_mul_right, &[bc, cb, raw_a, positive_a, h2])
            } else {
                d.lemma(p.int_mul_le_mul_right, &[bc, cb, raw_a, h2])
            };

            let relate = |d: &mut IntDev<'_>, left: ExprId, right: ExprId| -> ExprId {
                if strict_first || strict_second {
                    d.ilt(left, right)
                } else {
                    d.ile(left, right)
                }
            };
            let from_left = {
                let head = d.imul(ab, scale_c);
                let _ = head;
                iregroup3(d, [na, scale_b, scale_c], [na, scale_c, scale_b])
            };
            let from_middle = iregroup3(d, [nb, scale_a, scale_c], [nb, scale_c, scale_a]);
            let from_right = iregroup3(d, [nc, scale_b, scale_a], [nc, scale_a, scale_b]);

            let old_left = d.imul(ab, scale_c);
            let ac = d.imul(na, scale_c);
            let new_left = d.imul(ac, scale_b);
            let old_middle = d.imul(ba, scale_c);
            let new_middle = d.imul(bc, scale_a);
            let old_right = d.imul(cb, scale_a);
            let ca = d.imul(nc, scale_a);
            let new_right = d.imul(ca, scale_b);

            let first_aligned = {
                let relation = if strict_first {
                    |d: &mut IntDev<'_>, x: ExprId, y: ExprId| d.ilt(x, y)
                } else {
                    |d: &mut IntDev<'_>, x: ExprId, y: ExprId| d.ile(x, y)
                };
                let staged =
                    d.int_eq_rewrite(old_left, new_left, from_left, scaled_first, &|d, x| {
                        relation(d, x, old_middle)
                    });
                d.int_eq_rewrite(old_middle, new_middle, from_middle, staged, &|d, x| {
                    relation(d, new_left, x)
                })
            };
            let second_aligned = {
                let relation = if strict_second {
                    |d: &mut IntDev<'_>, x: ExprId, y: ExprId| d.ilt(x, y)
                } else {
                    |d: &mut IntDev<'_>, x: ExprId, y: ExprId| d.ile(x, y)
                };
                d.int_eq_rewrite(old_right, new_right, from_right, scaled_second, &|d, x| {
                    relation(d, new_middle, x)
                })
            };

            let joined = match (strict_first, strict_second) {
                (false, false) => d.lemma(
                    int.le_trans,
                    &[
                        new_left,
                        new_middle,
                        new_right,
                        first_aligned,
                        second_aligned,
                    ],
                ),
                (true, true) => d.lemma(
                    int.lt_trans,
                    &[
                        new_left,
                        new_middle,
                        new_right,
                        first_aligned,
                        second_aligned,
                    ],
                ),
                (true, false) => d.lemma(
                    int.lt_of_lt_of_le,
                    &[
                        new_left,
                        new_middle,
                        new_right,
                        first_aligned,
                        second_aligned,
                    ],
                ),
                (false, true) => d.lemma(
                    int.lt_of_le_of_lt,
                    &[
                        new_left,
                        new_middle,
                        new_right,
                        first_aligned,
                        second_aligned,
                    ],
                ),
            };
            let _ = relate;
            let cancelled = if strict_first || strict_second {
                d.lemma(
                    p.int_lt_of_mul_lt_mul_right,
                    &[ac, ca, raw_b, positive_b, joined],
                )
            } else {
                d.lemma(
                    p.int_le_of_mul_le_mul_right,
                    &[ac, ca, raw_b, positive_b, joined],
                )
            };
            let proof = {
                let with_second = d.lam_fv(h2_fv, second_ty, cancelled);
                d.lam_fv(h1_fv, first_ty, with_second)
            };
            (stmt, proof)
        })
    };
    transitive(d, p.le_trans, &statements::le_trans, false, false)?;
    transitive(d, p.lt_trans, &statements::lt_trans, true, true)?;
    transitive(
        d,
        p.lt_of_lt_of_le,
        &statements::lt_of_lt_of_le,
        true,
        false,
    )?;
    transitive(
        d,
        p.lt_of_le_of_lt,
        &statements::lt_of_le_of_lt,
        false,
        true,
    )?;

    // `le_total` and `lt_of_not_le` are NOT among the 22 — the `Real` package
    // assumes neither, so they are properties ℚ has that the axiomatization
    // does not name. Both are the corresponding `Int` fact read through the
    // cross-multiplication definition, which is why they cost nothing.
    rat_theorem(d, p.le_total, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let forward = rle(d, p, a, b);
        let backward = rle(d, p, b, a);
        let stmt = d.or(forward, backward);
        let left = cross(d, a, b);
        let right = cross(d, b, a);
        let proof = d.lemma(int.le_total, &[left, right]);
        (stmt, proof)
    })?;

    // `¬(a ≤ b) → b < a`. By `Int.le_total`: the `a ≤ b` branch contradicts the
    // hypothesis outright, and in the other branch the two cross-products
    // cannot be EQUAL — equality would give `a ≤ b` back through `le_refl`.
    rat_theorem(d, p.lt_of_not_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ordered = rle(d, p, a, b);
        let hypothesis = d.not(ordered);
        let conclusion = rlt(d, p, b, a);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let left = cross(d, a, b);
        let right = cross(d, b, a);
        let forward = d.ile(left, right);
        let backward = d.ile(right, left);
        let total = d.lemma(int.le_total, &[left, right]);
        let body = d.or_elim(
            forward,
            backward,
            conclusion,
            total,
            &|d, ordered_proof| {
                let impossible = d.apply(h, &[ordered_proof]);
                d.absurd(conclusion, impossible)
            },
            &|d, reversed| {
                let distinct = {
                    let equal = d.ieq(right, left);
                    let e_fv = d.fresh_fvar();
                    let e = d.kernel().fvar(e_fv);
                    let reflexive = d.lemma(int.le_refl, &[left]);
                    let flipped = d.isymm(right, left, e);
                    let recovered =
                        d.int_eq_rewrite(left, right, flipped, reflexive, &|d, x| d.ile(left, x));
                    let impossible = d.apply(h, &[recovered]);
                    d.lam_fv(e_fv, equal, impossible)
                };
                d.lemma(int.lt_of_le_of_ne, &[right, left, reversed, distinct])
            },
        );
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })?;

    // le_antisymm : ∀ a b, le a b → le b a → a = b.
    //
    // Also not one of the 22, and also missing until now: `le a b` and
    // `le b a` unfold to `Int.le x y` and `Int.le y x` at the same two cross-
    // products `eq_of_cross` already asks for, so `Int.le_antisymm` applied to
    // them gives exactly its hypothesis.
    rat_theorem(d, p.le_antisymm, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp1 = rle(d, p, a, b);
        let hyp2 = rle(d, p, b, a);
        let conclusion = req(d, a, b);
        let inner = d.arrow(hyp2, conclusion);
        let stmt = d.arrow(hyp1, inner);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let x = cross(d, a, b);
        let y = cross(d, b, a);
        let cross_eq = d.lemma(int.le_antisymm, &[x, y, h1, h2]);
        let body = d.lemma(p.eq_of_cross, &[a, b, cross_eq]);

        let value = d.lam_fv(h2_fv, hyp2, body);
        let proof = d.lam_fv(h1_fv, hyp1, value);
        (stmt, proof)
    })?;

    // mul_eq_zero : ∀ a b, a*b = 0 → Or (a=0) (b=0) — `ℚ` has no zero
    // divisors.
    //
    // `Rat.mul` normalises, so `num (a*b)` is not literally `num a * num b`.
    // `cross_of_eq` at `(a*b, 0)` collapses, via `Int.mul_one` and
    // `int_zero_mul` (the same computation `eq_zero_of_num_zero` runs in
    // reverse), to `num (a*b) = 0` outright. Substituting that into
    // `mul_cross` and cancelling the positive denominator `den (a*b)` with
    // `int_mul_right_cancel` lands on the clean integer fact
    // `num a * num b = 0`, with every denominator gone. From there
    // `Int.natAbs` and `Nat.mul_eq_zero` decide which numerator vanishes, and
    // `eq_zero_of_num_zero` lifts the winning branch back to `ℚ`.
    rat_theorem(d, p.mul_eq_zero, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = rmul(d, a, b);
        let target = rzero(d, p);
        let hypothesis = req(d, ab, target);
        let left = req(d, a, target);
        let right = req(d, b, target);
        let goal = d.or(left, right);
        let stmt = d.arrow(hypothesis, goal);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // num (a*b) = 0.
        let num_ab = num(d, ab);
        let zero_int = d.izero();
        let unit = d.ione();
        let den_ab_z = den_z(d, ab);
        let cross = d.lemma(p.cross_of_eq, &[ab, target, h]);
        let scaled_num_ab = d.imul(num_ab, unit);
        let unscale = d.lemma(int.mul_one, &[num_ab]);
        let num_ab_eq_scaled = d.isymm(scaled_num_ab, num_ab, unscale);
        let right_scaled = d.imul(zero_int, den_ab_z);
        let num_ab_eq_right_scaled =
            d.itrans(num_ab, scaled_num_ab, right_scaled, num_ab_eq_scaled, cross);
        let collapse_right = d.lemma(p.int_zero_mul, &[den_ab_z]);
        let num_ab_eq_zero = d.itrans(
            num_ab,
            right_scaled,
            zero_int,
            num_ab_eq_right_scaled,
            collapse_right,
        );

        // num a * num b = 0, via mul_cross and cancelling den (a*b).
        let num_a = num(d, a);
        let num_b = num(d, b);
        let prod = d.imul(num_a, num_b);
        let den_ab = den(d, ab);
        let den_ab_z2 = d.of_nat(den_ab);
        let scale = {
            let da = den(d, a);
            let db = den(d, b);
            let combined = NatOps::mul(d, da, db);
            d.of_nat(combined)
        };
        let mc = d.lemma(p.mul_cross, &[a, b]);
        let step2 = d.int_eq_rewrite(num_ab, zero_int, num_ab_eq_zero, mc, &|d, x| {
            let l = d.imul(x, scale);
            let r = d.imul(prod, den_ab_z2);
            d.ieq(l, r)
        });
        let prod_scaled = d.imul(prod, den_ab_z2);
        let right_scaled2 = d.imul(zero_int, scale);
        let collapse_scale = d.lemma(p.int_zero_mul, &[scale]);
        let back_collapse_scale = d.isymm(right_scaled2, zero_int, collapse_scale);
        let (_, zero_eq_prod_scaled) = d.ichain(
            zero_int,
            &[(right_scaled2, back_collapse_scale), (prod_scaled, step2)],
        );
        let prod_scaled_eq_zero = d.isymm(zero_int, prod_scaled, zero_eq_prod_scaled);
        let right_scaled_den = d.imul(zero_int, den_ab_z2);
        let collapse_scale2 = d.lemma(p.int_zero_mul, &[den_ab_z2]);
        let zero_eq_scaled2 = d.isymm(right_scaled_den, zero_int, collapse_scale2);
        let h_cancel = d.itrans(
            prod_scaled,
            zero_int,
            right_scaled_den,
            prod_scaled_eq_zero,
            zero_eq_scaled2,
        );
        let den_ab_pos = den_pos(d, ab);
        let numerators_eq = d.lemma(
            p.int_mul_right_cancel,
            &[prod, zero_int, den_ab, den_ab_pos, h_cancel],
        );

        // natAbs a * natAbs b = 0, hence one of them is 0 (Nat.mul_eq_zero).
        let magnitude_a = d.const_app(int.nat_abs, &[num_a]);
        let magnitude_b = d.const_app(int.nat_abs, &[num_b]);
        let magnitude_prod = d.const_app(int.nat_abs, &[prod]);
        let magnitude_eq = int_eq_to_nat(d, prod, zero_int, numerators_eq, &|d, y| {
            d.const_app(int.nat_abs, &[y])
        });
        let split = d.lemma(int.nat_abs_mul, &[num_a, num_b]);
        let nat_prod = NatOps::mul(d, magnitude_a, magnitude_b);
        let back_split = d.symm(magnitude_prod, nat_prod, split);
        let zero_nat = d.zero();
        let (_, nat_prod_eq_zero) = d.chain(
            nat_prod,
            &[(magnitude_prod, back_split), (zero_nat, magnitude_eq)],
        );
        let disjunction = d.lemma(
            int.nat.mul_eq_zero,
            &[magnitude_a, magnitude_b, nat_prod_eq_zero],
        );

        // Lift the winning branch back to ℚ.
        let mag_a_zero = d.eq(magnitude_a, zero_nat);
        let mag_b_zero = d.eq(magnitude_b, zero_nat);
        let body = d.or_elim(
            mag_a_zero,
            mag_b_zero,
            goal,
            disjunction,
            &|d, hma| {
                let num_a_zero = int_eq_zero_of_nat_abs_eq_zero(d, num_a, hma);
                let a_zero = d.const_app(p.eq_zero_of_num_zero, &[a, num_a_zero]);
                d.or_inl(left, right, a_zero)
            },
            &|d, hmb| {
                let num_b_zero = int_eq_zero_of_nat_abs_eq_zero(d, num_b, hmb);
                let b_zero = d.const_app(p.eq_zero_of_num_zero, &[b, num_b_zero]);
                d.or_inr(left, right, b_zero)
            },
        );
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })
}

/// `lt_trichotomy : ∀ a b, Or (lt a b) (Or (a = b) (lt b a))`.
///
/// Separate from [`declare_order_laws`] because it needs
/// [`RatPrelude::le_or_lt`], which is not declared until
/// `archimedean::declare_archimedean` runs — later in `build_rat_prelude`'s
/// pipeline than `declare_order_laws`. [`RatPrelude::le_antisymm`] has no such
/// dependency and stays there.
///
/// Constructive, not classical: `le_or_lt a b` gives `Or(le a b)(lt b a)`. The
/// `lt b a` branch is done. The `le a b` branch asks `le_or_lt b a` again —
/// `Or(le b a)(lt a b)` — and now `le a b ∧ le b a` gives `a = b` by
/// `le_antisymm`, or `lt a b` outright. Two decidable-order splits and one
/// antisymmetry, no double negation anywhere.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_trichotomy(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.lt_trichotomy, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let lt_ab = rlt(d, p, a, b);
        let eq_ab = req(d, a, b);
        let lt_ba = rlt(d, p, b, a);
        let right_or = d.or(eq_ab, lt_ba);
        let stmt = d.or(lt_ab, right_or);

        let le_ab = rle(d, p, a, b);
        let first = d.lemma(p.le_or_lt, &[a, b]);
        let body = d.or_elim(
            le_ab,
            lt_ba,
            stmt,
            first,
            &|d, h_le_ab| {
                let le_ba = rle(d, p, b, a);
                let second = d.lemma(p.le_or_lt, &[b, a]);
                d.or_elim(
                    le_ba,
                    lt_ab,
                    stmt,
                    second,
                    &|d, h_le_ba| {
                        let eq_proof = d.lemma(p.le_antisymm, &[a, b, h_le_ab, h_le_ba]);
                        let inner = d.or_inl(eq_ab, lt_ba, eq_proof);
                        d.or_inr(lt_ab, right_or, inner)
                    },
                    &|d, h_lt_ab| d.or_inl(lt_ab, right_or, h_lt_ab),
                )
            },
            &|d, h_lt_ba| {
                let inner = d.or_inr(eq_ab, lt_ba, h_lt_ba);
                d.or_inr(lt_ab, right_or, inner)
            },
        );
        (stmt, body)
    })
}

/// The ring laws.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_ring_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;

    // add_comm / mul_comm: both sides are `normalize` of inputs that differ by
    // `Int` commutativity in the numerator and `Nat` commutativity in the
    // denominator, so `normalize_congr` closes them.
    let commutative = |d: &mut IntDev<'_>,
                       name,
                       statement: &dyn Fn(&mut IntDev<'_>, RatPrelude, &[ExprId]) -> ExprId,
                       numerator: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
                       swap: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId|
     -> Result<(), KernelError> {
        rat_theorem(d, name, 2, &|d, v| {
            let (a, b) = (v[0], v[1]);
            let stmt = statement(d, p, v);
            let den_a = den(d, a);
            let den_b = den(d, b);
            let positive_a = den_pos(d, a);
            let positive_b = den_pos(d, b);
            let forward_den = NatOps::mul(d, den_a, den_b);
            let backward_den = NatOps::mul(d, den_b, den_a);
            let forward_pos = d.lemma(nat.one_le_mul, &[den_a, den_b, positive_a, positive_b]);
            let backward_pos = d.lemma(nat.one_le_mul, &[den_b, den_a, positive_b, positive_a]);
            let forward_num = numerator(d, a, b);
            let backward_num = numerator(d, b, a);
            let swapped = swap(d, a, b);
            let lifted_backward = d.of_nat(backward_den);
            let lifted_forward = d.of_nat(forward_den);
            let start = d.imul(forward_num, lifted_backward);
            let middle = d.imul(backward_num, lifted_backward);
            let head = d.icongr(forward_num, backward_num, swapped, &|d, t| {
                d.imul(t, lifted_backward)
            });
            let denominators = d.lemma(nat.mul_comm, &[den_b, den_a]);
            let tail = d.nat_eq_to_int(backward_den, forward_den, denominators, &|d, x| {
                let lifted = d.of_nat(x);
                d.imul(backward_num, lifted)
            });
            let target = d.imul(backward_num, lifted_forward);
            let (_, cross) = d.ichain(start, &[(middle, head), (target, tail)]);
            let proof = d.const_app(
                p.normalize_congr,
                &[
                    forward_num,
                    forward_den,
                    forward_pos,
                    backward_num,
                    backward_den,
                    backward_pos,
                    cross,
                ],
            );
            (stmt, proof)
        })
    };
    commutative(
        d,
        p.add_comm,
        &statements::add_comm,
        &|d, a, b| {
            let na = num(d, a);
            let nb = num(d, b);
            let scale_b = den_z(d, b);
            let scale_a = den_z(d, a);
            let first = d.imul(na, scale_b);
            let second = d.imul(nb, scale_a);
            d.iadd(first, second)
        },
        &|d, a, b| {
            let na = num(d, a);
            let nb = num(d, b);
            let scale_b = den_z(d, b);
            let scale_a = den_z(d, a);
            let first = d.imul(na, scale_b);
            let second = d.imul(nb, scale_a);
            d.lemma(int.add_comm, &[first, second])
        },
    )?;
    commutative(
        d,
        p.mul_comm,
        &statements::mul_comm,
        &|d, a, b| {
            let na = num(d, a);
            let nb = num(d, b);
            d.imul(na, nb)
        },
        &|d, a, b| {
            let na = num(d, a);
            let nb = num(d, b);
            d.lemma(int.mul_comm, &[na, nb])
        },
    )?;

    declare_unit_laws(d, p)?;
    declare_sign_laws(d, p)
}

/// `add_zero`, `mul_one`, `mul_zero`, `add_neg` — the laws relating an
/// arbitrary rational to the two constants.
fn declare_unit_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;

    // `q + 0 = q` and `q · 1 = q`, both by `eq_of_cross` after simplifying the
    // combined numerator (`n·1 + 0·d = n`, resp. `n·1 = n`) and the combined
    // denominator (`d·1 = d`).
    let unit_law = |d: &mut IntDev<'_>,
                    name,
                    statement: &dyn Fn(&mut IntDev<'_>, RatPrelude, &[ExprId]) -> ExprId,
                    is_add: bool|
     -> Result<(), KernelError> {
        rat_theorem(d, name, 1, &|d, v| {
            let a = v[0];
            let stmt = statement(d, p, v);
            let unit_rat = if is_add {
                d.kernel().const_(p.zero, vec![])
            } else {
                d.kernel().const_(p.one, vec![])
            };
            let combined = if is_add {
                radd(d, a, unit_rat)
            } else {
                rmul(d, a, unit_rat)
            };
            let na = num(d, a);
            let den_a = den(d, a);
            let scale_a = den_z(d, a);
            let unit_nat = d.num(1);
            let unit_den = NatOps::mul(d, den_a, unit_nat);
            let cross = d.lemma(
                if is_add { p.add_cross } else { p.mul_cross },
                &[a, unit_rat],
            );
            // `d·1 = d`, so the scaled cross equation is the one `eq_of_cross`
            // wants on the left.
            let shrink = d.lemma(nat.mul_one, &[den_a]);
            let combined_num = num(d, combined);
            let aligned_left = d.nat_rewrite(unit_den, den_a, shrink, cross, &|d, x| {
                let lifted = d.of_nat(x);
                let left = d.imul(combined_num, lifted);
                // The right-hand side is whatever the cross lemma states; it is
                // rebuilt below, so only the left factor moves here.
                let unit_int = d.ione();
                let head = d.imul(na, unit_int);
                let source = if is_add {
                    let zero = d.izero();
                    let tail = d.imul(zero, scale_a);
                    d.iadd(head, tail)
                } else {
                    head
                };
                let result_den = den(d, combined);
                let lifted_result = d.of_nat(result_den);
                let right = d.imul(source, lifted_result);
                d.ieq(left, right)
            });
            // `n·1 + 0·d = n` (resp. `n·1 = n`).
            let unit_int = d.ione();
            let head = d.imul(na, unit_int);
            let collapse_head = d.lemma(int.mul_one, &[na]);
            let simplified = if is_add {
                let zero = d.izero();
                let tail = d.imul(zero, scale_a);
                let source = d.iadd(head, tail);
                let staged = d.iadd(na, tail);
                let first = d.icongr(head, na, collapse_head, &|d, t| d.iadd(t, tail));
                let collapse_tail = d.lemma(p.int_zero_mul, &[scale_a]);
                let with_zero = d.iadd(na, zero);
                let second = d.icongr(tail, zero, collapse_tail, &|d, t| d.iadd(na, t));
                let third = d.lemma(int.add_zero, &[na]);
                let (_, chained) =
                    d.ichain(source, &[(staged, first), (with_zero, second), (na, third)]);
                chained
            } else {
                collapse_head
            };
            let source = if is_add {
                let zero = d.izero();
                let tail = d.imul(zero, scale_a);
                d.iadd(head, tail)
            } else {
                head
            };
            let result_den = den(d, combined);
            let lifted_result = d.of_nat(result_den);
            let final_cross = d.int_eq_rewrite(source, na, simplified, aligned_left, &|d, x| {
                let left = d.imul(combined_num, scale_a);
                let right = d.imul(x, lifted_result);
                d.ieq(left, right)
            });
            let proof = d.const_app(p.eq_of_cross, &[combined, a, final_cross]);
            (stmt, proof)
        })
    };
    unit_law(d, p.add_zero, &statements::add_zero, true)?;
    unit_law(d, p.mul_one, &statements::mul_one, false)
}

/// `mul_zero`, `add_neg`, `mul_nonneg`, `sq_nonneg` — everything that reaches a
/// conclusion about the *sign* or the *vanishing* of a rational.
fn declare_sign_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;

    // `q · 0 = 0`: the combined numerator is `n·0 = 0`, so the product's own
    // numerator is zero once the (positive) combined denominator is cancelled.
    rat_theorem(d, p.mul_zero, 1, &|d, v| {
        let a = v[0];
        let stmt = statements::mul_zero(d, p, v);
        let zero_rat = d.kernel().const_(p.zero, vec![]);
        let product = rmul(d, a, zero_rat);
        let na = num(d, a);
        let den_a = den(d, a);
        let positive_a = den_pos(d, a);
        let unit_nat = d.num(1);
        let combined_den = NatOps::mul(d, den_a, unit_nat);
        let combined_positive = {
            let unit_pos = d.lemma(nat.le_refl, &[unit_nat]);
            d.lemma(nat.one_le_mul, &[den_a, unit_nat, positive_a, unit_pos])
        };
        let cross = d.lemma(p.mul_cross, &[a, zero_rat]);
        let zero = d.izero();
        let source = d.imul(na, zero);
        let collapse = d.lemma(int.mul_zero, &[na]);
        let product_num = num(d, product);
        let product_den = den(d, product);
        let lifted_product = d.of_nat(product_den);
        let lifted_combined = d.of_nat(combined_den);
        let scaled = d.imul(product_num, lifted_combined);
        // `num (q·0) · (d·1) = 0 · den (q·0) = 0`.
        let vanishes = d.int_eq_rewrite(source, zero, collapse, cross, &|d, x| {
            let right = d.imul(x, lifted_product);
            d.ieq(scaled, right)
        });
        let collapse_right = d.lemma(p.int_zero_mul, &[lifted_product]);
        let right_scaled = d.imul(zero, lifted_product);
        let reduced = d.itrans(scaled, right_scaled, zero, vanishes, collapse_right);
        // `0 = 0 · (d·1)`, so cancellation applies to both sides.
        let zero_scaled = d.imul(zero, lifted_combined);
        let restore = d.lemma(p.int_zero_mul, &[lifted_combined]);
        let balanced = {
            let back = d.isymm(zero_scaled, zero, restore);
            d.itrans(scaled, zero, zero_scaled, reduced, back)
        };
        let numerator_zero = d.lemma(
            p.int_mul_right_cancel,
            &[product_num, zero, combined_den, combined_positive, balanced],
        );
        let proof = d.const_app(p.eq_zero_of_num_zero, &[product, numerator_zero]);
        (stmt, proof)
    })?;

    // `q + (-q) = 0`: `Rat.neg` keeps the denominator, so the combined
    // numerator is `n·d + (-n)·d = (n + -n)·d = 0`.
    rat_theorem(d, p.add_neg, 1, &|d, v| {
        let a = v[0];
        let stmt = statements::add_neg(d, p, v);
        let negated = super::ops::rneg(d, a);
        let sum = radd(d, a, negated);
        let na = num(d, a);
        let den_a = den(d, a);
        let scale_a = den_z(d, a);
        let positive_a = den_pos(d, a);
        let combined_den = NatOps::mul(d, den_a, den_a);
        let combined_positive = d.lemma(nat.one_le_mul, &[den_a, den_a, positive_a, positive_a]);
        let cross = d.lemma(p.add_cross, &[a, negated]);
        let opposite = d.ineg(na);
        let first = d.imul(na, scale_a);
        let second = d.imul(opposite, scale_a);
        let source = d.iadd(first, second);
        let folded = {
            let expand = d.lemma(p.int_right_distrib, &[na, opposite, scale_a]);
            let factored = {
                let head = d.iadd(na, opposite);
                d.imul(head, scale_a)
            };
            let back = d.isymm(factored, source, expand);
            let cancel = d.lemma(int.add_neg, &[na]);
            let zero = d.izero();
            let head = d.iadd(na, opposite);
            let collapsed = d.icongr(head, zero, cancel, &|d, t| d.imul(t, scale_a));
            let zero_scaled = d.imul(zero, scale_a);
            let vanish = d.lemma(p.int_zero_mul, &[scale_a]);
            let (_, chained) = d.ichain(
                source,
                &[(factored, back), (zero_scaled, collapsed), (zero, vanish)],
            );
            chained
        };
        let zero = d.izero();
        let sum_num = num(d, sum);
        let sum_den = den(d, sum);
        let lifted_sum = d.of_nat(sum_den);
        let lifted_combined = d.of_nat(combined_den);
        let scaled = d.imul(sum_num, lifted_combined);
        let vanishes = d.int_eq_rewrite(source, zero, folded, cross, &|d, x| {
            let right = d.imul(x, lifted_sum);
            d.ieq(scaled, right)
        });
        let collapse_right = d.lemma(p.int_zero_mul, &[lifted_sum]);
        let right_scaled = d.imul(zero, lifted_sum);
        let reduced = d.itrans(scaled, right_scaled, zero, vanishes, collapse_right);
        let zero_scaled = d.imul(zero, lifted_combined);
        let restore = d.lemma(p.int_zero_mul, &[lifted_combined]);
        let balanced = {
            let back = d.isymm(zero_scaled, zero, restore);
            d.itrans(scaled, zero, zero_scaled, reduced, back)
        };
        let numerator_zero = d.lemma(
            p.int_mul_right_cancel,
            &[sum_num, zero, combined_den, combined_positive, balanced],
        );
        let proof = d.const_app(p.eq_zero_of_num_zero, &[sum, numerator_zero]);
        (stmt, proof)
    })?;

    // `0 ≤ a → 0 ≤ b → 0 ≤ a·b`, and the unconditional `0 ≤ a·a`. Both go
    // through the numerator: the product's numerator has the sign of `n_a·n_b`,
    // because the (positive) denominators cancel.
    let nonneg_product =
        |d: &mut IntDev<'_>, a: ExprId, b: ExprId, numerator_nonneg: ExprId| -> ExprId {
            let product = rmul(d, a, b);
            let den_a = den(d, a);
            let den_b = den(d, b);
            let positive_a = den_pos(d, a);
            let positive_b = den_pos(d, b);
            let combined_den = NatOps::mul(d, den_a, den_b);
            let combined_positive =
                d.lemma(nat.one_le_mul, &[den_a, den_b, positive_a, positive_b]);
            let na = num(d, a);
            let nb = num(d, b);
            let source = d.imul(na, nb);
            let cross = d.lemma(p.mul_cross, &[a, b]);
            let product_num = num(d, product);
            let product_den = den(d, product);
            let lifted_product = d.of_nat(product_den);
            let lifted_combined = d.of_nat(combined_den);
            let scaled = d.imul(product_num, lifted_combined);
            let zero = d.izero();
            // `0 ≤ (n_a·n_b)·den(a·b)`, transported back along the cross equation.
            let denominator_nonneg = d.lemma(p.int_zero_le_of_nat, &[product_den]);
            let scaled_nonneg = d.lemma(
                int.mul_nonneg,
                &[source, lifted_product, numerator_nonneg, denominator_nonneg],
            );
            let right = d.imul(source, lifted_product);
            let back = d.isymm(scaled, right, cross);
            let moved =
                d.int_eq_rewrite(right, scaled, back, scaled_nonneg, &|d, x| d.ile(zero, x));
            // `0 = 0·(d_a·d_b)`, so the bound is between two scaled terms.
            let zero_scaled = d.imul(zero, lifted_combined);
            let restore = d.lemma(p.int_zero_mul, &[lifted_combined]);
            let rebalanced = {
                let inverse = d.isymm(zero_scaled, zero, restore);
                d.int_eq_rewrite(zero, zero_scaled, inverse, moved, &|d, x| d.ile(x, scaled))
            };
            let cancelled = d.lemma(
                p.int_le_of_mul_le_mul_right,
                &[
                    zero,
                    product_num,
                    combined_den,
                    combined_positive,
                    rebalanced,
                ],
            );
            d.const_app(p.nonneg_of_int_nonneg, &[product, cancelled])
        };

    rat_theorem(d, p.mul_nonneg, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let stmt = statements::mul_nonneg(d, p, v);
        let zero_rat = d.kernel().const_(p.zero, vec![]);
        let first_ty = rle(d, p, zero_rat, a);
        let second_ty = rle(d, p, zero_rat, b);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let na_nonneg = d.lemma(p.int_nonneg_of_nonneg, &[a, h1]);
        let nb_nonneg = d.lemma(p.int_nonneg_of_nonneg, &[b, h2]);
        let na = num(d, a);
        let nb = num(d, b);
        let numerator_nonneg = d.lemma(int.mul_nonneg, &[na, nb, na_nonneg, nb_nonneg]);
        let body = nonneg_product(d, a, b, numerator_nonneg);
        let proof = {
            let with_second = d.lam_fv(h2_fv, second_ty, body);
            d.lam_fv(h1_fv, first_ty, with_second)
        };
        (stmt, proof)
    })?;

    rat_theorem(d, p.sq_nonneg, 1, &|d, v| {
        let a = v[0];
        let stmt = statements::sq_nonneg(d, p, v);
        let na = num(d, a);
        let numerator_nonneg = d.lemma(int.sq_nonneg, &[na]);
        let proof = nonneg_product(d, a, a, numerator_nonneg);
        (stmt, proof)
    })?;

    let _ = normalize;
    let _ = req;
    Ok(())
}

/// `Rat.right_distrib : ∀ a b c, (a+b)*c = a*c + b*c`, from `left_distrib`
/// and `mul_comm` — the Rat-level mirror of `int_right_distrib` above, with
/// no representation reasoning needed since `left_distrib`/`mul_comm` are
/// already Rat-level facts.
///
/// **Not** called from [`declare_ring_laws`]: `left_distrib` itself is not
/// declared there (it lives in `rat_prelude::scaling`, declared later in
/// `build_rat_prelude`'s sequence), so this has to run after
/// `scaling::declare_scaling_laws`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_right_distrib(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.right_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let sum = radd(d, a, b);
        let lhs = rmul(d, sum, c);
        let ac = rmul(d, a, c);
        let bc = rmul(d, b, c);
        let rhs = radd(d, ac, bc);
        let stmt = req(d, lhs, rhs);

        // (a+b)*c = c*(a+b)
        let flipped = rmul(d, c, sum);
        let step1 = d.lemma(p.mul_comm, &[sum, c]);
        // c*(a+b) = c*a + c*b
        let ca = rmul(d, c, a);
        let cb = rmul(d, c, b);
        let expanded = radd(d, ca, cb);
        let step2 = d.lemma(p.left_distrib, &[c, a, b]);
        // c*a + c*b = a*c + c*b
        let ca_comm = d.lemma(p.mul_comm, &[c, a]);
        let after_head = radd(d, ac, cb);
        let step3 = rcongr(d, ca, ac, ca_comm, &|d, t| radd(d, t, cb));
        // a*c + c*b = a*c + b*c
        let cb_comm = d.lemma(p.mul_comm, &[c, b]);
        let step4 = rcongr(d, cb, bc, cb_comm, &|d, t| radd(d, ac, t));

        let (_e, proof) = rchain(
            d,
            lhs,
            &[
                (flipped, step1),
                (expanded, step2),
                (after_head, step3),
                (rhs, step4),
            ],
        );
        (stmt, proof)
    })
}
