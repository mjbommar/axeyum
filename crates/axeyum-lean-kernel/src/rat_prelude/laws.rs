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
    den, den_pos, den_z, iregroup3, normalize, num, radd, rat_theorem, req, rmul, rzero,
};
use super::statements;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// The three small `ℤ` facts and the two `Rat`/`ℤ` bridges the laws below need.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bridges(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;

    // int_right_distrib : (a+b)*c = a*c + b*c, from left_distrib and mul_comm.
    d.int_theorem(p.int_right_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let sum = d.iadd(a, b);
        let left = d.imul(sum, c);
        let first = d.imul(a, c);
        let second = d.imul(b, c);
        let right = d.iadd(first, second);
        let stmt = d.ieq(left, right);
        let flipped = d.imul(c, sum);
        let commute = d.lemma(int.mul_comm, &[sum, c]);
        let expanded = d.lemma(int.left_distrib, &[c, a, b]);
        let head = d.imul(c, a);
        let tail = d.imul(c, b);
        let opened = d.iadd(head, tail);
        let head_commute = d.lemma(int.mul_comm, &[c, a]);
        let with_head = d.icongr(head, first, head_commute, &|d, t| d.iadd(t, tail));
        let staged = d.iadd(first, tail);
        let tail_commute = d.lemma(int.mul_comm, &[c, b]);
        let with_tail = d.icongr(tail, second, tail_commute, &|d, t| d.iadd(first, t));
        let (_, proof) = d.ichain(
            left,
            &[
                (flipped, commute),
                (opened, expanded),
                (staged, with_head),
                (right, with_tail),
            ],
        );
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
                super::ops::rle(d, p, target, q)
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
    )
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
        let first_ty = super::ops::rle(d, p, zero_rat, a);
        let second_ty = super::ops::rle(d, p, zero_rat, b);
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
