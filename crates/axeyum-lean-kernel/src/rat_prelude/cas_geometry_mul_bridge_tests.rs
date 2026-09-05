//! CAS -> kernel bridge, the **polynomial × polynomial** slice: `prove_mul`.
//!
//! [`super::cas_geometry_bridge_tests`] reconstructs a `GeometryCertificate`'s
//! Nullstellensatz cofactor identity `conclusion = Σᵢ cofactorᵢ · generatorᵢ`
//! for **constant** cofactors only. That covers exactly one of the ten
//! committed certificates. This module lifts the restriction: a cofactor may be
//! any polynomial, which is what eight of the ten need.
//!
//! # What `prove_mul` unblocks — measured, and it is not eight
//!
//! `docs/plan/status/277-cas-multivariate.md` sized the non-constant-cofactor
//! cluster at 8 and listed a *fractional literal cast* as a separate blocker on
//! `medians-concurrent`. The two blockers **overlap**, and nothing said so.
//! Counting, per certificate in `artifacts/geometry-certificates/`, terms whose
//! serialised coefficient denominator is not `1`:
//!
//! | certificate | terms | non-integer coeffs | max cofactor terms | blocked on |
//! | --- | --- | --- | --- | --- |
//! | orthocentre-altitudes-concurrent | 26 | 0 | 1 | (landed, constant cofactors) |
//! | thales-right-angle-in-semicircle | 17 | 0 | 1 | vacuous identity (cofactor `1`, conclusion == generator) |
//! | varignon-midpoint-parallelogram | 0 | 0 | 0 | vacuous identity (`0 = 0`) |
//! | medians-concurrent | 32 | 24 | 1 | fractional cast only |
//! | **rhombus-diagonals-perpendicular** | **79** | **0** | **12** | **`prove_mul` only** |
//! | pappus-hexagon | 145 | 0 | 10 | `prove_mul` only |
//! | simson-line | 2010 | 0 | 324 | `prove_mul` only |
//! | parallelogram-diagonals-bisect | 53 | 24 | 4 | `prove_mul` AND fractional cast |
//! | centroid-divides-medians | 61 | 16 | 4 | `prove_mul` AND fractional cast |
//! | euler-line | 337 | 272 | 74 | `prove_mul` AND fractional cast |
//!
//! So `prove_mul` alone reaches **three**, and
//! `parallelogram-diagonals-bisect` — lane 277's named "cheapest next target"
//! on term count — is **not** one of them: every one of its cofactors and both
//! of its conclusions carry `±1/2`. The cheapest reachable certificate is
//! `rhombus-diagonals-perpendicular`, and that is what this module
//! reconstructs.
//!
//! # The design: the atoms stop being opaque, so make the SORT the invariant
//!
//! The parent module's tractability argument is that every monomial goes
//! through one builder, so two equal monomials are the same `ExprId` and the
//! cofactor identity is *linear* over an ordered basis of opaque atoms. A
//! polynomial cofactor breaks that: the product of two monomials has to be
//! rebuilt in canonical order, which is exactly the `mul_comm`/`mul_assoc`
//! reasoning the constant case never needed.
//!
//! The move that keeps it cheap is to treat a monomial as a **sorted list of
//! variable occurrences** rather than as an exponent map, and to prove the
//! product by the same *sorted merge* the addition already uses:
//!
//! - [`prove_mono_mul`] — `prod(u) · prod(v) = prod(merge(u, v))` by recursion
//!   on two ascending factor lists. Four cases, and two of them are free: when
//!   the left list's head wins and its tail is empty the two sides are the
//!   **same `ExprId`** (`rrefl`), and when the right list's head wins and *its*
//!   tail is empty it is a single [`super::ops`] `mul_comm`. The other two are
//!   one `mul_assoc` (reversed) and one derived `mul_left_comm` respectively.
//! - [`prove_term_mul`] — `(c₁·m₁) · Σⱼ cⱼmⱼ = Σⱼ (c₁cⱼ)·(m₁mⱼ)`, distributing
//!   with `left_distrib` and re-inserting each product term through the parent
//!   module's [`super::cas_geometry_bridge_tests::prove_merge`].
//! - [`prove_poly_mul`] — `Σᵢ · Σⱼ` by `right_distrib` over the left factor.
//!
//! **The re-insertion is not optional and it is the subtle part.**
//! Multiplication by a fixed monomial is *not* order-preserving under the
//! monomial order: with `m₁ = x`, `x < y` as monomials but `x·y < x·x`, so the
//! image of a sorted term list is not sorted. Every product term therefore goes
//! back through `prove_merge`, which is also what makes the cancelling case
//! (`(x−y)(x+y)`, where two `xy` terms must vanish) work without a special
//! path.
//!
//! `Rat.one_mul` and `Rat.zero_mul` do not exist in this prelude; both are
//! <!-- absent: Rat.one_mul, Rat.zero_mul -->
//! derived here from `mul_comm` plus `mul_one`/`mul_zero`
//! ([`rat_one_mul`], [`rat_zero_mul`]).
//!
//! # What this does NOT establish
//!
//! Everything the parent module disclaims applies verbatim, and one item gets
//! *worse* rather than better for `rhombus-diagonals-perpendicular`:
//!
//! 1. **It does not prove the geometry.** The kernel sees nine `Rat` variables
//!    and one algebraic identity. That `ax` is a point's abscissa, that the
//!    four generators are "AB ∥ DC", "BC ∥ AD", "|AB| = |BC|" and the
//!    non-degeneracy saturation, and that the conclusion is "AC ⟂ BD", are
//!    modelling choices made in `axeyum_cas::geometry_corpus` and reproduced by
//!    the translator here. Reconstruction **relocates** that assumption into a
//!    kernel definition choice; it does not discharge it.
//! 2. **It does not establish the geometric conditional.** The theorem is the
//!    identity `f = Σ hᵢgᵢ`. The implication `(∀i. gᵢ = 0) → f = 0` is one
//!    `Rat` rewrite away and is not taken: no hypothesis is discharged and no
//!    implication is declared.
//! 3. **Non-degeneracy is now IN the statement, as an uninterpreted variable.**
//!    Unlike orthocentre, this certificate saturates: `Zinv0` is a fresh
//!    variable and `generators[3]` is `Zinv0 · (abd-not-collinear) − 1`. In the
//!    kernel that is one more universally quantified `Rat` with no
//!    interpretation at all — the *reading* that `Zinv0` witnesses invertibility
//!    of the collinearity determinant, and hence that the theorem is vacuous on
//!    degenerate configurations, is entirely outside what is proved. The
//!    certificate's own `statement` field says the geometric claim is FALSE
//!    without that condition; the kernel term knows nothing of that.
//! 4. **It is over `Rat`, not `CReal`.** Nothing says the coordinates are real
//!    numbers; a rational-coefficient identity holds in every ℚ-algebra.
//! 5. **The translator is not the kernel's business.** `int_poly` reading the
//!    `MvPoly` correctly is checked by evaluation at integer points
//!    ([`tests::rhombus_certificate_identity_holds_at_integer_points`]), never
//!    by the trusted gate — the kernel never sees an `MvPoly`.

use std::collections::BTreeMap;

use axeyum_cas::geometry_certify::{GeometryCertificate, ProofOutcome, certify, geometry_limits};
use axeyum_cas::geometry_corpus;

use super::RatPrelude;
use super::cas_geometry_bridge_tests::{
    IntPoly, Mono, add_poly, built, eval_int_poly, int_poly, mono_expr, poly_expr, prove_merge,
    term_expr,
};
use super::cas_ivt_bridge_tests::{int_lit, of_int};
use super::ops::{radd, rat_theorem, rchain, rcongr, req, rmul, rone, rrefl, rsymm, rzero};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::on_a_deep_stack;

// ---------------------------------------------------------------------------
// Monomials as sorted FACTOR LISTS.
// ---------------------------------------------------------------------------

/// The factor list of a monomial: each variable repeated by its exponent, in
/// the monomial's own ascending order.
///
/// This is precisely the sequence
/// [`super::cas_geometry_bridge_tests::mono_expr`] right-nests, so
/// [`factors_expr`] and `mono_expr` are two spellings of one term — pinned by
/// [`tests::factor_list_and_monomial_build_the_same_term`], because every
/// argument in this module rests on it.
///
/// # Panics
///
/// If the monomial's variables are not strictly ascending. The CAS's
/// `Monomial::powers` is documented to be, and the merge below is only correct
/// if it is, so this is asserted rather than assumed.
pub(super) fn mono_factors(mono: &[(String, u32)]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut previous: Option<&str> = None;
    for (name, exp) in mono {
        if let Some(prev) = previous {
            assert!(
                prev < name.as_str(),
                "monomial variables must be strictly ascending: {prev} then {name}"
            );
        }
        previous = Some(name.as_str());
        assert!(*exp > 0, "a stored exponent must be positive");
        for _ in 0..*exp {
            out.push(name.clone());
        }
    }
    out
}

/// The product of two monomials: exponents added, variables kept ascending.
pub(super) fn mul_mono(a: &[(String, u32)], b: &[(String, u32)]) -> Mono {
    let (mut i, mut j) = (0usize, 0usize);
    let mut out: Mono = Vec::new();
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j].clone());
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push((a[i].0.clone(), a[i].1 + b[j].1));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// `t · p` on [`IntPoly`]s, mirroring [`prove_term_mul`]'s recursion exactly so
/// the two cannot disagree about the answer.
pub(super) fn mul_term_poly(t: &(Mono, i128), poly: &[(Mono, i128)]) -> IntPoly {
    let Some((head, rest)) = poly.split_first() else {
        return Vec::new();
    };
    let product = (mul_mono(&t.0, &head.0), t.1 * head.1);
    let tail = mul_term_poly(t, rest);
    add_poly(std::slice::from_ref(&product), &tail)
}

/// `a · b` on [`IntPoly`]s, mirroring [`prove_poly_mul`]'s recursion.
pub(super) fn mul_poly(a: &[(Mono, i128)], b: &[(Mono, i128)]) -> IntPoly {
    let Some((head, rest)) = a.split_first() else {
        return Vec::new();
    };
    add_poly(&mul_term_poly(head, b), &mul_poly(rest, b))
}

// ---------------------------------------------------------------------------
// Kernel-side term builders and the two derived lemmas.
// ---------------------------------------------------------------------------

/// A factor list as a right-nested `Rat.mul`; the empty list is `Rat.one`.
///
/// Byte-for-byte the shape
/// [`super::cas_geometry_bridge_tests::mono_expr`] produces — see
/// [`mono_factors`].
pub(super) fn factors_expr(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    factors: &[String],
) -> ExprId {
    let ids: Vec<ExprId> = factors
        .iter()
        .map(|name| {
            *vars
                .get(name)
                .expect("factors_expr: every factor must be bound")
        })
        .collect();
    let Some((&last, rest)) = ids.split_last() else {
        return rone(d, p);
    };
    let mut acc = last;
    for &factor in rest.iter().rev() {
        acc = rmul(d, factor, acc);
    }
    acc
}

/// `Rat.one * x = x`. The prelude has `mul_one` and `mul_comm` but no
/// `one_mul`, so it is derived rather than assumed.
pub(super) fn rat_one_mul(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let one = rone(d, p);
    let lhs = rmul(d, one, x);
    let flipped = rmul(d, x, one);
    let comm = d.lemma(p.mul_comm, &[one, x]);
    let unit = d.lemma(p.mul_one, &[x]);
    let (_, proof) = rchain(d, lhs, &[(flipped, comm), (x, unit)]);
    proof
}

/// `Rat.zero * x = Rat.zero`, derived from `mul_comm` and `mul_zero` for the
/// same reason as [`rat_one_mul`].
pub(super) fn rat_zero_mul(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let zero = rzero(d, p);
    let lhs = rmul(d, zero, x);
    let flipped = rmul(d, x, zero);
    let comm = d.lemma(p.mul_comm, &[zero, x]);
    let absorb = d.lemma(p.mul_zero, &[x]);
    let (_, proof) = rchain(d, lhs, &[(flipped, comm), (zero, absorb)]);
    proof
}

/// `x * (y * z) = y * (x * z)` — the multiplicative twin of the parent
/// module's `add_left_comm`, and needed for the same reason: the kernel has no
/// `mul_left_comm`, and the sorted merge needs to pull the right-hand list's
/// head out past the whole left-hand product.
pub(super) fn mul_left_comm(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> (ExprId, ExprId) {
    let y_z = rmul(d, y, z);
    let start = rmul(d, x, y_z);
    let x_y = rmul(d, x, y);
    let mid1 = rmul(d, x_y, z);
    let assoc1 = d.lemma(p.mul_assoc, &[x, y, z]);
    let step1 = rsymm(d, mid1, start, assoc1);

    let y_x = rmul(d, y, x);
    let mid2 = rmul(d, y_x, z);
    let comm = d.lemma(p.mul_comm, &[x, y]);
    let step2 = rcongr(d, x_y, y_x, comm, &|d, t| rmul(d, t, z));

    let x_z = rmul(d, x, z);
    let end = rmul(d, y, x_z);
    let step3 = d.lemma(p.mul_assoc, &[y, x, z]);

    let (_, proof) = rchain(d, start, &[(mid1, step1), (mid2, step2), (end, step3)]);
    (end, proof)
}

// ---------------------------------------------------------------------------
// prove_mul, in three layers.
// ---------------------------------------------------------------------------

/// `factors_expr(u) * factors_expr(v) = factors_expr(merge(u, v))` for two
/// ascending factor lists, returning the merged list alongside the proof.
///
/// The four cases, and what each costs:
///
/// | case | rewrite |
/// | --- | --- |
/// | `u` empty | one derived `one_mul` |
/// | `v` empty | one `mul_one` |
/// | `head(u) ≤ head(v)`, `u` a singleton | **none** — the two sides are the same `ExprId` |
/// | `head(u) ≤ head(v)`, otherwise | `mul_assoc` reversed, then recurse under `x * _` |
/// | `head(u) > head(v)`, `v` a singleton | one `mul_comm` |
/// | `head(u) > head(v)`, otherwise | [`mul_left_comm`], then recurse under `y * _` |
///
/// The two singleton cases exist because `factors_expr` does **not** terminate
/// its product in `Rat.one` (a monomial is `ax * (bx * cy)`, not
/// `ax * (bx * (cy * 1))`), which keeps the declared statement readable at the
/// cost of these two extra branches.
pub(super) fn prove_mono_mul(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    u: &[String],
    v: &[String],
) -> (Vec<String>, ExprId) {
    let u_e = factors_expr(d, p, vars, u);
    let v_e = factors_expr(d, p, vars, v);

    let Some((u_head, u_rest)) = u.split_first() else {
        return (v.to_vec(), rat_one_mul(d, p, v_e));
    };
    let Some((v_head, v_rest)) = v.split_first() else {
        return (u.to_vec(), d.lemma(p.mul_one, &[u_e]));
    };

    let start = rmul(d, u_e, v_e);
    if u_head <= v_head {
        let head_e = *vars
            .get(u_head)
            .expect("prove_mono_mul: every factor must be bound");
        if u_rest.is_empty() {
            // `u_e` IS `head_e`, and `v` is non-empty, so `head_e * v_e` is
            // already the canonical form of `[u_head] ++ v`. Nothing to prove.
            let mut merged = vec![u_head.clone()];
            merged.extend_from_slice(v);
            return (merged, rrefl(d, start));
        }
        let rest_e = factors_expr(d, p, vars, u_rest);
        let inner = rmul(d, rest_e, v_e);
        let mid = rmul(d, head_e, inner);
        // `mul_assoc x y z : (x*y)*z = x*(y*z)` runs start -> mid directly.
        let step1 = d.lemma(p.mul_assoc, &[head_e, rest_e, v_e]);

        let (merged_rest, tail) = prove_mono_mul(d, p, vars, u_rest, v);
        let merged_rest_e = factors_expr(d, p, vars, &merged_rest);
        let end = rmul(d, head_e, merged_rest_e);
        let step2 = rcongr(d, inner, merged_rest_e, tail, &|d, t| rmul(d, head_e, t));

        let (_, proof) = rchain(d, start, &[(mid, step1), (end, step2)]);
        let mut merged = vec![u_head.clone()];
        merged.extend(merged_rest);
        (merged, proof)
    } else {
        let head_e = *vars
            .get(v_head)
            .expect("prove_mono_mul: every factor must be bound");
        if v_rest.is_empty() {
            // `v_e` IS `head_e`; `u` is non-empty, so the target is
            // `head_e * u_e` and one `mul_comm` gets there.
            let mut merged = vec![v_head.clone()];
            merged.extend_from_slice(u);
            return (merged, d.lemma(p.mul_comm, &[u_e, head_e]));
        }
        let rest_e = factors_expr(d, p, vars, v_rest);
        let (mid, step1) = mul_left_comm(d, p, u_e, head_e, rest_e);
        let inner = rmul(d, u_e, rest_e);

        let (merged_rest, tail) = prove_mono_mul(d, p, vars, u, v_rest);
        let merged_rest_e = factors_expr(d, p, vars, &merged_rest);
        let end = rmul(d, head_e, merged_rest_e);
        let step2 = rcongr(d, inner, merged_rest_e, tail, &|d, t| rmul(d, head_e, t));

        let (_, proof) = rchain(d, start, &[(mid, step1), (end, step2)]);
        let mut merged = vec![v_head.clone()];
        merged.extend(merged_rest);
        (merged, proof)
    }
}

/// `term_expr(a) * term_expr(b) = term_expr(a·b)` for two single terms.
///
/// Five rewrites: `mul_assoc` reversed to expose the left monomial,
/// [`mul_left_comm`] to lift the right coefficient out, `mul_assoc` forward to
/// pair the two coefficients, `Rat.ofInt_mul` reversed to fold them into one
/// literal, then [`prove_mono_mul`] under `ofInt (c₁c₂) * _`. A final defeq
/// ascription re-normalises the kernel's `Int.mul` node to the canonical
/// literal, exactly as the parent module's `prove_scale` does.
fn prove_head_product(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    a: &(Mono, i128),
    b: &(Mono, i128),
) -> ((Mono, i128), ExprId) {
    let a_int = int_lit(d, a.1);
    let a_rat = of_int(d, p, a_int);
    let a_mono = mono_expr(d, p, vars, &a.0);
    let b_int = int_lit(d, b.1);
    let b_rat = of_int(d, p, b_int);
    let b_mono = mono_expr(d, p, vars, &b.0);

    let a_e = rmul(d, a_rat, a_mono);
    let b_e = rmul(d, b_rat, b_mono);
    let start = rmul(d, a_e, b_e);

    // 1. (ca * m1) * (cb * m2) = ca * (m1 * (cb * m2))
    let inner1 = rmul(d, a_mono, b_e);
    let mid1 = rmul(d, a_rat, inner1);
    let step1 = d.lemma(p.mul_assoc, &[a_rat, a_mono, b_e]);

    // 2. m1 * (cb * m2) = cb * (m1 * m2)
    let (swapped, swap_proof) = mul_left_comm(d, p, a_mono, b_rat, b_mono);
    let mid2 = rmul(d, a_rat, swapped);
    let step2 = rcongr(d, inner1, swapped, swap_proof, &|d, t| rmul(d, a_rat, t));

    // 3. ca * (cb * (m1 * m2)) = (ca * cb) * (m1 * m2)
    let monos = rmul(d, a_mono, b_mono);
    let coeffs = rmul(d, a_rat, b_rat);
    let mid3 = rmul(d, coeffs, monos);
    let assoc3 = d.lemma(p.mul_assoc, &[a_rat, b_rat, monos]);
    let step3 = rsymm(d, mid3, mid2, assoc3);

    // 4. (ofInt ca * ofInt cb) * M = ofInt (ca*cb) * M
    let product_int = d.imul(a_int, b_int);
    let product_rat = of_int(d, p, product_int);
    let of_mul = d.lemma(p.of_int_mul, &[a_int, b_int]);
    let of_mul_rev = rsymm(d, product_rat, coeffs, of_mul);
    let mid4 = rmul(d, product_rat, monos);
    let step4 = rcongr(d, coeffs, product_rat, of_mul_rev, &|d, t| {
        rmul(d, t, monos)
    });

    // 5. m1 * m2 = canonical monomial.
    let a_factors = mono_factors(&a.0);
    let b_factors = mono_factors(&b.0);
    let (merged_factors, mono_proof) = prove_mono_mul(d, p, vars, &a_factors, &b_factors);
    let merged_mono_e = factors_expr(d, p, vars, &merged_factors);
    let mid5 = rmul(d, product_rat, merged_mono_e);
    let step5 = rcongr(d, monos, merged_mono_e, mono_proof, &|d, t| {
        rmul(d, product_rat, t)
    });

    // 6. `ofInt (Int.mul ca cb)` and `ofInt (literal ca*cb)` are the same value;
    //    the kernel's own `Int` computation is what checks it.
    let product = (mul_mono(&a.0, &b.0), a.1 * b.1);
    let end = term_expr(d, p, vars, &product);
    let step6 = rrefl(d, end);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (mid5, step5),
            (end, step6),
        ],
    );
    debug_assert_eq!(
        merged_factors,
        mono_factors(&product.0),
        "the merged factor list must be the product monomial's own"
    );
    (product, proof)
}

/// `term_expr(t) * poly_expr(b) = poly_expr(t · b)`.
///
/// `left_distrib` peels one term off `b`, [`prove_head_product`] normalises the
/// product, and the result is re-inserted with
/// [`super::cas_geometry_bridge_tests::prove_merge`] — necessary because
/// multiplying by a fixed monomial does not preserve the monomial order (with
/// `t = x`: `x < y` but `x·y < x·x`).
fn prove_term_mul(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    t: &(Mono, i128),
    b: &[(Mono, i128)],
) -> (IntPoly, ExprId) {
    let t_e = term_expr(d, p, vars, t);
    let Some((b_head, b_rest)) = b.split_first() else {
        return (Vec::new(), d.lemma(p.mul_zero, &[t_e]));
    };

    let b_head_e = term_expr(d, p, vars, b_head);
    let b_rest_e = poly_expr(d, p, vars, b_rest);
    let b_e = radd(d, b_head_e, b_rest_e);
    let start = rmul(d, t_e, b_e);

    // 1. X * (h + B') = X*h + X*B'
    let x_head = rmul(d, t_e, b_head_e);
    let x_rest = rmul(d, t_e, b_rest_e);
    let mid1 = radd(d, x_head, x_rest);
    let step1 = d.lemma(p.left_distrib, &[t_e, b_head_e, b_rest_e]);

    // 2. X*h = the canonical product term.
    let (product, product_proof) = prove_head_product(d, p, vars, t, b_head);
    let product_e = term_expr(d, p, vars, &product);
    let mid2 = radd(d, product_e, x_rest);
    let step2 = rcongr(d, x_head, product_e, product_proof, &|d, t| {
        radd(d, t, x_rest)
    });

    // 3. Give the head term `poly_expr`'s `+ 0` terminator so `prove_merge`
    //    can consume it as a one-term polynomial.
    let product_poly = vec![product];
    let product_poly_e = poly_expr(d, p, vars, &product_poly);
    let add_zero = d.lemma(p.add_zero, &[product_e]);
    let terminated = rsymm(d, product_poly_e, product_e, add_zero);
    let mid3 = radd(d, product_poly_e, x_rest);
    let step3 = rcongr(d, product_e, product_poly_e, terminated, &|d, t| {
        radd(d, t, x_rest)
    });

    // 4. recurse on the tail, then merge.
    let (tail_poly, tail_proof) = prove_term_mul(d, p, vars, t, b_rest);
    let tail_poly_e = poly_expr(d, p, vars, &tail_poly);
    let mid4 = radd(d, product_poly_e, tail_poly_e);
    let step4 = rcongr(d, x_rest, tail_poly_e, tail_proof, &|d, t| {
        radd(d, product_poly_e, t)
    });

    let (merged, merge_proof) = prove_merge(d, p, vars, &product_poly, &tail_poly);
    let end = poly_expr(d, p, vars, &merged);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (end, merge_proof),
        ],
    );
    (merged, proof)
}

/// **`prove_mul`**: `poly_expr(a) * poly_expr(b) = poly_expr(a · b)`.
///
/// `right_distrib` peels one term off `a`, [`prove_term_mul`] handles it
/// against the whole of `b`, and the two partial sums are merged.
fn prove_poly_mul(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    a: &[(Mono, i128)],
    b: &[(Mono, i128)],
) -> (IntPoly, ExprId) {
    let b_e = poly_expr(d, p, vars, b);
    let Some((a_head, a_rest)) = a.split_first() else {
        return (Vec::new(), rat_zero_mul(d, p, b_e));
    };

    let a_head_e = term_expr(d, p, vars, a_head);
    let a_rest_e = poly_expr(d, p, vars, a_rest);
    let a_e = radd(d, a_head_e, a_rest_e);
    let start = rmul(d, a_e, b_e);

    // 1. (h + A') * B = h*B + A'*B
    let head_times = rmul(d, a_head_e, b_e);
    let rest_times = rmul(d, a_rest_e, b_e);
    let mid1 = radd(d, head_times, rest_times);
    // `right_distrib x y z : (x+y)*z = x*z + y*z` runs start -> mid1 directly.
    let step1 = d.lemma(p.right_distrib, &[a_head_e, a_rest_e, b_e]);

    let (head_poly, head_proof) = prove_term_mul(d, p, vars, a_head, b);
    let head_poly_e = poly_expr(d, p, vars, &head_poly);
    let mid2 = radd(d, head_poly_e, rest_times);
    let step2 = rcongr(d, head_times, head_poly_e, head_proof, &|d, t| {
        radd(d, t, rest_times)
    });

    let (rest_poly, rest_proof) = prove_poly_mul(d, p, vars, a_rest, b);
    let rest_poly_e = poly_expr(d, p, vars, &rest_poly);
    let mid3 = radd(d, head_poly_e, rest_poly_e);
    let step3 = rcongr(d, rest_times, rest_poly_e, rest_proof, &|d, t| {
        radd(d, head_poly_e, t)
    });

    let (merged, merge_proof) = prove_merge(d, p, vars, &head_poly, &rest_poly);
    let end = poly_expr(d, p, vars, &merged);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (end, merge_proof),
        ],
    );
    (merged, proof)
}

/// `Σᵢ (poly_expr(hᵢ) · poly_expr(gᵢ)) = poly_expr(Σᵢ hᵢgᵢ)` for POLYNOMIAL
/// cofactors, with the left-hand sum right-nested and not terminated in zero,
/// so the declared statement reads as the certificate writes it.
fn prove_poly_combination(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    parts: &[(IntPoly, IntPoly)],
) -> (ExprId, IntPoly, ExprId) {
    let ((cofactor, generator), rest) = parts
        .split_first()
        .expect("prove_poly_combination: at least one generator is required");
    let cofactor_e = poly_expr(d, p, vars, cofactor);
    let generator_e = poly_expr(d, p, vars, generator);
    let head_e = rmul(d, cofactor_e, generator_e);
    let (product, product_proof) = prove_poly_mul(d, p, vars, cofactor, generator);
    let product_e = poly_expr(d, p, vars, &product);

    if rest.is_empty() {
        return (head_e, product, product_proof);
    }

    let (tail_e, tail_poly, tail_proof) = prove_poly_combination(d, p, vars, rest);
    let start = radd(d, head_e, tail_e);
    let tail_poly_e = poly_expr(d, p, vars, &tail_poly);

    let mid1 = radd(d, product_e, tail_e);
    let step1 = rcongr(d, head_e, product_e, product_proof, &|d, t| {
        radd(d, t, tail_e)
    });
    let mid2 = radd(d, product_e, tail_poly_e);
    let step2 = rcongr(d, tail_e, tail_poly_e, tail_proof, &|d, t| {
        radd(d, product_e, t)
    });

    let (merged, merge_proof) = prove_merge(d, p, vars, &product, &tail_poly);
    let merged_e = poly_expr(d, p, vars, &merged);

    let (_, proof) = rchain(
        d,
        start,
        &[(mid1, step1), (mid2, step2), (merged_e, merge_proof)],
    );
    (start, merged, proof)
}

// ---------------------------------------------------------------------------
// The certificate side.
// ---------------------------------------------------------------------------

/// Produce `rhombus-diagonals-perpendicular`'s certificate from the CAS's own
/// corpus and certifier — the same artifact
/// `F:geometry-rhombus-diagonals-perpendicular` cites, not a hand-copy.
fn rhombus_certificate() -> GeometryCertificate {
    let problem = geometry_corpus::corpus()
        .into_iter()
        .find(|p| p.id == "rhombus-diagonals-perpendicular")
        .expect("the CAS corpus must carry rhombus-diagonals-perpendicular");
    match certify(&problem, geometry_limits()) {
        ProofOutcome::Certified(cert) => *cert,
        other => panic!("the CAS must certify rhombus-diagonals-perpendicular: {other:?}"),
    }
}

/// Every variable the certificate quantifies over: the coordinates first, then
/// each saturation's inverse variable, in the certificate's own order.
fn certificate_variables(cert: &GeometryCertificate) -> Vec<String> {
    let mut names = cert.coordinates.clone();
    names.extend(cert.saturations.iter().map(|s| s.var.clone()));
    names
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    fn mono(pairs: &[(&str, u32)]) -> Mono {
        pairs.iter().map(|(n, e)| ((*n).to_owned(), *e)).collect()
    }

    fn point(pairs: &[(&'static str, i128)]) -> BTreeMap<&'static str, i128> {
        pairs.iter().copied().collect()
    }

    /// [`mono_factors`] + [`factors_expr`] must build the SAME term
    /// [`mono_expr`] does. Every step of [`prove_mono_mul`] assumes it, and the
    /// two functions live in different modules, so nothing else would notice
    /// them drifting apart.
    #[test]
    fn factor_list_and_monomial_build_the_same_term() {
        let (mut kernel, prelude) = built();
        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        let names = ["ax", "by", "cy"];
        let vars: BTreeMap<String, ExprId> = names
            .iter()
            .map(|n| {
                let fv = d.fresh_fvar();
                ((*n).to_owned(), d.kernel().fvar(fv))
            })
            .collect();

        for shape in [
            mono(&[]),
            mono(&[("ax", 1)]),
            mono(&[("ax", 2)]),
            mono(&[("ax", 1), ("by", 1)]),
            mono(&[("ax", 2), ("by", 1), ("cy", 3)]),
        ] {
            let direct = mono_expr(&mut d, p, &vars, &shape);
            let factors = mono_factors(&shape);
            let via_list = factors_expr(&mut d, p, &vars, &factors);
            assert_eq!(
                direct, via_list,
                "mono_expr and factors_expr must agree on {shape:?}"
            );
        }

        // Negative control: a DIFFERENT exponent must give a different term, or
        // the equalities above could hold for a builder that ignores its input.
        let a = mono_expr(&mut d, p, &vars, &mono(&[("ax", 2), ("by", 1)]));
        let b = mono_expr(&mut d, p, &vars, &mono(&[("ax", 1), ("by", 2)]));
        assert_ne!(a, b, "x²y and xy² must not be the same term");
    }

    /// [`mul_mono`] and [`mul_poly`] checked against NUMBERS, at arguments that
    /// discriminate.
    ///
    /// The kernel cannot tell us this arithmetic is right — it is Rust, and the
    /// trusted gate only ever sees the term the arithmetic *directed*. So each
    /// product is evaluated at a concrete integer point and compared against the
    /// product of the factors' evaluations, computed independently.
    ///
    /// The exponents are deliberately asymmetric (`x²y`, not `x²y²`) so that
    /// transposing two of them changes the value: at `(x,y,z) = (2,3,1)`,
    /// `2x²y − yz` is `21` while `2xy² − yz` is `33`. Magnitudes are kept
    /// single-digit on purpose (`Nat` numerals here are unary).
    #[test]
    fn mul_poly_evaluates_to_the_product_of_the_factors() {
        // p = 2x²y − yz,  q = x + 3z.
        let p: IntPoly = vec![
            (mono(&[("x", 2), ("y", 1)]), 2),
            (mono(&[("y", 1), ("z", 1)]), -1),
        ];
        let q: IntPoly = vec![(mono(&[("x", 1)]), 1), (mono(&[("z", 1)]), 3)];
        let at = point(&[("x", 2), ("y", 3), ("z", 1)]);

        assert_eq!(eval_int_poly(&p, &at), 21, "2·4·3 − 3·1");
        assert_eq!(eval_int_poly(&q, &at), 5, "2 + 3");

        let product = mul_poly(&p, &q);
        assert_eq!(product.len(), 4, "no monomial collides, so 2 × 2 = 4 terms");
        assert_eq!(
            eval_int_poly(&product, &at),
            105,
            "2x³y + 6x²yz − xyz − 3yz² at (2,3,1)"
        );
        assert_eq!(eval_int_poly(&product, &at), 21 * 5);

        // Transposing the exponents of the first monomial changes the value, so
        // the assertions above are not satisfied by an exponent-blind builder.
        let transposed: IntPoly = vec![
            (mono(&[("x", 1), ("y", 2)]), 2),
            (mono(&[("y", 1), ("z", 1)]), -1),
        ];
        assert_eq!(eval_int_poly(&transposed, &at), 33);
        assert_ne!(
            eval_int_poly(&mul_poly(&transposed, &q), &at),
            105,
            "x²y ↦ xy² must change the product's value"
        );

        // Cancellation: (x − y)(x + y) = x² − y², where the two xy terms must
        // vanish. This is the case `prove_merge`'s zero-drop path handles, and
        // the only one in which the term COUNT falls.
        let diff: IntPoly = vec![(mono(&[("x", 1)]), 1), (mono(&[("y", 1)]), -1)];
        let sum: IntPoly = vec![(mono(&[("x", 1)]), 1), (mono(&[("y", 1)]), 1)];
        let squares = mul_poly(&diff, &sum);
        assert_eq!(squares.len(), 2, "the two xy terms cancel: 4 in, 2 out");
        assert_eq!(
            squares,
            vec![(mono(&[("x", 2)]), 1), (mono(&[("y", 2)]), -1)],
            "(x − y)(x + y) = x² − y²"
        );
        let sq_at = point(&[("x", 3), ("y", 2)]);
        assert_eq!(eval_int_poly(&squares, &sq_at), 5, "9 − 4");
        assert_eq!(
            eval_int_poly(&diff, &sq_at) * eval_int_poly(&sum, &sq_at),
            5,
            "1 × 5"
        );
    }

    /// The smallest kernel exercise of [`prove_poly_mul`]: `(x − y)(x + y) =
    /// x² − y²`, admitted through [`crate::Kernel::add_declaration`].
    ///
    /// Chosen because it is the cheapest instance that exercises every branch
    /// that can go wrong: monomial × monomial across two distinct variables (so
    /// `prove_mono_mul`'s `Greater` case fires), a negative coefficient, and the
    /// zero-drop inside `prove_merge`. If the rhombus reconstruction below fails
    /// this one localises whether the fault is in `prove_mul` or in the
    /// certificate plumbing.
    #[test]
    fn prove_mul_difference_of_squares_kernel_checked() {
        on_a_deep_stack(prove_mul_difference_of_squares_body);
    }

    fn prove_mul_difference_of_squares_body() {
        let diff: IntPoly = vec![(mono(&[("x", 1)]), 1), (mono(&[("y", 1)]), -1)];
        let sum: IntPoly = vec![(mono(&[("x", 1)]), 1), (mono(&[("y", 1)]), 1)];
        let expected = mul_poly(&diff, &sum);

        let (mut kernel, prelude) = built();
        let anon = kernel.anon();
        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;
        let name = d
            .kernel()
            .name_str(anon, "Check.cas_geometry_prove_mul_difference_of_squares");

        let names = ["x".to_owned(), "y".to_owned()];
        let expected_for_build = expected.clone();
        let result = rat_theorem(&mut d, name, names.len(), &|d, fvars| {
            let vars: BTreeMap<String, ExprId> =
                names.iter().cloned().zip(fvars.iter().copied()).collect();
            let lhs_e = poly_expr(d, p, &vars, &diff);
            let rhs_e = poly_expr(d, p, &vars, &sum);
            let start = rmul(d, lhs_e, rhs_e);
            let (product, proof) = prove_poly_mul(d, p, &vars, &diff, &sum);
            assert_eq!(
                product, expected_for_build,
                "the emitted normal form must be x² − y²"
            );
            let end = poly_expr(d, p, &vars, &product);
            let stmt = req(d, start, end);
            (stmt, proof)
        });
        result.expect("the kernel must admit (x − y)(x + y) = x² − y²");

        let env = kernel.environment();
        assert!(
            matches!(env.get(name), Some(Decl::Theorem { .. })),
            "must be admitted as a Theorem"
        );
        assert!(
            kernel.axiom_footprint(name).is_empty(),
            "must be axiom-free"
        );
    }

    /// The translator, checked against NUMBERS rather than asserted.
    ///
    /// The kernel never sees an `MvPoly`, so nothing downstream can tell us
    /// `int_poly` read the certificate correctly. The control is the cofactor
    /// identity itself, evaluated at an integer point where **no** generator
    /// vanishes — so the identity is doing work at that point rather than
    /// reducing to `0 = 0`.
    #[test]
    fn rhombus_certificate_identity_holds_at_integer_points() {
        let cert = rhombus_certificate();
        assert_eq!(cert.coordinates.len(), 8, "eight coordinates");
        assert_eq!(cert.saturations.len(), 1, "one non-degeneracy saturation");
        assert_eq!(
            cert.saturations[0].var, "Zinv0",
            "the inverse variable's NAME is the certificate's"
        );
        assert_eq!(
            cert.generators.len(),
            4,
            "three hypotheses plus the saturation"
        );
        assert_eq!(cert.conclusions.len(), 1, "one conclusion");

        let generators: Vec<IntPoly> = cert
            .generators
            .iter()
            .map(|g| int_poly(g).expect("integer coefficients"))
            .collect();
        let cofactors: Vec<IntPoly> = cert.conclusions[0]
            .cofactors
            .iter()
            .map(|c| int_poly(c).expect("integer cofactor"))
            .collect();
        let concl = int_poly(&cert.conclusions[0].poly).expect("integer coefficients");
        assert_eq!(
            generators.len(),
            cofactors.len(),
            "one cofactor per generator"
        );

        // At least one cofactor is NOT constant — otherwise this certificate
        // would be reachable without `prove_mul` at all and this whole module
        // would be untested by it.
        let non_constant = cofactors
            .iter()
            .filter(|c| c.len() > 1 || c.first().is_some_and(|t| !t.0.is_empty()))
            .count();
        assert_eq!(
            non_constant, 4,
            "all four cofactors are polynomial, which is why prove_mul is needed"
        );

        // A point where nothing vanishes: a scalene configuration with an
        // arbitrary Zinv0. Small integers on purpose.
        let at = point(&[
            ("ax", 1),
            ("ay", 2),
            ("bx", 3),
            ("by", 1),
            ("cx", 2),
            ("cy", 4),
            ("dx", 1),
            ("dy", 3),
            ("Zinv0", 2),
        ]);
        let gen_values: Vec<i128> = generators.iter().map(|g| eval_int_poly(g, &at)).collect();
        assert!(
            gen_values.iter().all(|v| *v != 0),
            "no generator may vanish at the control point, or the identity is vacuous there: {gen_values:?}"
        );

        let lhs = eval_int_poly(&concl, &at);
        let rhs: i128 = cofactors
            .iter()
            .zip(&generators)
            .map(|(c, g)| eval_int_poly(c, &at) * eval_int_poly(g, &at))
            .sum();
        assert_eq!(lhs, rhs, "the cofactor identity must hold at the point");

        // And the same identity re-derived through `mul_poly`/`add_poly`, which
        // is what the proof follows. This is what pins the Rust arithmetic to
        // the certificate rather than to itself.
        let mut combination: IntPoly = Vec::new();
        for (c, g) in cofactors.iter().zip(&generators) {
            combination = add_poly(&combination, &mul_poly(c, g));
        }
        assert_eq!(
            combination, concl,
            "Σ cofactorᵢ · generatorᵢ IS the conclusion polynomial"
        );

        // Negative control, differing in a SMALL term: dropping the last
        // generator's contribution must break it, or the equality above could
        // be satisfied by an arithmetic that ignores its arguments.
        let mut short: IntPoly = Vec::new();
        for (c, g) in cofactors.iter().zip(&generators).take(generators.len() - 1) {
            short = add_poly(&short, &mul_poly(c, g));
        }
        assert_ne!(
            short, concl,
            "a three-generator combination must NOT equal the conclusion"
        );
    }

    /// The reconstruction: `Check.geometry_rhombus_cofactor_identity`, admitted
    /// through [`crate::Kernel::add_declaration`].
    ///
    /// ```text
    /// ∀ (ax ay bx by cx cy dx dy Zinv0 : Rat),
    ///   ⟨AC ⟂ BD⟩ = ⟨h₀⟩·⟨AB ∥ DC⟩ + (⟨h₁⟩·⟨BC ∥ AD⟩
    ///             + (⟨h₂⟩·⟨|AB| = |BC|⟩ + ⟨h₃⟩·⟨Zinv0·det − 1⟩))
    /// ```
    ///
    /// See the module doc for the five things this does NOT establish. The
    /// shortest of them: `Zinv0` is an uninterpreted `Rat` variable, and
    /// nothing in the kernel knows it witnesses non-degeneracy.
    #[test]
    fn geometry_rhombus_cofactor_identity_kernel_checked() {
        on_a_deep_stack(geometry_rhombus_cofactor_identity_body);
    }

    fn geometry_rhombus_cofactor_identity_body() {
        let cert = rhombus_certificate();
        let generators: Vec<IntPoly> = cert
            .generators
            .iter()
            .map(|g| int_poly(g).expect("integer coefficients"))
            .collect();
        let cofactors: Vec<IntPoly> = cert.conclusions[0]
            .cofactors
            .iter()
            .map(|c| int_poly(c).expect("integer cofactor"))
            .collect();
        let concl = int_poly(&cert.conclusions[0].poly).expect("integer coefficients");

        let names = certificate_variables(&cert);
        assert_eq!(
            names,
            vec!["ax", "ay", "bx", "by", "cx", "cy", "dx", "dy", "Zinv0"],
            "the variable ORDER is the certificate's, not this test's"
        );

        let parts: Vec<(IntPoly, IntPoly)> = cofactors.into_iter().zip(generators).collect();
        let concl_for_build = concl.clone();

        let (mut kernel, prelude) = built();
        let anon = kernel.anon();
        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;
        let name = d
            .kernel()
            .name_str(anon, "Check.geometry_rhombus_cofactor_identity");

        let result = rat_theorem(&mut d, name, names.len(), &|d, fvars| {
            let vars: BTreeMap<String, ExprId> =
                names.iter().cloned().zip(fvars.iter().copied()).collect();
            let (rhs, merged, proof) = prove_poly_combination(d, p, &vars, &parts);
            assert_eq!(
                merged, concl_for_build,
                "the emitted normal form must BE the certificate's conclusion"
            );
            let lhs = poly_expr(d, p, &vars, &concl_for_build);
            let stmt = req(d, lhs, rhs);
            let flipped = rsymm(d, rhs, lhs, proof);
            (stmt, flipped)
        });
        result.expect("the kernel must admit the rhombus cofactor identity");

        let env = kernel.environment();
        let decl = env
            .get(name)
            .expect("the declaration must be in the environment");
        assert!(
            matches!(decl, Decl::Theorem { .. }),
            "must be admitted as a Theorem, not an Axiom or an Opaque"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "the identity must be axiom-free; footprint was {footprint:?}"
        );
    }
}
