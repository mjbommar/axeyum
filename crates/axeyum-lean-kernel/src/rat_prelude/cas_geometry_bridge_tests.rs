//! CAS -> kernel bridge, the **multivariate** slice: the Nullstellensatz
//! cofactor identity `conclusion = Σᵢ cofactorᵢ · generatorᵢ` of
//! `axeyum_cas::geometry_certify`'s [`GeometryCertificate`], reconstructed at
//! **symbolic** coordinates through [`crate::Kernel::add_declaration`].
//!
//! Every bridge before this one (`cas_ivt_bridge_tests`,
//! `cas_evt_bridge_tests`, `cas_mvt_secant_bridge_tests`,
//! `cas_taylor_remainder_bridge_tests`, `complex::cas_bridge_tests`) is
//! univariate by construction and evaluates at CONCRETE rational points. This
//! one is neither: the identity holds for all coordinates, so the statement
//! quantifies over them and nothing reduces to an integer literal.
//!
//! # The representation, and why there is no new kernel type
//!
//! `Rat.polyEval c n x = sumRange (fun i => c i * x^i) n` takes coefficients as
//! a FUNCTION and the degree as a CALLER-SUPPLIED BOUND — never a computed
//! degree, because `CReal.Equiv` and `CReal.le` are undecidable so no total
//! function can extract one (`creal/polynomial.rs`). The obvious multivariate
//! analogue is a function from exponent TUPLES to coefficients, which needs a
//! tuple type; the kernel's only product type is `Nat.Pair`.
//!
//! **This module deliberately does not go that way, and the arity survey is
//! why.** Measured over the ten committed certificates in
//! `artifacts/geometry-certificates/`:
//!
//! | certificate | vars | max total degree | total terms |
//! | --- | --- | --- | --- |
//! | thales-right-angle-in-semicircle | 6 | 2 | 17 |
//! | orthocentre-altitudes-concurrent | 8 | 2 | 26 |
//! | medians-concurrent | 8 | 2 | 32 |
//! | parallelogram-diagonals-bisect | 9 | 3 | 47 |
//! | centroid-divides-medians | 9 | 3 | 55 |
//! | rhombus-diagonals-perpendicular | 9 | 3 | 73 |
//! | euler-line | 11 | 6 | 331 |
//! | simson-line | 17 | 9 | 1992 |
//! | pappus-hexagon | 19 | 3 | 137 |
//! | varignon-midpoint-parallelogram | 0 | 0 | 0 |
//!
//! Arities run 6 to 19, so a fixed-arity (bivariate/trivariate) bridge covers
//! none of them, and a `Nat.Pair`-nested exponent tuple would have to nest to
//! depth 19. A general `Nat → Nat` exponent vector avoids the nesting but buys
//! a product-over-range: a degree-2 monomial in 8 variables unfolds to an
//! eight-factor product with six `Rat.one`s in it, and each of those is a
//! `mul_one` rewrite the kernel has to check. Twenty-four monomials would be
//! ~150 rewrites of pure padding.
//!
//! So the representation here is: **the ambient `Rat` ring expression, with
//! the CAS's canonical sparse form as the NORMAL FORM rather than as a kernel
//! datatype.** A certificate's obligation is a single closed identity with no
//! quantification over polynomials, so a polynomial type would carry no
//! statement that the plain expression cannot. The `polyEval` design principle
//! is preserved exactly: the term count, the variable support and every
//! exponent come from the translator, and nothing in the kernel ever computes
//! a degree or a support.
//!
//! # What makes the proof tractable: the atoms are opaque
//!
//! Every monomial is built by ONE Rust function ([`mono_expr`]) from the same
//! variable list in the same order, so two syntactically equal monomials are
//! the same `ExprId`. The cofactor identity therefore never needs `mul_comm`
//! or `mul_assoc` ON THE MONOMIALS — it is a purely LINEAR identity over an
//! ordered basis of opaque atoms. That is what reduces a ring-normalisation
//! problem to two small proof-emitting primitives:
//!
//! - [`prove_scale`] — `k · Σ cᵢmᵢ = Σ (k·cᵢ)mᵢ` (`left_distrib`, `mul_assoc`,
//!   `Rat.ofInt_mul`).
//! - [`prove_merge`] — a sorted merge of two canonical sums, combining like
//!   monomials (`add_assoc`, `add_comm`, `right_distrib`, `Rat.ofInt_add`),
//!   and DROPPING a monomial whose combined coefficient is zero (`mul_comm`,
//!   `mul_zero`, `zero_add`).
//!
//! Monomial × monomial is needed only when a cofactor is not constant, and is
//! NOT built here — see "What this does not establish".
//!
//! # Mutation-verified, both halves separately
//!
//! Two mutations were run against the committed tree (in this lane's own
//! worktree, never the shared checkout), each killing EXACTLY ONE test and
//! leaving the other two green:
//!
//! - **The statement check.** `scaled_head`'s coefficient `k * head.1` ->
//!   `k * head.1 + 1`: `geometry_orthocentre_cofactor_identity_kernel_checked`
//!   dies at the `merged == concl` assertion inside the builder, printing the
//!   12-term wrong normal form against the 8-term conclusion. So the statement
//!   the kernel is asked to admit is pinned to the CERTIFICATE's conclusion,
//!   not to whatever the emitter happened to produce.
//! - **The kernel gate.** One lemma swapped in the zero-drop path,
//!   `p.zero_add` -> `p.add_zero` (same arity, same argument, wrong direction):
//!   the same test dies with `TypeMismatch` out of
//!   [`crate::Kernel::add_declaration`], in 6.93 s. So the PROOF is genuinely
//!   re-derived by the trust anchor rather than accepted on the emitter's word,
//!   and a wrong rewrite is refused in bounded time (a failing defeq here has
//!   no early exit, so that bound is worth stating).
//!
//! # What this does NOT establish
//!
//! Stated up front because it is the load-bearing part, and the design review
//! (`docs/research/11-design-review/2026-08-29-row-three-is-blocked-on-multivariate.md`)
//! is emphatic about it:
//!
//! 1. **It does not prove the geometry.** The identity is about eight
//!    `Rat`-valued variables named `ax … py`. That `ax` IS the abscissa of a
//!    point A, that `ax·bx + ay·by − …` IS perpendicularity, and that the
//!    three altitudes of a triangle are what those two hypotheses describe, is
//!    a MODELLING choice made in `axeyum_cas::geometry_corpus` and reproduced
//!    here. Reconstruction RELOCATES that assumption from a CAS-internal
//!    convention into a kernel definition choice; it does not discharge it.
//! 2. **It does not establish the conclusion, only the implication's algebraic
//!    core.** `f = −g₀ − g₁` gives `g₀ = 0 ∧ g₁ = 0 → f = 0` in one further
//!    step, which this module does not take: no `Rat` hypothesis is discharged
//!    and no implication is declared.
//! 3. **It says nothing about non-degeneracy.** Orthocentre's certificate has
//!    an empty `saturations` list, so there is no inverse variable and no
//!    condition to reconstruct. For the six certificates that DO saturate, the
//!    `d·z − 1` generator is an extra variable and an extra generator, and the
//!    identity's meaning depends on that construction being right.
//! 4. **It does not cover non-constant cofactors**, which is eight of the ten
//!    geometry certificates, nor non-integer coefficients, which is what
//!    `medians-concurrent`'s `±1/2` needs (the same `Rat.ofRat`-style cast
//!    `F:cas-partial-fractions-mixed-general-case` is blocked on).
//!
//! # Thales, added 2026-08-30, and Varignon, deliberately NOT added
//!
//! `thales-right-angle-in-semicircle` reuses this module's machinery
//! unchanged: one generator, one conclusion, cofactor the constant `1` — the
//! conclusion polynomial IS the hypothesis polynomial, term for term, so
//! [`prove_const_combination`] with a one-element `parts` list needs only
//! [`prove_scale`] at `k=1` and never reaches [`add_poly`]/`prove_merge`'s
//! cancellation branch at all. No new proof-emitting code, same as
//! orthocentre.
//!
//! `varignon-midpoint-parallelogram` is deliberately **not** reconstructed
//! here, or anywhere. Read directly from
//! `artifacts/geometry-certificates/varignon-midpoint-parallelogram.json`:
//! `coordinates: []`, `generators: []`, and both conclusions' `poly` is
//! already `{"terms": []}` — the CAS's own empty `MvPoly`. The actual
//! content (that the four midpoint differences algebraically cancel) is
//! computed entirely inside `axeyum_cas::mvpoly`'s untrusted ring arithmetic
//! *before* a `GeometryCertificate` ever reaches this bridge; by the time it
//! does, there is no coordinate left to quantify over and no hypothesis or
//! cofactor to combine. The only statement this module's machinery could
//! build from that certificate is `Rat.zero = Rat.zero` over zero free
//! variables — well-formed, admissible, and content-free. It would still
//! satisfy `scripts/validate-facts.py`'s `classify_cas_certificate_fact`
//! (ADR-0601 §2 only asks whether some evidence row's `cargo test` names
//! `-p axeyum-lean-kernel`, never what the test checked), so registering a
//! sibling fact for it would move the `cas-certificate` ledger's
//! kernel-reconstructed count without adding one bit of kernel-checked
//! content — the exact failure this repository's own standing rule warns
//! against. See `docs/plan/status/332-cas-thales-varignon.md` for the full
//! argument. No `F:varignon-midpoint-parallelogram-kernel-checked` fact
//! exists, and none should be added on this route.

use std::collections::BTreeMap;

use axeyum_cas::geometry_certify::{GeometryCertificate, ProofOutcome, certify, geometry_limits};
use axeyum_cas::geometry_corpus;
use axeyum_cas::mvpoly::MvPoly;

use super::cas_ivt_bridge_tests::{int_lit, of_int, rational_to_int};
use super::ops::{radd, rat_theorem, rcongr, rmul, rone, rsymm, rtrans, rzero};
use super::{RatPrelude, build_rat_prelude};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Kernel, on_a_deep_stack};

pub(crate) fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    (kernel, prelude)
}

// ---------------------------------------------------------------------------
// The translator: `MvPoly` -> integer-coefficient sparse form.
// ---------------------------------------------------------------------------

/// One monomial as `(variable, exponent)` pairs in ascending variable order,
/// every exponent `> 0`; the empty vector is the constant monomial `1`. Same
/// canonical shape [`axeyum_cas::mvpoly::Monomial`] keeps, re-derived here
/// rather than borrowed so the ORDER this module sorts by is entirely its own
/// (see [`IntPoly`]).
pub(super) type Mono = Vec<(String, u32)>;

/// A polynomial as `(monomial, integer coefficient)` pairs, sorted by
/// monomial under `Mono`'s derived lexicographic order, with no zero
/// coefficient stored.
///
/// The sort is this module's, not the CAS's: nothing here ever compares its
/// order against `MvPoly`'s, only against itself, and internal consistency is
/// what makes two equal polynomials build the identical `ExprId`.
pub(super) type IntPoly = Vec<(Mono, i128)>;

/// `MvPoly` -> [`IntPoly`], declining (`None`) on any non-integer coefficient.
///
/// The integer-only restriction is [`rational_to_int`]'s, inherited verbatim
/// from `cas_ivt_bridge_tests`: `axeyum_cas`'s `Rational` is fixed-width
/// `i128` (ADR-0038) and there is no general `Rat.ofRat` cast in this bridge
/// layer. `medians-concurrent` is declined for exactly this reason and its
/// `±1/2` coefficients are why.
pub(super) fn int_poly(poly: &MvPoly) -> Option<IntPoly> {
    let mut terms: IntPoly = Vec::new();
    for (mono, coeff) in poly.terms() {
        let value = rational_to_int(*coeff)?;
        if value == 0 {
            continue;
        }
        let key: Mono = mono
            .powers()
            .map(|(name, exp)| (name.to_owned(), exp))
            .collect();
        terms.push((key, value));
    }
    terms.sort();
    Some(terms)
}

/// `k · p` on [`IntPoly`]s. `k` must be nonzero, so no coefficient can vanish
/// and the term list keeps its shape (the zero-coefficient case is
/// [`prove_merge`]'s, where it is genuinely reachable).
fn scale_poly(k: i128, poly: &[(Mono, i128)]) -> IntPoly {
    assert!(k != 0, "scale_poly: k must be nonzero");
    poly.iter()
        .map(|(m, c)| (m.clone(), k * c))
        .collect::<IntPoly>()
}

/// `a + b` on [`IntPoly`]s: a sorted merge dropping any monomial whose
/// combined coefficient is zero. Mirrors [`prove_merge`]'s recursion exactly,
/// so the two cannot disagree about the answer.
pub(super) fn add_poly(a: &[(Mono, i128)], b: &[(Mono, i128)]) -> IntPoly {
    let (mut i, mut j) = (0usize, 0usize);
    let mut out: IntPoly = Vec::new();
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
                let sum = a[i].1 + b[j].1;
                if sum != 0 {
                    out.push((a[i].0.clone(), sum));
                }
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// Evaluate an [`IntPoly`] at an integer assignment. Used ONLY by the
/// translator's own discrimination test — never in a proof — so that
/// "`int_poly` produced the polynomial the certificate meant" is checked
/// against numbers rather than asserted.
pub(super) fn eval_int_poly(poly: &[(Mono, i128)], point: &BTreeMap<&str, i128>) -> i128 {
    let mut total = 0i128;
    for (mono, coeff) in poly {
        let mut term = *coeff;
        for (var, exp) in mono {
            let value = *point
                .get(var.as_str())
                .expect("eval_int_poly: every variable must be assigned");
            for _ in 0..*exp {
                term *= value;
            }
        }
        total += term;
    }
    total
}

// ---------------------------------------------------------------------------
// Kernel-side term builders. Everything below builds ONE canonical shape.
// ---------------------------------------------------------------------------

/// A monomial as a right-nested `Rat.mul` of its variables with multiplicity;
/// the constant monomial is `Rat.one`.
///
/// This is the whole reason the identity is linear rather than a ring-
/// normalisation problem: two equal monomials go through this function and
/// come out as the SAME `ExprId`, so no `mul_comm`/`mul_assoc` step ever has
/// to see inside one.
pub(super) fn mono_expr(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    mono: &[(String, u32)],
) -> ExprId {
    let mut factors: Vec<ExprId> = Vec::new();
    for (name, exp) in mono {
        let var = *vars
            .get(name)
            .expect("mono_expr: every monomial variable must be bound");
        for _ in 0..*exp {
            factors.push(var);
        }
    }
    let Some((&last, rest)) = factors.split_last() else {
        return rone(d, p);
    };
    let mut acc = last;
    for &factor in rest.iter().rev() {
        acc = rmul(d, factor, acc);
    }
    acc
}

/// One term as `Rat.ofInt c * monomial`.
pub(super) fn term_expr(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    term: &(Mono, i128),
) -> ExprId {
    let coeff_int = int_lit(d, term.1);
    let coeff = of_int(d, p, coeff_int);
    let mono = mono_expr(d, p, vars, &term.0);
    rmul(d, coeff, mono)
}

/// A polynomial as a right-nested `Rat.add` of its terms, TERMINATED IN
/// `Rat.zero` — `[a, b]` becomes `a + (b + 0)`.
///
/// The terminator is not decoration: it gives [`prove_merge`] and
/// [`prove_scale`] a single base case each (`zero_add`/`add_zero`/`mul_zero`)
/// instead of a separate singleton case, and it costs one `+ 0` per
/// polynomial.
pub(super) fn poly_expr(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    poly: &[(Mono, i128)],
) -> ExprId {
    let mut acc = rzero(d, p);
    for term in poly.iter().rev() {
        let term_e = term_expr(d, p, vars, term);
        acc = radd(d, term_e, acc);
    }
    acc
}

// ---------------------------------------------------------------------------
// The two proof-emitting primitives.
// ---------------------------------------------------------------------------

/// `x + (y + z) = y + (x + z)` — the swap [`prove_merge`] needs when the
/// right-hand list supplies the next monomial. Built from `add_assoc` and
/// `add_comm`, since the kernel has no `add_left_comm`.
pub(super) fn add_left_comm(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> (ExprId, ExprId) {
    let y_z = radd(d, y, z);
    let start = radd(d, x, y_z);
    let x_y = radd(d, x, y);
    let mid1 = radd(d, x_y, z);
    let assoc1 = d.lemma(p.add_assoc, &[x, y, z]);
    let step1 = rsymm(d, mid1, start, assoc1);

    let y_x = radd(d, y, x);
    let mid2 = radd(d, y_x, z);
    let comm = d.lemma(p.add_comm, &[x, y]);
    let step2 = rcongr(d, x_y, y_x, comm, &|d, t| radd(d, t, z));

    let x_z = radd(d, x, z);
    let end = radd(d, y, x_z);
    let step3 = d.lemma(p.add_assoc, &[y, x, z]);

    let proof12 = rtrans(d, start, mid1, mid2, step1, step2);
    let proof = rtrans(d, start, mid2, end, proof12, step3);
    (end, proof)
}

/// `Rat.ofInt k * poly_expr(poly) = poly_expr(k · poly)`, for a NONZERO `k`.
///
/// Recursion over the term list: `left_distrib` splits the head off, then
/// `mul_assoc` (reversed) and `Rat.ofInt_mul` (reversed) fold `k · (c · m)`
/// into `(k·c) · m`, and one defeq ascription re-normalises the `Int.mul`
/// tree to the literal the canonical term uses.
fn prove_scale(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    k: i128,
    k_rat: ExprId,
    k_int: ExprId,
    poly: &[(Mono, i128)],
) -> (IntPoly, ExprId) {
    let Some((head, rest)) = poly.split_first() else {
        let zero = rzero(d, p);
        let base = d.lemma(p.mul_zero, &[k_rat]);
        let _ = zero;
        return (Vec::new(), base);
    };

    let head_e = term_expr(d, p, vars, head);
    let rest_e = poly_expr(d, p, vars, rest);
    let sum_e = radd(d, head_e, rest_e);
    let start = rmul(d, k_rat, sum_e);

    // 1. k * (t + S') = k*t + k*S'
    let k_head = rmul(d, k_rat, head_e);
    let k_rest = rmul(d, k_rat, rest_e);
    let mid1 = radd(d, k_head, k_rest);
    let step1 = d.lemma(p.left_distrib, &[k_rat, head_e, rest_e]);

    // 2. k * (c * m) = (k * c) * m
    let coeff_int = int_lit(d, head.1);
    let coeff_rat = of_int(d, p, coeff_int);
    let mono = mono_expr(d, p, vars, &head.0);
    let k_coeff = rmul(d, k_rat, coeff_rat);
    let assoc_target = rmul(d, k_coeff, mono);
    let assoc = d.lemma(p.mul_assoc, &[k_rat, coeff_rat, mono]);
    let assoc_rev = rsymm(d, assoc_target, k_head, assoc);
    let mid2 = radd(d, assoc_target, k_rest);
    let step2 = rcongr(d, k_head, assoc_target, assoc_rev, &|d, t| {
        radd(d, t, k_rest)
    });

    // 3. (ofInt k * ofInt c) * m = ofInt (k*c) * m, then defeq to the literal.
    let product_int = d.imul(k_int, coeff_int);
    let product_rat = of_int(d, p, product_int);
    let of_mul = d.lemma(p.of_int_mul, &[k_int, coeff_int]);
    let of_mul_rev = rsymm(d, product_rat, k_coeff, of_mul);
    let folded = rmul(d, product_rat, mono);
    let mid3 = radd(d, folded, k_rest);
    let step3 = rcongr(d, k_coeff, product_rat, of_mul_rev, &|d, t| {
        let inner = rmul(d, t, mono);
        radd(d, inner, k_rest)
    });

    let scaled_head = (head.0.clone(), k * head.1);
    let canon_head = term_expr(d, p, vars, &scaled_head);
    let mid4 = radd(d, canon_head, k_rest);
    // `ofInt (Int.mul k c)` and `ofInt (literal k*c)` are the same value and
    // the kernel's own `Int` computation is what checks it — the same defeq
    // ascription `cas_ivt_bridge_tests::poly_eval_to_of_int` makes for its
    // accumulator.
    let step4 = crate::rat_prelude::ops::rrefl(d, mid4);

    // 4. recurse on the tail.
    let (scaled_rest, tail_proof) = prove_scale(d, p, vars, k, k_rat, k_int, rest);
    let scaled_rest_e = poly_expr(d, p, vars, &scaled_rest);
    let end = radd(d, canon_head, scaled_rest_e);
    let step5 = rcongr(d, k_rest, scaled_rest_e, tail_proof, &|d, t| {
        radd(d, canon_head, t)
    });

    let (_, proof) = super::ops::rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (end, step5),
        ],
    );

    let mut scaled = vec![scaled_head];
    scaled.extend(scaled_rest);
    (scaled, proof)
}

/// `poly_expr(a) + poly_expr(b) = poly_expr(a + b)` — a sorted merge over the
/// shared monomial basis.
///
/// The three interesting cases are the head comparison: `Less` regroups with
/// `add_assoc`, `Greater` swaps with [`add_left_comm`], and `Equal` combines
/// the two coefficients through `right_distrib` (reversed) and
/// `Rat.ofInt_add` (reversed) — then, when the sum is zero, DELETES the term
/// via `mul_comm`/`mul_zero`/`zero_add`. That deletion is the case the
/// orthocentre identity actually exercises four times.
pub(super) fn prove_merge(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    a: &[(Mono, i128)],
    b: &[(Mono, i128)],
) -> (IntPoly, ExprId) {
    let a_e = poly_expr(d, p, vars, a);
    let b_e = poly_expr(d, p, vars, b);

    let Some((a_head, a_rest)) = a.split_first() else {
        let proof = d.lemma(p.zero_add, &[b_e]);
        return (b.to_vec(), proof);
    };
    let Some((b_head, b_rest)) = b.split_first() else {
        let proof = d.lemma(p.add_zero, &[a_e]);
        return (a.to_vec(), proof);
    };

    let a_head_e = term_expr(d, p, vars, a_head);
    let a_rest_e = poly_expr(d, p, vars, a_rest);
    let b_head_e = term_expr(d, p, vars, b_head);
    let b_rest_e = poly_expr(d, p, vars, b_rest);
    let start = radd(d, a_e, b_e);

    match a_head.0.cmp(&b_head.0) {
        std::cmp::Ordering::Less => {
            // (t + A') + B = t + (A' + B), then merge(A', B).
            let inner = radd(d, a_rest_e, b_e);
            let mid = radd(d, a_head_e, inner);
            let step1 = d.lemma(p.add_assoc, &[a_head_e, a_rest_e, b_e]);

            let (merged_rest, tail) = prove_merge(d, p, vars, a_rest, b);
            let merged_rest_e = poly_expr(d, p, vars, &merged_rest);
            let end = radd(d, a_head_e, merged_rest_e);
            let step2 = rcongr(d, inner, merged_rest_e, tail, &|d, t| radd(d, a_head_e, t));

            let (_, proof) = super::ops::rchain(d, start, &[(mid, step1), (end, step2)]);
            let mut merged = vec![a_head.clone()];
            merged.extend(merged_rest);
            (merged, proof)
        }
        std::cmp::Ordering::Greater => {
            // A + (t + B') = t + (A + B'), then merge(A, B').
            let (mid, step1) = add_left_comm(d, p, a_e, b_head_e, b_rest_e);
            let inner = radd(d, a_e, b_rest_e);

            let (merged_rest, tail) = prove_merge(d, p, vars, a, b_rest);
            let merged_rest_e = poly_expr(d, p, vars, &merged_rest);
            let end = radd(d, b_head_e, merged_rest_e);
            let step2 = rcongr(d, inner, merged_rest_e, tail, &|d, t| radd(d, b_head_e, t));

            let (_, proof) = super::ops::rchain(d, start, &[(mid, step1), (end, step2)]);
            let mut merged = vec![b_head.clone()];
            merged.extend(merged_rest);
            (merged, proof)
        }
        std::cmp::Ordering::Equal => {
            // (ta + A') + (tb + B')
            //   = ta + (A' + (tb + B'))          [add_assoc]
            //   = ta + (tb + (A' + B'))          [add_left_comm, under ta + _]
            //   = (ta + tb) + (A' + B')          [add_assoc, reversed]
            //   = ((ca+cb)·m) + (A' + B')        [right_distrib / ofInt_add]
            let a_rest_plus_b = radd(d, a_rest_e, b_e);
            let mid1 = radd(d, a_head_e, a_rest_plus_b);
            let step1 = d.lemma(p.add_assoc, &[a_head_e, a_rest_e, b_e]);

            let (swapped, swap_proof) = add_left_comm(d, p, a_rest_e, b_head_e, b_rest_e);
            let mid2 = radd(d, a_head_e, swapped);
            let step2 = rcongr(d, a_rest_plus_b, swapped, swap_proof, &|d, t| {
                radd(d, a_head_e, t)
            });

            let rests = radd(d, a_rest_e, b_rest_e);
            let heads = radd(d, a_head_e, b_head_e);
            let mid3 = radd(d, heads, rests);
            let assoc = d.lemma(p.add_assoc, &[a_head_e, b_head_e, rests]);
            let step3 = rsymm(d, mid3, mid2, assoc);

            // ca·m + cb·m = (ca + cb)·m = ofInt(ca+cb)·m
            let ca_int = int_lit(d, a_head.1);
            let ca_rat = of_int(d, p, ca_int);
            let cb_int = int_lit(d, b_head.1);
            let cb_rat = of_int(d, p, cb_int);
            let mono = mono_expr(d, p, vars, &a_head.0);
            let coeff_sum = radd(d, ca_rat, cb_rat);
            let distrib_target = rmul(d, coeff_sum, mono);
            let distrib = d.lemma(p.right_distrib, &[ca_rat, cb_rat, mono]);
            let distrib_rev = rsymm(d, distrib_target, heads, distrib);
            let mid4 = radd(d, distrib_target, rests);
            let step4 = rcongr(d, heads, distrib_target, distrib_rev, &|d, t| {
                radd(d, t, rests)
            });

            let sum_int = d.iadd(ca_int, cb_int);
            let sum_rat = of_int(d, p, sum_int);
            let of_add = d.lemma(p.of_int_add, &[ca_int, cb_int]);
            let of_add_rev = rsymm(d, sum_rat, coeff_sum, of_add);
            let folded = rmul(d, sum_rat, mono);
            let mid5 = radd(d, folded, rests);
            let step5 = rcongr(d, coeff_sum, sum_rat, of_add_rev, &|d, t| {
                let inner = rmul(d, t, mono);
                radd(d, inner, rests)
            });

            let combined = a_head.1 + b_head.1;
            let (merged_rest, tail) = prove_merge(d, p, vars, a_rest, b_rest);
            let merged_rest_e = poly_expr(d, p, vars, &merged_rest);

            if combined == 0 {
                // ofInt 0 · m = m · 0 = 0, then 0 + R = R.
                let zero_c = rzero(d, p);
                let flipped = rmul(d, mono, sum_rat);
                let comm = d.lemma(p.mul_comm, &[sum_rat, mono]);
                let mul_zero = d.lemma(p.mul_zero, &[mono]);
                let (_, kill) =
                    super::ops::rchain(d, folded, &[(flipped, comm), (zero_c, mul_zero)]);
                let mid6 = radd(d, zero_c, rests);
                let step6 = rcongr(d, folded, zero_c, kill, &|d, t| radd(d, t, rests));
                let step7 = d.lemma(p.zero_add, &[rests]);
                let step8 = tail;

                let (_, proof) = super::ops::rchain(
                    d,
                    start,
                    &[
                        (mid1, step1),
                        (mid2, step2),
                        (mid3, step3),
                        (mid4, step4),
                        (mid5, step5),
                        (mid6, step6),
                        (rests, step7),
                        (merged_rest_e, step8),
                    ],
                );
                (merged_rest, proof)
            } else {
                let canon_head = (a_head.0.clone(), combined);
                let canon_head_e = term_expr(d, p, vars, &canon_head);
                let mid6 = radd(d, canon_head_e, rests);
                let step6 = crate::rat_prelude::ops::rrefl(d, mid6);

                let end = radd(d, canon_head_e, merged_rest_e);
                let step7 = rcongr(d, rests, merged_rest_e, tail, &|d, t| {
                    radd(d, canon_head_e, t)
                });

                let (_, proof) = super::ops::rchain(
                    d,
                    start,
                    &[
                        (mid1, step1),
                        (mid2, step2),
                        (mid3, step3),
                        (mid4, step4),
                        (mid5, step5),
                        (mid6, step6),
                        (end, step7),
                    ],
                );
                let mut merged = vec![canon_head];
                merged.extend(merged_rest);
                (merged, proof)
            }
        }
    }
}

/// `Σᵢ (ofInt kᵢ · poly_expr(Pᵢ)) = poly_expr(Σᵢ kᵢ·Pᵢ)` for CONSTANT
/// cofactors `kᵢ`, with the left-hand sum right-nested and NOT terminated in
/// zero (so the declared statement reads as the certificate writes it).
///
/// Folds from the right: [`prove_scale`] on the head, the recursive result on
/// the tail, then [`prove_merge`] to combine.
fn prove_const_combination(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    parts: &[(i128, IntPoly)],
) -> (ExprId, IntPoly, ExprId) {
    let ((k, poly), rest) = parts
        .split_first()
        .expect("prove_const_combination: at least one generator is required");
    let k_int = int_lit(d, *k);
    let k_rat = of_int(d, p, k_int);
    let poly_e = poly_expr(d, p, vars, poly);
    let head_e = rmul(d, k_rat, poly_e);
    let (scaled, scale_proof) = prove_scale(d, p, vars, *k, k_rat, k_int, poly);
    let scaled_e = poly_expr(d, p, vars, &scaled);

    if rest.is_empty() {
        return (head_e, scaled, scale_proof);
    }

    let (tail_e, tail_poly, tail_proof) = prove_const_combination(d, p, vars, rest);
    let start = radd(d, head_e, tail_e);
    let tail_poly_e = poly_expr(d, p, vars, &tail_poly);

    let mid1 = radd(d, scaled_e, tail_e);
    let step1 = rcongr(d, head_e, scaled_e, scale_proof, &|d, t| radd(d, t, tail_e));
    let mid2 = radd(d, scaled_e, tail_poly_e);
    let step2 = rcongr(d, tail_e, tail_poly_e, tail_proof, &|d, t| {
        radd(d, scaled_e, t)
    });

    let (merged, merge_proof) = prove_merge(d, p, vars, &scaled, &tail_poly);
    let merged_e = poly_expr(d, p, vars, &merged);

    let (_, proof) = super::ops::rchain(
        d,
        start,
        &[(mid1, step1), (mid2, step2), (merged_e, merge_proof)],
    );
    (start, merged, proof)
}

// ---------------------------------------------------------------------------
// The certificate side.
// ---------------------------------------------------------------------------

/// Produce `orthocentre-altitudes-concurrent`'s certificate from the CAS's own
/// corpus and certifier — the SAME artifact
/// `F:geometry-orthocentre-altitudes-concurrent` cites, not a hand-copy.
fn orthocentre_certificate() -> GeometryCertificate {
    let problem = geometry_corpus::corpus()
        .into_iter()
        .find(|p| p.id == "orthocentre-altitudes-concurrent")
        .expect("the CAS corpus must carry orthocentre-altitudes-concurrent");
    match certify(&problem, geometry_limits()) {
        ProofOutcome::Certified(cert) => *cert,
        other => panic!("the CAS must certify orthocentre-altitudes-concurrent: {other:?}"),
    }
}

/// Produce `thales-right-angle-in-semicircle`'s certificate from the CAS's
/// own corpus and certifier — the SAME artifact
/// `F:geometry-thales-right-angle-in-semicircle` cites, not a hand-copy.
fn thales_certificate() -> GeometryCertificate {
    let problem = geometry_corpus::corpus()
        .into_iter()
        .find(|p| p.id == "thales-right-angle-in-semicircle")
        .expect("the CAS corpus must carry thales-right-angle-in-semicircle");
    match certify(&problem, geometry_limits()) {
        ProofOutcome::Certified(cert) => *cert,
        other => panic!("the CAS must certify thales-right-angle-in-semicircle: {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// The translator, checked against NUMBERS rather than asserted.
    ///
    /// The kernel cannot tell us [`int_poly`] read the certificate correctly —
    /// it never sees the `MvPoly`. So the control is an evaluation at a point
    /// where the two hypotheses and the conclusion all take DIFFERENT values,
    /// computed independently here and compared against the CAS's own
    /// polynomials.
    ///
    /// The point is the certificate's own generic witness, `A = (0,0)`,
    /// `B = (4,0)`, `C = (1,3)`, `P = (1,1)`, at which all three vanish — so a
    /// second, DELIBERATELY OFF-configuration is evaluated too (`P = (2,1)`,
    /// where the true orthocentre is `(1,1)`), at which the values are `-3`,
    /// `-1` and `4`: three distinct nonzero numbers, so a transposition
    /// between any two of the three polynomials changes the answer. The
    /// three were recomputed by hand at that point and the first written
    /// guess was WRONG in all three slots — which is exactly why the
    /// assertion is against numbers and not against a shape.
    #[test]
    fn translator_reads_the_certificate_the_cas_produced() {
        let cert = orthocentre_certificate();
        assert_eq!(cert.coordinates.len(), 8, "eight coordinates");
        assert!(
            cert.saturations.is_empty(),
            "orthocentre needs no non-degeneracy condition, so there is no inverse variable"
        );
        assert_eq!(cert.generators.len(), 2, "two altitude hypotheses");
        assert_eq!(cert.conclusions.len(), 1, "one conclusion");

        let g0 = int_poly(&cert.generators[0]).expect("integer coefficients");
        let g1 = int_poly(&cert.generators[1]).expect("integer coefficients");
        let concl = int_poly(&cert.conclusions[0].poly).expect("integer coefficients");
        assert_eq!((g0.len(), g1.len(), concl.len()), (8, 8, 8));

        // Every cofactor is the constant -1; that is what makes this the
        // cheapest non-vacuous certificate of the ten.
        let cofactors: Vec<IntPoly> = cert.conclusions[0]
            .cofactors
            .iter()
            .map(|c| int_poly(c).expect("integer cofactor"))
            .collect();
        assert_eq!(
            cofactors,
            vec![vec![(Vec::new(), -1)], vec![(Vec::new(), -1)]],
            "both cofactors are the constant -1"
        );

        // On the certificate's own generic witness all three vanish.
        let generic: BTreeMap<&str, i128> = [
            ("ax", 0),
            ("ay", 0),
            ("bx", 4),
            ("by", 0),
            ("cx", 1),
            ("cy", 3),
            ("px", 1),
            ("py", 1),
        ]
        .into_iter()
        .collect();
        assert_eq!(eval_int_poly(&g0, &generic), 0, "AP ⟂ BC at the witness");
        assert_eq!(eval_int_poly(&g1, &generic), 0, "BP ⟂ CA at the witness");
        assert_eq!(eval_int_poly(&concl, &generic), 0, "CP ⟂ AB at the witness");

        // Off the orthocentre the three take three DISTINCT nonzero values,
        // so this point discriminates between the polynomials.
        let off: BTreeMap<&str, i128> = [
            ("ax", 0),
            ("ay", 0),
            ("bx", 4),
            ("by", 0),
            ("cx", 1),
            ("cy", 3),
            ("px", 2),
            ("py", 1),
        ]
        .into_iter()
        .collect();
        let (v0, v1, vc) = (
            eval_int_poly(&g0, &off),
            eval_int_poly(&g1, &off),
            eval_int_poly(&concl, &off),
        );
        assert_eq!((v0, v1, vc), (-3, -1, 4), "three distinct nonzero values");

        // And the identity itself, checked numerically at that same point:
        // conclusion = -g0 - g1, so 4 = 3 + 1.
        assert_eq!(vc, -v0 - v1, "the cofactor identity holds at the point");
    }

    /// The `IntPoly` arithmetic that [`prove_scale`] and [`prove_merge`] each
    /// mirror, checked independently of the kernel — including the ZERO-drop,
    /// which is the case the orthocentre identity exercises four times and the
    /// only one that changes the term COUNT.
    #[test]
    fn int_poly_arithmetic_drops_cancelling_monomials() {
        let cert = orthocentre_certificate();
        let g0 = int_poly(&cert.generators[0]).expect("integer coefficients");
        let g1 = int_poly(&cert.generators[1]).expect("integer coefficients");
        let concl = int_poly(&cert.conclusions[0].poly).expect("integer coefficients");

        let neg_g0 = scale_poly(-1, &g0);
        let neg_g1 = scale_poly(-1, &g1);
        assert_eq!(neg_g0.len(), 8);
        assert_eq!(neg_g1.len(), 8);

        let combined = add_poly(&neg_g0, &neg_g1);
        assert_eq!(
            combined.len(),
            8,
            "16 terms in, 8 out: four monomials cancel exactly"
        );
        assert_eq!(combined, concl, "-g0 - g1 IS the conclusion polynomial");

        // Negative control, and it must differ in a SMALL term: swapping the
        // sign of ONE cofactor gives +g0 - g1, which is a different
        // polynomial. Without this the assertion above could be satisfied by
        // an `add_poly` that ignored its arguments.
        let wrong = add_poly(&g0, &neg_g1);
        assert_ne!(
            wrong, concl,
            "+g0 - g1 must NOT equal the conclusion, or the test above is vacuous"
        );
    }

    /// The reconstruction: `Check.geometry_orthocentre_cofactor_identity`,
    /// admitted through [`Kernel::add_declaration`].
    ///
    /// ```text
    /// ∀ (ax ay bx by cx cy px py : Rat),
    ///   Rat.add (Rat.mul (Rat.ofInt 1) (Rat.mul ax cx)) (…)      -- CP ⟂ AB
    ///     = Rat.add (Rat.mul (Rat.ofInt (-1)) ⟨AP ⟂ BC⟩)
    ///               (Rat.mul (Rat.ofInt (-1)) ⟨BP ⟂ CA⟩)
    /// ```
    ///
    /// See the module doc for the four things this does NOT establish. The
    /// shortest of them: it is an identity between eight `Rat` variables, and
    /// nothing in the kernel knows they are coordinates.
    #[test]
    fn geometry_orthocentre_cofactor_identity_kernel_checked() {
        on_a_deep_stack(geometry_orthocentre_cofactor_identity_body);
    }

    fn geometry_orthocentre_cofactor_identity_body() {
        let cert = orthocentre_certificate();
        let g0 = int_poly(&cert.generators[0]).expect("integer coefficients");
        let g1 = int_poly(&cert.generators[1]).expect("integer coefficients");
        let concl = int_poly(&cert.conclusions[0].poly).expect("integer coefficients");
        let cofactors: Vec<i128> = cert.conclusions[0]
            .cofactors
            .iter()
            .map(|c| {
                let terms = int_poly(c).expect("integer cofactor");
                assert_eq!(terms.len(), 1, "cofactor must be a single constant term");
                assert!(terms[0].0.is_empty(), "cofactor must be CONSTANT");
                terms[0].1
            })
            .collect();

        let names: Vec<String> = cert.coordinates.clone();
        assert_eq!(
            names,
            vec!["ax", "ay", "bx", "by", "cx", "cy", "px", "py"],
            "the coordinate ORDER is the certificate's, not this test's"
        );

        let (mut kernel, prelude) = built();
        let anon = kernel.anon();
        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        let name = d
            .kernel()
            .name_str(anon, "Check.geometry_orthocentre_cofactor_identity");

        let parts: Vec<(i128, IntPoly)> =
            vec![(cofactors[0], g0.clone()), (cofactors[1], g1.clone())];
        let concl_for_build = concl.clone();

        let result = rat_theorem(&mut d, name, names.len(), &|d, fvars| {
            let vars: BTreeMap<String, ExprId> =
                names.iter().cloned().zip(fvars.iter().copied()).collect();
            let (rhs, merged, proof) = prove_const_combination(d, p, &vars, &parts);
            assert_eq!(
                merged, concl_for_build,
                "the emitted normal form must BE the certificate's conclusion"
            );
            let lhs = poly_expr(d, p, &vars, &concl_for_build);
            let stmt = crate::rat_prelude::ops::req(d, lhs, rhs);
            let flipped = rsymm(d, rhs, lhs, proof);
            (stmt, flipped)
        });
        result.expect("the kernel must admit the cofactor identity");

        // The trusted gate's own record: a Theorem, and axiom-free.
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

    /// The translator, checked against NUMBERS -- see
    /// `translator_reads_the_certificate_the_cas_produced` above for the same
    /// discipline applied to orthocentre.
    ///
    /// Thales has only ONE generator and ONE conclusion, and — unlike
    /// orthocentre's two DIFFERENT hypothesis polynomials that must be
    /// combined and partly cancel — the certificate's conclusion polynomial
    /// is BYTE-IDENTICAL to its generator (same 8 terms, same coefficients);
    /// the cofactor is the constant `1`. So there is no cross-wiring to
    /// control for (there is only one thing to wire), and no `add_poly`
    /// cancellation to exercise. The discriminator instead is a point OFF
    /// the circle, where the shared polynomial is a nonzero value
    /// independently hand-computed from the certificate's own coefficient
    /// list — a translator bug that silently produced the empty
    /// (always-zero) polynomial, or that dropped/mis-signed a term, cannot
    /// pass this.
    #[test]
    fn translator_reads_the_thales_certificate_the_cas_produced() {
        let cert = thales_certificate();
        assert_eq!(cert.coordinates.len(), 6, "six coordinates");
        assert!(
            cert.saturations.is_empty(),
            "thales needs no non-degeneracy condition"
        );
        assert_eq!(cert.generators.len(), 1, "one hypothesis: C lies on the circle");
        assert_eq!(cert.conclusions.len(), 1, "one conclusion: CA is perpendicular to CB");

        let hyp = int_poly(&cert.generators[0]).expect("integer coefficients");
        let concl = int_poly(&cert.conclusions[0].poly).expect("integer coefficients");
        assert_eq!((hyp.len(), concl.len()), (8, 8));
        assert_eq!(
            hyp, concl,
            "the conclusion polynomial IS the hypothesis polynomial, term for term -- \
             that coincidence is exactly Thales' theorem's algebraic content, and it is \
             checked HERE, at the Rust level, never by the kernel (see the reconstruction \
             test's doc comment)"
        );

        let cofactors: Vec<IntPoly> = cert.conclusions[0]
            .cofactors
            .iter()
            .map(|c| int_poly(c).expect("integer cofactor"))
            .collect();
        assert_eq!(
            cofactors,
            vec![vec![(Vec::new(), 1)]],
            "the single cofactor is the constant 1"
        );

        // The certificate's own generic witness: the unit semicircle
        // A = (-1,0), B = (1,0), C = (0,1). C is ON the circle, so both
        // polynomials vanish.
        let generic: BTreeMap<&str, i128> = [
            ("ax", -1),
            ("ay", 0),
            ("bx", 1),
            ("by", 0),
            ("cx", 0),
            ("cy", 1),
        ]
        .into_iter()
        .collect();
        assert_eq!(
            eval_int_poly(&hyp, &generic),
            0,
            "C is on the circle with diameter AB at the witness"
        );
        assert_eq!(
            eval_int_poly(&concl, &generic),
            0,
            "CA is perpendicular to CB at the witness"
        );

        // Off the circle -- C = (0,2), so |OC| = 2 != |OA| = 1 -- both
        // polynomials take the SAME nonzero value, hand-computed independently
        // from the certificate's own coefficient list:
        // ax*bx - ax*cx + ay*by - ay*cy - bx*cx - by*cy + cx^2 + cy^2
        //   = (-1)(1) - (-1)(0) + (0)(0) - (0)(2) - (1)(0) - (0)(2) + 0 + 4 = 3
        let off: BTreeMap<&str, i128> = [
            ("ax", -1),
            ("ay", 0),
            ("bx", 1),
            ("by", 0),
            ("cx", 0),
            ("cy", 2),
        ]
        .into_iter()
        .collect();
        assert_eq!(eval_int_poly(&hyp, &off), 3, "hand-computed value off the circle");
        assert_eq!(
            eval_int_poly(&concl, &off),
            3,
            "conclusion matches the hypothesis exactly, even off the witness"
        );
    }

    /// The reconstruction: `Check.geometry_thales_cofactor_identity`, admitted
    /// through [`Kernel::add_declaration`].
    ///
    /// **This identity is weaker than orthocentre's, and the difference is
    /// disclosed rather than hidden.** Orthocentre's kernel obligation
    /// genuinely combines two DIFFERENT polynomials additively, with real
    /// cancellation (16 terms in, 8 out). Thales's single cofactor is the
    /// constant `1` and its one generator is byte-identical to its
    /// conclusion, so `prove_const_combination`'s obligation degenerates to
    /// `poly_expr(concl) = Rat.ofInt 1 * poly_expr(hyp)` where `concl` and
    /// `hyp` are THE SAME `IntPoly`, hence THE SAME `ExprId` — a `mul_one`
    /// shaped fact true of ANY polynomial whatsoever, not one specific to
    /// this geometry. The substantive claim — that the CAS's independently
    /// derived polynomial forms of "C lies on the circle with diameter AB"
    /// and "CA ⟂ CB" coincide exactly — is checked ONLY by the Rust-level
    /// `assert_eq!(hyp, concl, ...)` in
    /// `translator_reads_the_thales_certificate_the_cas_produced`, never by
    /// `add_declaration`. What the kernel DOES independently confirm: that
    /// the translator's 8-term, 6-variable transcription of the certificate
    /// is a well-typed `Rat` expression obeying `left_distrib`/`mul_assoc`/
    /// `Rat.ofInt_mul` — the same assurance floor every other bridge in this
    /// family rests on, just without orthocentre's additional additive-
    /// combination content. See the module doc and this fact's own
    /// `axiom_footprint` for the full disclosure.
    #[test]
    fn geometry_thales_cofactor_identity_kernel_checked() {
        on_a_deep_stack(geometry_thales_cofactor_identity_body);
    }

    fn geometry_thales_cofactor_identity_body() {
        let cert = thales_certificate();
        let hyp = int_poly(&cert.generators[0]).expect("integer coefficients");
        let concl = int_poly(&cert.conclusions[0].poly).expect("integer coefficients");
        let cofactors: Vec<i128> = cert.conclusions[0]
            .cofactors
            .iter()
            .map(|c| {
                let terms = int_poly(c).expect("integer cofactor");
                assert_eq!(terms.len(), 1, "cofactor must be a single constant term");
                assert!(terms[0].0.is_empty(), "cofactor must be CONSTANT");
                terms[0].1
            })
            .collect();

        let names: Vec<String> = cert.coordinates.clone();
        assert_eq!(
            names,
            vec!["ax", "ay", "bx", "by", "cx", "cy"],
            "the coordinate ORDER is the certificate's, not this test's"
        );

        let (mut kernel, prelude) = built();
        let anon = kernel.anon();
        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        let name = d
            .kernel()
            .name_str(anon, "Check.geometry_thales_cofactor_identity");

        let parts: Vec<(i128, IntPoly)> = vec![(cofactors[0], hyp.clone())];
        let concl_for_build = concl.clone();

        let result = rat_theorem(&mut d, name, names.len(), &|d, fvars| {
            let vars: BTreeMap<String, ExprId> =
                names.iter().cloned().zip(fvars.iter().copied()).collect();
            let (rhs, merged, proof) = prove_const_combination(d, p, &vars, &parts);
            assert_eq!(
                merged, concl_for_build,
                "the emitted normal form must BE the certificate's conclusion"
            );
            let lhs = poly_expr(d, p, &vars, &concl_for_build);
            let stmt = crate::rat_prelude::ops::req(d, lhs, rhs);
            let flipped = rsymm(d, rhs, lhs, proof);
            (stmt, flipped)
        });
        result.expect("the kernel must admit the cofactor identity");

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
