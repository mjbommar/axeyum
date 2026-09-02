//! **`CReal.mvt_interiorExtremum`** (Spivak ch. 11, Theorem 3): the Mean
//! Value Theorem, on the same graded-family accounting as
//! [`super::rolle`]'s Rolle theorem, which this file's row 1 is a thin
//! wrapper over.
//!
//! ## Row 1: taking the extremum as a hypothesis, honestly — and via Rolle
//!
//! Classical MVT is Rolle's theorem applied to `g(x) := F(x) - (the chord
//! through `(lo, F lo)` and `(hi, F hi)`)`. Concretely, given a slope `m`
//! satisfying the secant equation `F hi ≡ F lo + m·(hi − lo)` (stated
//! without division, exactly the way this development avoids needing
//! `CReal` reciprocals whenever an equivalent multiplicative form exists),
//! `g(x) := F(x) − m·x` has `g(lo) ≡ g(hi)` **unconditionally from the
//! secant equation alone** (no extra hypothesis beyond `hslope`), and
//! `g'(x) = F'(x) − m` by [`super::derivative`]'s existing `hasDerivative_sub`
//! composed with a from-scratch (see below) derivative witness for the
//! linear map `x ↦ m·x`. Handing `g` to
//! [`super::rolle::declare_rolle`]'s `CReal.rolle_interiorExtremum`
//! **directly** — the extremum-of-`g` hypothesis this file's own statement
//! takes is exactly Rolle's own case-split hypothesis, unchanged — produces
//! `Equiv (g' c) zero`, i.e. `Equiv (F' c − m) zero`, and one
//! `neg_unique`/`double_neg` unwind (structurally the same closing move
//! [`super::rolle`]'s own min branch uses) turns that into the stated
//! conclusion `Equiv (F' c) m`.
//!
//! **This is genuinely thinner than Rolle's own wrapper over Fermat**: Rolle
//! still had to build a case split (`Or` of max/min) that Fermat's statement
//! does not carry; MVT needs no case split of its own at all — the `Or`
//! hypothesis this file states is `g`'s, and it is handed to
//! `rolle_interior_extremum` **verbatim**, with Rolle performing the
//! internal case analysis. The only genuinely new content here is the
//! auxiliary linear map's derivative, proved below.
//!
//! ## Why `hasDerivative_linear` is built from scratch, not via `hasDerivative_smul`
//!
//! [`super::derivative`] already has a scalar-multiple rule,
//! `hasDerivative_smul`, but its statement carries an extra hypothesis: a
//! `k : Nat` with `le (abs c) (ofRat (natDivSucc (Nat.succ k) 0))` — an
//! explicit magnitude bound on the scalar. For MVT's slope `m` (an arbitrary
//! `CReal`, not known in advance to be bounded by any particular natural),
//! discharging that bound would need an existential elimination through
//! `CReal.archimedean` and a bridge between `ofNat` and `ofRat
//! (natDivSucc (Nat.succ k) 0)` that does not obviously exist as a single
//! lemma — real work orthogonal to MVT itself.
//!
//! The linear map `x ↦ m·x` does not need any such bound: its difference
//! quotient is EXACTLY `m` for every pair `(x, y)`, unconditionally, by pure
//! ring algebra (`m·y − m·x − m·(y−x) ≡ 0`, via `left_distrib` and the usual
//! `neg`/`add` shuffle — the same "any modulus works, error ≡ 0
//! unconditionally" shape [`super::derivative`]'s own `hasDerivative_const`
//! and `hasDerivative_id` already use). So this file proves
//! `HasDerivativeOn (fun r => mul m r) (fun _ => m) lo hi` directly via
//! `HasDerivativeOn.mk`, mirroring `hasDerivative_const`/`hasDerivative_id`'s
//! construction, rather than composing `hasDerivative_smul` with
//! `hasDerivative_id`. It is **not** registered as its own `CReal.*` theorem
//! or `CRealPrelude` field — it is scaffolding internal to this file's own
//! proof term, exactly as `rolle.rs`'s min-branch algebra is internal to
//! `declare_rolle_interior_extremum` rather than its own combinator.
//!
//! ## Row 2: UNASSESSED, for the same reason `rolle.rs` records
//!
//! `rolle.rs`'s own module documentation records, in detail, why the
//! unrestricted (existential) form of Rolle does not reduce to
//! `creal/extreme_value.rs`'s decision-principle obstruction by any short
//! route it could find, and observes that **Rolle and MVT are equivalent up
//! to a chord subtraction, so a genuine row-2 construction for one is
//! probably adaptable to the other.** This file did not find such a
//! construction either (the same three auxiliary-function attempts
//! `rolle.rs` tried all transport verbatim through the chord subtraction:
//! `evtLinear v`'s issue is that scaling by `v` never moves the derivative's
//! zero location, which is exactly as true of `F(x) := x·(1−x)·v − (a chord
//! through two `v`-independent endpoints)` as it is of `evtLinear v` alone).
//! So: row 2 is **unassessed**, not refuted — nothing here derives `False`,
//! and per ADR-0603's vocabulary correction, "unassessed" is the honest
//! label for "several short reductions provably fail to separate", not
//! "asserted unavailable".
//!
//! ## Row 3: not a new statement — already the existing CAS certificate
//!
//! `crates/axeyum-cas/src/mvt.rs` already certifies the exact classical Mean
//! Value Theorem for polynomials with rational coefficients on a rational
//! closed interval (`F:cas-mvt-cubic-witness-sqrt3`), and its own module
//! documentation routes through Rolle applied to the SAME chord-subtracted
//! `g` this file's row 1 builds abstractly. `rolle.rs` already made the
//! judgement call that Rolle-on-polynomials is a SPECIALIZATION of that
//! certificate (`m ≡ 0`), not a distinct fact; MVT-on-polynomials is that
//! certificate at its STATED generality (`m` the secant slope, unrestricted).
//! So row 3 for MVT is not merely subsumed the way Rolle's is — it is the
//! literal general case the CAS module already names in its own type
//! signature. No new CAS file is added here, per ADR-0603's rule that two
//! routes proving the same statement are one fact with multiple evidence
//! rows, never duplicate facts.
//!
//! ## Row 4
//!
//! Not attempted, for the reason `rolle.rs` gives for its own row 4: rows 1
//! and 3 already cover the constructive and decidable fragments, and a
//! labeled import of the full classical existential statement would add
//! axiom-footprint-visible scaffolding without closing anything rows 1–3
//! leave open.

#![allow(clippy::too_many_arguments, clippy::many_single_char_names)]

use super::series::neg_zero_equiv;
use super::{CRealPrelude, cadd, cle, clt, creal_ty, div_succ, equiv};
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// Admit `CReal.mvt_interiorExtremum`. See the module documentation for the
/// graded-family accounting (which rows land, and why).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_mvt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_mvt_interior_extremum(d, p)
}

// --- shared term builders (private copies of idioms this development
// rebuilds per-module; see `derivative.rs`/`fermat.rs`/`rolle.rs`'s own
// identical disclaimers for why) ---------------------------------------------

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `add x (neg y)` — `x - y`.
fn cdiff(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    cadd(d, p, x, ny)
}

fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// Chain `Equiv start ...` through `(next, step)` pairs — the `echain` idiom
/// used throughout this development.
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `Equiv (add (neg x) x) zero` — the commuted form of `add_neg`. Copied
/// verbatim from `rolle.rs`/`fermat.rs`'s own private helper.
fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// From `h_ab_zero : Equiv (add a b) zero`, derive `Equiv b (neg a)`. Copied
/// verbatim from `rolle.rs`/`fermat.rs`'s own private helper.
fn neg_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h_ab_zero: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_a = cneg(d, p, a);

    let add_a_nega = cadd(d, p, a, neg_a);
    let add_nega_a = cadd(d, p, neg_a, a);
    let h_add_neg = d.lemma(p.add_neg, &[a]);
    let comm0 = d.lemma(p.add_comm, &[a, neg_a]);
    let symm_h = esymm(d, p, add_a_nega, zero_c, h_add_neg);
    let zero_equiv_nega_a = d.lemma(
        p.equiv_trans,
        &[zero_c, add_a_nega, add_nega_a, symm_h, comm0],
    );

    let add_b_zero = cadd(d, p, b, zero_c);
    let add_zero_b = cadd(d, p, zero_c, b);
    let h_addzero_b = d.lemma(p.add_zero, &[b]);
    let b_equiv_addbzero = esymm(d, p, add_b_zero, b, h_addzero_b);
    let comm_b0 = d.lemma(p.add_comm, &[b, zero_c]);
    let b_equiv_addzerob = d.lemma(
        p.equiv_trans,
        &[b, add_b_zero, add_zero_b, b_equiv_addbzero, comm_b0],
    );

    let addnega_a_plus_b = cadd(d, p, add_nega_a, b);
    let refl_b = erefl(d, p, b);
    let subst1 = d.lemma(
        p.add_congr,
        &[zero_c, add_nega_a, b, b, zero_equiv_nega_a, refl_b],
    );

    let a_plus_b = cadd(d, p, a, b);
    let nega_plus_aplusb = cadd(d, p, neg_a, a_plus_b);
    let assoc = d.lemma(p.add_assoc, &[neg_a, a, b]);

    let nega_plus_zero = cadd(d, p, neg_a, zero_c);
    let refl_nega = erefl(d, p, neg_a);
    let subst2 = d.lemma(
        p.add_congr,
        &[neg_a, neg_a, a_plus_b, zero_c, refl_nega, h_ab_zero],
    );

    let final_step = d.lemma(p.add_zero, &[neg_a]);

    echain(
        d,
        p,
        b,
        &[
            (add_zero_b, b_equiv_addzerob),
            (addnega_a_plus_b, subst1),
            (nega_plus_aplusb, assoc),
            (nega_plus_zero, subst2),
            (neg_a, final_step),
        ],
    )
}

/// `Equiv (neg (neg x)) x`. Copied verbatim from `rolle.rs`/`fermat.rs`'s
/// own private helper.
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (mul x (neg y)) (neg (mul x y))`. Copied verbatim from
/// `derivative.rs`'s own private helper.
fn mul_neg_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let xy = cmul(d, p, x, y);
    let x_ny = cmul(d, p, x, ny);
    let y_plus_ny = cadd(d, p, y, ny);
    let x_times_sum = cmul(d, p, x, y_plus_ny);

    let h_add_neg_y = d.lemma(p.add_neg, &[y]);
    let refl_x = erefl(d, p, x);
    let h_mulcongr = d.lemma(p.mul_congr, &[x, x, y_plus_ny, zero_c, refl_x, h_add_neg_y]);
    let x_zero = cmul(d, p, x, zero_c);
    let h_mulzero = d.lemma(p.mul_zero, &[x]);
    let sum_equiv_zero = echain(
        d,
        p,
        x_times_sum,
        &[(x_zero, h_mulcongr), (zero_c, h_mulzero)],
    );

    let h_ld = d.lemma(p.left_distrib, &[x, y, ny]);
    let sum_of_products = cadd(d, p, xy, x_ny);
    let symm_ld = esymm(d, p, x_times_sum, sum_of_products, h_ld);
    let h_sum_zero = d.lemma(
        p.equiv_trans,
        &[
            sum_of_products,
            x_times_sum,
            zero_c,
            symm_ld,
            sum_equiv_zero,
        ],
    );

    neg_unique(d, p, xy, x_ny, h_sum_zero)
}

/// `Equiv (neg (add a b)) (add (neg a) (neg b))`. Copied verbatim from
/// `derivative.rs`'s own private helper.
fn neg_add_distrib(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let ab = cadd(d, p, a, b);
    let na_nb = cadd(d, p, na, nb);
    let b_na = cadd(d, p, b, na);
    let na_b = cadd(d, p, na, b);
    let b_nanb = cadd(d, p, b, na_nb);
    let b_na_nb = cadd(d, p, b_na, nb);
    let na_b_nb = cadd(d, p, na_b, nb);
    let b_nb = cadd(d, p, b, nb);
    let na_bnb = cadd(d, p, na, b_nb);
    let na_zero = cadd(d, p, na, zero_c);
    let ab_nanb = cadd(d, p, ab, na_nb);
    let a_bnanb = cadd(d, p, a, b_nanb);
    let a_na = cadd(d, p, a, na);
    let neg_ab = cneg(d, p, ab);

    let step2 = d.lemma(p.add_assoc, &[b, na, nb]);
    let step2_symm = esymm(d, p, b_na_nb, b_nanb, step2);

    let step3 = d.lemma(p.add_comm, &[b, na]);
    let refl_nb = erefl(d, p, nb);
    let step4 = d.lemma(p.add_congr, &[b_na, na_b, nb, nb, step3, refl_nb]);

    let step5 = d.lemma(p.add_assoc, &[na, b, nb]);

    let step6 = d.lemma(p.add_neg, &[b]);
    let refl_na = erefl(d, p, na);
    let step7 = d.lemma(p.add_congr, &[na, na, b_nb, zero_c, refl_na, step6]);

    let step8 = d.lemma(p.add_zero, &[na]);

    let middle_result = echain(
        d,
        p,
        b_nanb,
        &[
            (b_na_nb, step2_symm),
            (na_b_nb, step4),
            (na_bnb, step5),
            (na_zero, step7),
            (na, step8),
        ],
    );

    let refl_a = erefl(d, p, a);
    let step9 = d.lemma(p.add_congr, &[a, a, b_nanb, na, refl_a, middle_result]);
    let step10 = d.lemma(p.add_neg, &[a]);

    let step1 = d.lemma(p.add_assoc, &[a, b, na_nb]);

    let h = echain(
        d,
        p,
        ab_nanb,
        &[(a_bnanb, step1), (a_na, step9), (zero_c, step10)],
    );

    let nu = neg_unique(d, p, ab, na_nb, h);
    esymm(d, p, na_nb, neg_ab, nu)
}

/// `Equiv (add (add q r) (neg q)) r` — cancelling a trailing `+q -q`.
fn cancel_right(d: &mut IntDev<'_>, p: CRealPrelude, q: ExprId, r: ExprId) -> ExprId {
    let neg_q = cneg(d, p, q);
    let qr = cadd(d, p, q, r);
    let qr_negq = cadd(d, p, qr, neg_q);
    let rq = cadd(d, p, r, q);
    let rq_negq = cadd(d, p, rq, neg_q);
    let q_negq = cadd(d, p, q, neg_q);
    let r_q_negq = cadd(d, p, r, q_negq);
    let zero_c = czero(d, p);
    let r_zero = cadd(d, p, r, zero_c);

    let comm1 = d.lemma(p.add_comm, &[q, r]);
    let refl_negq = erefl(d, p, neg_q);
    let step1 = d.lemma(p.add_congr, &[qr, rq, neg_q, neg_q, comm1, refl_negq]);
    let assoc = d.lemma(p.add_assoc, &[r, q, neg_q]);
    let an = d.lemma(p.add_neg, &[q]);
    let refl_r = erefl(d, p, r);
    let step2 = d.lemma(p.add_congr, &[r, r, q_negq, zero_c, refl_r, an]);
    let az = d.lemma(p.add_zero, &[r]);

    echain(
        d,
        p,
        qr_negq,
        &[
            (rq_negq, step1),
            (r_q_negq, assoc),
            (r_zero, step2),
            (r, az),
        ],
    )
}

/// `Equiv (add (add p_val (add q r)) (neg q)) (add p_val r)` — cancelling a
/// `+q -q` pair one level inside an outer sum, via [`cancel_right`] under
/// `add_assoc`.
fn cancel_middle_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    p_val: ExprId,
    q_val: ExprId,
    r_val: ExprId,
) -> ExprId {
    let neg_q = cneg(d, p, q_val);
    let qr = cadd(d, p, q_val, r_val);
    let p_qr = cadd(d, p, p_val, qr);
    let p_qr_negq = cadd(d, p, p_qr, neg_q);
    let qr_negq = cadd(d, p, qr, neg_q);
    let p_r = cadd(d, p, p_val, r_val);
    let p_qrnegq = cadd(d, p, p_val, qr_negq);

    let assoc = d.lemma(p.add_assoc, &[p_val, qr, neg_q]);
    let cr = cancel_right(d, p, q_val, r_val);
    let refl_p = erefl(d, p, p_val);
    let congr = d.lemma(p.add_congr, &[p_val, p_val, qr_negq, r_val, refl_p, cr]);

    echain(d, p, p_qr_negq, &[(p_qrnegq, assoc), (p_r, congr)])
}

/// `le (abs v) q` — the derivative's own two-argument closeness predicate.
/// Copied verbatim from `derivative.rs`'s own private helper.
fn within_real(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId, q: ExprId) -> ExprId {
    let magnitude = cabs(d, p, v);
    d.const_app(p.le, &[magnitude, q])
}

/// `CReal.HasDerivativeOn F F' a b`.
fn hd_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.has_derivative_on, &[f, fp, a, b])
}

/// `CReal -> CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `(term, proof)` = `(ofRat (natDivSucc k idx), le zero term)`. Copied
/// verbatim from `derivative.rs`'s own private helper.
fn nonneg_rat_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, idx: ExprId) -> (ExprId, ExprId) {
    let q = div_succ(d, p, k, idx);
    let ofr_q = d.const_app(p.of_rat, &[q]);
    let rzero_expr = crate::rat_prelude::ops::rzero(d, p.rat);
    let numerator = d.num(k);
    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[numerator, idx]);
    let proof = d.lemma(p.of_rat_le, &[rzero_expr, q, rat_nonneg]);
    (ofr_q, proof)
}

/// `(bound, proof)` = `(mul (ofRat (natDivSucc 1 e)) (abs diff), le zero
/// bound)`. Copied verbatim from `derivative.rs`'s own private helper.
fn error_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e: ExprId,
    diff_yx: ExprId,
) -> (ExprId, ExprId) {
    let (ofr_e, ofr_e_nonneg) = nonneg_rat_bound(d, p, 1, e);
    let abs_diff = cabs(d, p, diff_yx);
    let abs_diff_nonneg = d.lemma(p.abs_nonneg, &[diff_yx]);
    let bound = cmul(d, p, ofr_e, abs_diff);
    let bound_nonneg = d.lemma(
        p.mul_nonneg,
        &[ofr_e, abs_diff, ofr_e_nonneg, abs_diff_nonneg],
    );
    (bound, bound_nonneg)
}

/// From `v_equiv_zero : Equiv v zero` and `zero_le_bound : le zero bound`,
/// derive `le (abs v) bound`. Copied verbatim from `derivative.rs`'s own
/// private helper.
fn close_zero_error(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    v_equiv_zero: ExprId,
    zero_le_bound: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);

    let v_le_zero = d.lemma(p.le_of_equiv, &[v, zero_c, v_equiv_zero]);
    let h_upper = d.lemma(p.le_trans, &[v, zero_c, bound, v_le_zero, zero_le_bound]);

    let nv = cneg(d, p, v);
    let neg_zero_c = cneg(d, p, zero_c);
    let nv_eq_negzero = d.lemma(p.neg_congr, &[v, zero_c, v_equiv_zero]);
    let nz_eq = neg_zero_equiv(d, p);
    let nv_equiv_zero = echain(d, p, nv, &[(neg_zero_c, nv_eq_negzero), (zero_c, nz_eq)]);
    let nv_le_zero = d.lemma(p.le_of_equiv, &[nv, zero_c, nv_equiv_zero]);
    let h_lower = d.lemma(p.le_trans, &[nv, zero_c, bound, nv_le_zero, zero_le_bound]);

    d.lemma(p.abs_le, &[v, bound, h_upper, h_lower])
}

/// `Equiv (add (add (mul m y) (neg (mul m x))) (neg (mul m (add y (neg
/// x))))) zero` — the linear map `r ↦ m·r`'s difference-quotient error is
/// EXACTLY zero, unconditionally (no bound on `m` needed): `m·y − m·x −
/// m·(y−x) ≡ 0` by `left_distrib` plus the usual `neg`/`add` shuffle. See
/// the module documentation's "why from scratch" section.
fn linear_error_equiv_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    m: ExprId,
    x: ExprId,
    y: ExprId,
) -> (ExprId, ExprId) {
    let zero_c = czero(d, p);
    let a_val = cmul(d, p, m, y);
    let b_val = cmul(d, p, m, x);
    let neg_b = cneg(d, p, b_val);
    let big_x = cadd(d, p, a_val, neg_b);
    let neg_a = cneg(d, p, a_val);
    let big_y = cadd(d, p, neg_a, b_val);

    let neg_x = cneg(d, p, x);
    let diff_yx = cadd(d, p, y, neg_x);
    let mul_m_diffyx = cmul(d, p, m, diff_yx);
    let neg_mul_m_diffyx = cneg(d, p, mul_m_diffyx);

    let error = cadd(d, p, big_x, neg_mul_m_diffyx);

    // mul_m_diffyx ~ big_x, via left_distrib then mul_neg_equiv.
    let mul_m_negx = cmul(d, p, m, neg_x);
    let dist = d.lemma(p.left_distrib, &[m, y, neg_x]);
    let add_a_mmnegx = cadd(d, p, a_val, mul_m_negx);
    let mne = mul_neg_equiv(d, p, m, x);
    let refl_a = erefl(d, p, a_val);
    let step_b = d.lemma(p.add_congr, &[a_val, a_val, mul_m_negx, neg_b, refl_a, mne]);
    let diffyx_eq_x = echain(d, p, mul_m_diffyx, &[(add_a_mmnegx, dist), (big_x, step_b)]);

    // neg(mul_m_diffyx) ~ neg(big_x)
    let neg_x_ty = cneg(d, p, big_x);
    let step4 = d.lemma(p.neg_congr, &[mul_m_diffyx, big_x, diffyx_eq_x]);

    // neg(big_x) ~ big_y, via neg_add_distrib then double_neg.
    let nad = neg_add_distrib(d, p, a_val, neg_b);
    let nn_b = cneg(d, p, neg_b);
    let add_nega_nnb = cadd(d, p, neg_a, nn_b);
    let dn_b = double_neg(d, p, b_val);
    let refl_nega = erefl(d, p, neg_a);
    let step_y = d.lemma(p.add_congr, &[neg_a, neg_a, nn_b, b_val, refl_nega, dn_b]);
    let neg_x_eq_y = echain(d, p, neg_x_ty, &[(add_nega_nnb, nad), (big_y, step_y)]);

    // neg(mul_m_diffyx) ~ big_y
    let step8 = echain(
        d,
        p,
        neg_mul_m_diffyx,
        &[(neg_x_ty, step4), (big_y, neg_x_eq_y)],
    );

    // error ~ add(big_x, big_y)
    let refl_x = erefl(d, p, big_x);
    let error_to_addxy = d.lemma(
        p.add_congr,
        &[big_x, big_x, neg_mul_m_diffyx, big_y, refl_x, step8],
    );
    let add_x_y = cadd(d, p, big_x, big_y);

    // big_y ~ neg(big_x); add(big_x,big_y) ~ add(big_x, neg big_x) ~ zero.
    let y_eq_negx = esymm(d, p, neg_x_ty, big_y, neg_x_eq_y);
    let add_x_negx = cadd(d, p, big_x, neg_x_ty);
    let step_final_congr = d.lemma(
        p.add_congr,
        &[big_x, big_x, big_y, neg_x_ty, refl_x, y_eq_negx],
    );
    let an = d.lemma(p.add_neg, &[big_x]);

    let proof = echain(
        d,
        p,
        error,
        &[
            (add_x_y, error_to_addxy),
            (add_x_negx, step_final_congr),
            (zero_c, an),
        ],
    );
    (error, proof)
}

/// Builds `HasDerivativeOn (fun r => mul m r) (fun _ => m) lo hi` from
/// scratch — see the module documentation for why this is not
/// `hasDerivative_smul` composed with `hasDerivative_id`. Returns `(h, hp,
/// proof)`; `h`/`hp` are the exact lambda `ExprId`s the proof's inferred
/// type mentions, for the caller to reuse structurally (matching the
/// convention every `hasDerivative_*` combinator in `derivative.rs` already
/// follows).
pub(super) fn build_hd_linear(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    m: ExprId,
    lo: ExprId,
    hi: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let h_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let mr = cmul(d, p, m, r);
        d.lam_fv(r_fv, carrier, mr)
    };
    let hp_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, m)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let z = d.num(0);
        d.lam_fv(ignore_fv, nat, z)
    };

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let range_ax = cle(d, p, lo, x);
        let range_xb = cle(d, p, x, hi);
        let range_ay = cle(d, p, lo, y);
        let range_yb = cle(d, p, y, hi);

        let diff_yx = cdiff(d, p, y, x);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);

        let (error, error_equiv_zero) = linear_error_equiv_zero(d, p, m, x, y);
        let (bound, bound_nonneg) = error_bound(d, p, e, diff_yx);
        let conclusion = close_zero_error(d, p, error, bound, error_equiv_zero, bound_nonneg);

        let h = d.kernel().fvar(h_fv);
        let _ = h;
        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let proof = d.const_app(p.hd_mk, &[h_fn, hp_fn, lo, hi, modulus, spec]);
    (h_fn, hp_fn, proof)
}

/// `∀ x : CReal, le lo x → le x hi → le (f x) (f c)` — "`f` attains a
/// maximum at `c` over `[lo, hi]`". Copied verbatim from `rolle.rs`'s
/// private `hmax_ty`, applied here to the auxiliary `g`.
fn hmax_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    lo: ExprId,
    hi: ExprId,
    c: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let le_lo_x = cle(d, p, lo, x);
    let le_x_hi = cle(d, p, x, hi);
    let fx = d.apply(f, &[x]);
    let fc = d.apply(f, &[c]);
    let concl = cle(d, p, fx, fc);
    let after2 = d.arrow(le_x_hi, concl);
    let after1 = d.arrow(le_lo_x, after2);
    d.pi_fv(x_fv, carrier, after1)
}

/// `∀ x : CReal, le lo x → le x hi → le (f c) (f x)` — "`f` attains a
/// minimum at `c` over `[lo, hi]`". Copied verbatim from `rolle.rs`'s
/// private `hmin_ty`.
fn hmin_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    lo: ExprId,
    hi: ExprId,
    c: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let le_lo_x = cle(d, p, lo, x);
    let le_x_hi = cle(d, p, x, hi);
    let fx = d.apply(f, &[x]);
    let fc = d.apply(f, &[c]);
    let concl = cle(d, p, fc, fx);
    let after2 = d.arrow(le_x_hi, concl);
    let after1 = d.arrow(le_lo_x, after2);
    d.pi_fv(x_fv, carrier, after1)
}

/// `CReal.mvt_interiorExtremum` — see the module documentation for the
/// statement, the graded-family accounting, and the route through Rolle.
fn declare_mvt_interior_extremum(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let fn_carrier = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let lo_fv = d.fresh_fvar();
    let lo = d.kernel().fvar(lo_fv);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let hd_type = hd_ty(d, p, f, fp, lo, hi);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // hslope : Equiv (F hi) (add (F lo) (mul m (add hi (neg lo)))) — the
    // secant-slope equation, stated without division.
    let f_lo = d.apply(f, &[lo]);
    let f_hi = d.apply(f, &[hi]);
    let hslope_ty = {
        let hi_minus_lo = cdiff(d, p, hi, lo);
        let slope_term = cmul(d, p, m, hi_minus_lo);
        let rhs = cadd(d, p, f_lo, slope_term);
        equiv(d, p, f_hi, rhs)
    };
    let hslope_fv = d.fresh_fvar();
    let hslope = d.kernel().fvar(hslope_fv);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hlc_ty = clt(d, p, lo, c);
    let hlc_fv = d.fresh_fvar();
    let hlc = d.kernel().fvar(hlc_fv);
    let hch_ty = clt(d, p, c, hi);
    let hch_fv = d.fresh_fvar();
    let hch = d.kernel().fvar(hch_fv);

    // The auxiliary linear map h(r) := m*r and its from-scratch derivative.
    let (h_fn, hp_fn, hd_h) = build_hd_linear(d, p, m, lo, hi);

    // g := fun r => add (F r) (neg (h r)); gp := fun x => add (F' x) (neg (h'
    // x)) — the EXACT function terms `hasDerivative_sub`'s own substitution
    // produces (mirrors `derivative.rs::declare_has_derivative_sub`'s
    // `fsub`/`fsub_p` construction).
    let g_expr = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let hr = d.apply(h_fn, &[r]);
        let neg_hr = cneg(d, p, hr);
        let diff = cadd(d, p, fr, neg_hr);
        d.lam_fv(r_fv, carrier, diff)
    };
    let gp_expr = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let hpx = d.apply(hp_fn, &[x]);
        let neg_hpx = cneg(d, p, hpx);
        let diff = cadd(d, p, fpx, neg_hpx);
        d.lam_fv(x_fv, carrier, diff)
    };

    let hd_g = d.const_app(
        p.has_derivative_sub,
        &[f, fp, h_fn, hp_fn, lo, hi, hd, hd_h],
    );

    // heq : Equiv (g lo) (g hi) — from hslope alone, no extra hypothesis.
    let heq = {
        let h_lo = cmul(d, p, m, lo); // q_val's mirror at lo, reused as r_val below
        let h_hi = cmul(d, p, m, hi); // q_val
        let r_val = cneg(d, p, h_lo);
        let g_lo = cadd(d, p, f_lo, r_val);
        let neg_hhi_for_g = cneg(d, p, h_hi);
        let g_hi = cadd(d, p, f_hi, neg_hhi_for_g);

        // Expand the slope term: mul m (add hi (neg lo)) ~ add h_hi r_val.
        let neg_lo = cneg(d, p, lo);
        let mul_m_neglo = cmul(d, p, m, neg_lo);
        let ld = d.lemma(p.left_distrib, &[m, hi, neg_lo]);
        let add_hhi_mmneglo = cadd(d, p, h_hi, mul_m_neglo);
        let mne_lo = mul_neg_equiv(d, p, m, lo); // mul_m_neglo ~ r_val
        let refl_hhi = erefl(d, p, h_hi);
        let step_expand = d.lemma(
            p.add_congr,
            &[h_hi, h_hi, mul_m_neglo, r_val, refl_hhi, mne_lo],
        );
        let hi_minus_lo = cdiff(d, p, hi, lo);
        let slope_term = cmul(d, p, m, hi_minus_lo);
        let q_plus_r = cadd(d, p, h_hi, r_val);
        let slope_eq_qr = echain(
            d,
            p,
            slope_term,
            &[(add_hhi_mmneglo, ld), (q_plus_r, step_expand)],
        );

        // f_lo + slope_term ~ f_lo + (h_hi + r_val)
        let refl_flo = erefl(d, p, f_lo);
        let step_plus = d.lemma(
            p.add_congr,
            &[f_lo, f_lo, slope_term, q_plus_r, refl_flo, slope_eq_qr],
        );
        let p_plus_qr = cadd(d, p, f_lo, q_plus_r);
        let rhs = cadd(d, p, f_lo, slope_term);
        let f_hi_eq_pqr = echain(d, p, f_hi, &[(rhs, hslope), (p_plus_qr, step_plus)]);

        // g_hi = add(f_hi, neg h_hi) ~ add(p_plus_qr, neg h_hi)
        let neg_hhi = cneg(d, p, h_hi);
        let refl_neghhi = erefl(d, p, neg_hhi);
        let g_hi_eq = d.lemma(
            p.add_congr,
            &[f_hi, p_plus_qr, neg_hhi, neg_hhi, f_hi_eq_pqr, refl_neghhi],
        );
        let p_qr_negq = cadd(d, p, p_plus_qr, neg_hhi);

        // cancel h_hi: add(p_plus_qr, neg h_hi) ~ add(f_lo, r_val) = g_lo
        let cma = cancel_middle_add(d, p, f_lo, h_hi, r_val);

        let g_hi_to_g_lo = echain(d, p, g_hi, &[(p_qr_negq, g_hi_eq), (g_lo, cma)]);
        esymm(d, p, g_hi, g_lo, g_hi_to_g_lo)
    };

    let hmax_type = hmax_ty(d, p, g_expr, lo, hi, c);
    let hmin_type = hmin_ty(d, p, g_expr, lo, hi, c);
    let case_ty = d.or(hmax_type, hmin_type);
    let case_fv = d.fresh_fvar();
    let case = d.kernel().fvar(case_fv);

    // Apply Rolle to g, verbatim: no case split here, no new algebra beyond
    // undoing the subtraction on the conclusion.
    let h_rolle = d.const_app(
        p.rolle_interior_extremum,
        &[g_expr, gp_expr, lo, hi, hd_g, heq, c, hlc, hch, case],
    );
    // h_rolle : Equiv (gp_expr c) zero, treated as Equiv (add (F' c) (neg m))
    // zero — defeq via beta on gp_expr/hp_fn, the same convention
    // `rolle.rs`'s own min branch relies on for `fermat_interior_extremum`'s
    // output.
    let fp_c = d.apply(fp, &[c]);
    let neg_m = cneg(d, p, m);
    let nu = neg_unique(d, p, fp_c, neg_m, h_rolle); // Equiv(neg_m, neg(fp_c))
    let neg_fpc = cneg(d, p, fp_c);
    let step_negcongr = d.lemma(p.neg_congr, &[neg_m, neg_fpc, nu]);
    let neg_neg_m = cneg(d, p, neg_m);
    let neg_neg_fpc = cneg(d, p, neg_fpc);
    let dn_m = double_neg(d, p, m); // Equiv(neg_neg_m, m)
    let dn_m_symm = esymm(d, p, neg_neg_m, m, dn_m); // Equiv(m, neg_neg_m)
    let dn_fpc = double_neg(d, p, fp_c); // Equiv(neg_neg_fpc, fp_c)
    let m_to_fpc = echain(
        d,
        p,
        m,
        &[
            (neg_neg_m, dn_m_symm),
            (neg_neg_fpc, step_negcongr),
            (fp_c, dn_fpc),
        ],
    );
    let target_proof = esymm(d, p, m, fp_c, m_to_fpc); // Equiv(fp_c, m)

    let target = equiv(d, p, fp_c, m);

    let value = {
        let with_case = d.lam_fv(case_fv, case_ty, target_proof);
        let with_hch = d.lam_fv(hch_fv, hch_ty, with_case);
        let with_hlc = d.lam_fv(hlc_fv, hlc_ty, with_hch);
        let with_c = d.lam_fv(c_fv, carrier, with_hlc);
        let with_hslope = d.lam_fv(hslope_fv, hslope_ty, with_c);
        let with_m = d.lam_fv(m_fv, carrier, with_hslope);
        let with_hd = d.lam_fv(hd_fv, hd_type, with_m);
        let with_hi = d.lam_fv(hi_fv, carrier, with_hd);
        let with_lo = d.lam_fv(lo_fv, carrier, with_hi);
        let with_fp = d.lam_fv(fp_fv, fn_carrier, with_lo);
        d.lam_fv(f_fv, fn_carrier, with_fp)
    };
    let ty = {
        let after_case = d.arrow(case_ty, target);
        let after_hch = d.arrow(hch_ty, after_case);
        let after_hlc = d.arrow(hlc_ty, after_hch);
        let with_c = d.pi_fv(c_fv, carrier, after_hlc);
        let after_hslope = d.arrow(hslope_ty, with_c);
        let with_m = d.pi_fv(m_fv, carrier, after_hslope);
        let with_hd = d.pi_fv(hd_fv, hd_type, with_m);
        let with_hi = d.pi_fv(hi_fv, carrier, with_hd);
        let with_lo = d.pi_fv(lo_fv, carrier, with_hi);
        let with_fp = d.pi_fv(fp_fv, fn_carrier, with_lo);
        d.pi_fv(f_fv, fn_carrier, with_fp)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mvt.mvt_interior_extremum,
        uparams: vec![],
        ty,
        value,
    })
}

/// The kernel names `creal/mvt.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MvtNames {
    /// `CReal.mvt_interiorExtremum : ∀ F F' lo hi, HasDerivativeOn F F' lo
    /// hi → ∀ m, Equiv (F hi) (add (F lo) (mul m (add hi (neg lo)))) → ∀ c,
    /// lt lo c → lt c hi → (Or (∀ x, le lo x → le x hi → le (g x) (g c)) (∀
    /// x, le lo x → le x hi → le (g c) (g x))) → Equiv (F' c) m`, where `g :=
    /// fun r => add (F r) (neg (mul m r))` (`creal/mvt.rs`) — the Mean Value
    /// Theorem (Spivak ch. 11, Thm 3), a thin wrapper over
    /// [`super::CRealPrelude::rolle_interior_extremum`] applied to `g`: the secant-slope
    /// hypothesis makes `Equiv (g lo) (g hi)` provable UNCONDITIONALLY (pure
    /// algebra, no extra hypothesis), `g`'s derivative is `fun x => add (F'
    /// x) (neg m)` via [`super::CRealPrelude::has_derivative_sub`] composed with a
    /// from-scratch (not [`super::CRealPrelude::has_derivative_smul`], which would need an
    /// extra magnitude bound on `m`) derivative witness for `r ↦ m·r`, and
    /// the `Or` case-split hypothesis is Rolle's own, passed through
    /// verbatim with no case analysis performed in this theorem at all. See
    /// `creal/mvt.rs`'s module documentation for the full graded-family
    /// accounting (row 2 unassessed, row 3 already the existing CAS
    /// certificate).
    pub mvt_interior_extremum: NameId,
}

impl MvtNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            mvt_interior_extremum: kernel.name_str(creal, "mvt_interiorExtremum"),
        }
    }
}
