//! **`CReal.rolle_interiorExtremum`** (Spivak ch. 11, Theorem 2): if `F` is
//! differentiable on `[lo, hi]`, `F(lo)` and `F(hi)` are `Equiv`, and `c` is
//! an INTERIOR point (`lt lo c`, `lt c hi`) at which `F` attains EITHER a
//! maximum OR a minimum over `[lo, hi]`, then `F'(c)` is `Equiv`-zero.
//!
//! This is ADR-0603's graded family applied to Rolle's theorem. The honest
//! accounting, worked out below, is: **row 1 lands and is close to a thin
//! wrapper over [`super::fermat::declare_fermat`]'s
//! `CReal.fermat_interiorExtremum`**; row 2 (the unrestricted/existential
//! form's unprovability witness) does **not** land this session, and the
//! reasons are recorded rather than papered over; row 3 is **not a new
//! statement** — it already exists, subsumed by `crates/axeyum-cas/src/
//! mvt.rs`'s exact polynomial MVT, whose own module documentation names its
//! construction "Rolle's theorem applied to `g`" verbatim; row 4 (a labeled
//! import of the classical existential statement) is not attempted.
//!
//! ## Row 1: taking the extremum as a hypothesis, honestly
//!
//! Classical Rolle's proof has exactly one non-constructive step: applying
//! the Extreme Value Theorem to PRODUCE a point where `F` attains an
//! extremum over `[lo, hi]` (`creal/extreme_value.rs` shows this kernel
//! cannot do that in general — `evt_attained_max_decides_sign` reduces an
//! attained max to a decision principle this development lacks). Exactly as
//! [`super::fermat`]'s module documentation observes for Fermat's own
//! theorem, taking the extremum point `c` as a HYPOTHESIS rather than a
//! conclusion makes that non-constructive step never enter. Rolle adds
//! exactly one thing beyond Fermat's own statement: the classical theorem
//! does not tell you IN ADVANCE whether the extremum EVT would hand you is a
//! maximum or a minimum, so the honest row-1 statement takes
//! `Or (attains-max-at c) (attains-min-at c)` as its hypothesis rather than
//! `attains-max-at c` alone.
//!
//! **This is genuinely close to a thin wrapper, and this file says so rather
//! than padding it.** The max branch of the `Or` is `fermat_interior_extremum`
//! applied VERBATIM — no new mathematics. The min branch is `fermat_interior_
//! extremum` applied to `neg ∘ F` (via `CReal.hasDerivative_neg`, exactly the
//! device `creal/monotone.rs`'s `constant_of_zero_deriv` already uses for the
//! same "flip and undo" trick) followed by unwinding one `neg_congr` +
//! `double_neg` + `neg_zero_equiv` chain to turn `Equiv (neg (F' c)) zero`
//! back into `Equiv (F' c) zero`. Both branches are short, entirely
//! algebraic, and reuse existing theorems as black boxes. The one piece of
//! content beyond Fermat is packaging the case split — which branch of the
//! `Or` you are handed — into one statement, which is exactly what makes it
//! recognizable as ROLLE's theorem (an extremum of EITHER sign) rather than
//! Fermat's (a maximum, specifically) applied twice by the caller.
//!
//! `Equiv (F lo) (F hi)` is included as a hypothesis — faithful to Rolle's
//! classical statement — but, like `fermat_interior_extremum`'s own `hd`
//! modulus machinery being unneeded by `hmax`, it is **never consumed by this
//! proof**. Neither branch needs to know the endpoints agree; the maximizer
//! (or minimizer) hypothesis alone already pins `F'(c)` down. It is kept
//! anyway so the statement reads as Rolle's, matching the precedent
//! `creal/extreme_value.rs` sets for its own unused `le zero c`/`le c one`
//! hypotheses.
//!
//! ## Row 2: NOT landed — why the obvious reductions dodge the decision
//!
//! The natural question, per ADR-0603's own methodology
//! (`evt_attained_max_decides_sign` as the model): does the UNRESTRICTED
//! (existential) form of Rolle —
//!
//! ```text
//! ∀ F F' lo hi, HasDerivativeOn F F' lo hi → Equiv (F lo) (F hi) →
//!   ∃ c, lt lo c ∧ lt c hi ∧ Equiv (F' c) zero
//! ```
//!
//! — reduce to a decision principle this kernel lacks, ideally by a SHORT
//! derivation reusing `CReal.evt_linear`/`evt_attained_max_decides_sign`
//! directly, the way row 1 above reuses Fermat?
//!
//! **It was investigated and does not reduce that way, for a structural
//! reason worth recording.** Every natural attempt to build an auxiliary `F`
//! from `CReal.evtLinear v := fun t => mul t v` that (a) satisfies `F(lo) ≡
//! F(hi)` for EVERY `v` (needed since `v` must stay a free, undetermined
//! parameter) and (b) has a derivative whose zero LOCATION depends on the
//! sign of `v` runs into the same obstruction:
//!
//! - `F(t) := t·(1−t)·v` (or any `v · (polynomial in t)`) satisfies (a) — it
//!   vanishes at both endpoints of `[0, 1]` for every `v` — but its
//!   derivative is `v · (a polynomial in t alone)`, so scaling by `v` never
//!   MOVES a zero, it only rescales the derivative's magnitude. The critical
//!   point (`t = 1/2` here) is exactly computable with no information about
//!   `v` at all: a hypothetical Rolle-solver can always answer with the
//!   fixed rational point and reveal nothing.
//! - Building `F` so `v` enters ADDITIVELY rather than as an overall scalar
//!   factor (so the balance between a `v`-term and a `t`-term could
//!   genuinely shift the zero's location, mirroring how `evtLinear`'s own
//!   maximizer shifts between `t = 0` and `t = 1` with the sign of `v`)
//!   forces `F(lo) ≡ F(hi)` to hold only for ONE specific value of `v`
//!   (matching coefficients in the identity `F(lo) − F(hi) ≡ 0` for every
//!   `v` kills exactly the terms that would carry the useful dependence),
//!   not for `v` free.
//! - A genuinely separating construction along the lines the discriminant of
//!   a cubic `F'` suggests (something like `F(t) := t(t−2)(t−1+v)` on a
//!   symmetric setup, whose derivative has two real roots for every `v` but
//!   only one of them interior once `|v|` grows, with WHICH one interior
//!   flipping with the sign of `v`) is plausible on paper but needs exact
//!   `CReal.sqrt`/quadratic-root reasoning and a genuine case analysis on
//!   root position — a substantially larger undertaking than anything else
//!   in this file, and it was not attempted this session.
//!
//! So: **row 2 is neither proved nor refuted here.** Per ADR-0603's own
//! vocabulary correction, the honest label is that it is UNASSESSED beyond
//! the negative result above (several short reductions provably fail to
//! separate), not "asserted unavailable" (that would overclaim) and
//! certainly not "refuted" (nothing here derives `False`, and — as with EVT
//! and IVT — nothing could, since the classical conclusion is merely at
//! least as strong as an undecidable comparison, not inconsistent with
//! Bishop-style constructive mathematics).
//!
//! ## Row 3: not a new statement — already subsumed by the polynomial MVT
//!
//! `crates/axeyum-cas/src/mvt.rs` certifies the exact classical Mean Value
//! Theorem for polynomials with rational coefficients on a rational closed
//! interval, and its own module documentation is explicit that the
//! construction routes THROUGH Rolle: it builds `g(x) := p(x) − p(a) −
//! m·(x−a)` for the secant slope `m`, observes `g(a) = g(b) = 0` BY
//! CONSTRUCTION, and calls finding an interior root of `g'` "Rolle's theorem
//! applied to `g`" in its own prose. When the caller's `p` already satisfies
//! `p(a) = p(b)` (Rolle's own hypothesis, `m ≡ 0`), `g = p − p(a)` and `g' =
//! p'`, so the SAME certificate hands back a named root `c` of `p'` with
//! `p'(c) = 0` exactly — Rolle's classical conclusion, on the decidable
//! fragment, with a certificate.
//!
//! **Judgement call: this is not a distinct row-3 FACT for Rolle.** Per
//! ADR-0603 ("where classes overlap and two routes prove the SAME statement,
//! that is one fact with multiple evidence rows, never duplicate facts"),
//! Rolle-on-polynomials is a special case of MVT-on-polynomials, not a
//! separate mathematical statement needing its own CAS module. Writing a
//! second `polynomial_rolle` certificate that re-derives what
//! `verify_mvt_certificate` already does at `m = 0` would be exactly the
//! "two proofs of one fact that must stay in sync" antipattern this
//! project's own multi-agent hygiene notes warn against for kernel
//! declarations, and the same reasoning applies to CAS certificates. Row 3
//! for Rolle is `mvt.rs`'s existing certificate, specialized; no new file is
//! added here.
//!
//! ## Row 4
//!
//! Not attempted. Rows 1 and 3 already cover the constructive and decidable
//! fragments; a labeled import of the full classical existential statement
//! would add axiom-footprint-visible scaffolding without closing anything
//! rows 1–3 leave open, so it is left for a future session if the ledger
//! ever wants an explicit `imported-kernel-lean` row for cross-referencing.

#![allow(clippy::too_many_arguments, clippy::many_single_char_names)]

use super::{CRealPrelude, cadd, cle, clt, creal_ty};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Admit `CReal.rolle_interiorExtremum`. See the module documentation for
/// the graded-family accounting (which rows land, and why the other two do
/// not).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_rolle(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_rolle_interior_extremum(d, p)
}

// --- shared term builders (private copies of idioms this development
// rebuilds per-module; see `derivative.rs`/`deriv_unique.rs`/`fermat.rs`'s
// own identical disclaimers for why) -----------------------------------------

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// Chain `Equiv start ...` through `(next, step)` pairs — the `echain` idiom
/// used throughout this development. Copied verbatim from `fermat.rs`'s
/// private helper of the same shape.
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
/// verbatim from `derivative.rs`/`deriv_unique.rs`/`fermat.rs`'s private
/// helper.
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
/// verbatim from `fermat.rs`'s private helper of the same shape.
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

/// `Equiv (neg (neg x)) x`. Copied verbatim from `fermat.rs`'s private
/// helper (itself copied from `derivative.rs`).
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (neg zero) zero`. Copied verbatim from `fermat.rs`'s private
/// helper (itself copied from `derivative.rs`).
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]);
    let step1 = esymm(d, p, padded, nz, h1);
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]);
    let h3 = d.lemma(p.add_neg, &[zero_c]);
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `HasDerivativeOn F F' lo hi`.
fn hd_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    lo: ExprId,
    hi: ExprId,
) -> ExprId {
    d.const_app(p.has_derivative_on, &[f, fp, lo, hi])
}

/// `∀ x : CReal, le lo x → le x hi → le (F x) (F c)` — "`F` attains a maximum
/// at `c` over `[lo, hi]`". Verbatim shape of `fermat.rs`'s private
/// `hmax_ty`.
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

/// `∀ x : CReal, le lo x → le x hi → le (F c) (F x)` — "`F` attains a minimum
/// at `c` over `[lo, hi]`". The mirror image of [`hmax_ty`].
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

/// `CReal.rolle_interiorExtremum` — see the module documentation for the
/// statement, the graded-family accounting, and the two branches' proofs.
fn declare_rolle_interior_extremum(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
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

    // `Equiv (F lo) (F hi)` — faithful to Rolle's classical statement, never
    // consumed by either branch below (see the module documentation).
    let heq_ty = {
        let f_lo = d.apply(f, &[lo]);
        let f_hi = d.apply(f, &[hi]);
        super::equiv(d, p, f_lo, f_hi)
    };
    let heq_fv = d.fresh_fvar();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hlc_ty = clt(d, p, lo, c);
    let hlc_fv = d.fresh_fvar();
    let hlc = d.kernel().fvar(hlc_fv);
    let hch_ty = clt(d, p, c, hi);
    let hch_fv = d.fresh_fvar();
    let hch = d.kernel().fvar(hch_fv);

    let hmax_type = hmax_ty(d, p, f, lo, hi, c);
    let hmin_type = hmin_ty(d, p, f, lo, hi, c);
    let case_ty = d.or(hmax_type, hmin_type);
    let case_fv = d.fresh_fvar();
    let case = d.kernel().fvar(case_fv);

    let fp_c = d.apply(fp, &[c]);
    let zero_c = czero(d, p);
    let target = super::equiv(d, p, fp_c, zero_c);

    // --- max branch: `fermat_interior_extremum` applied directly -----------
    let on_max = |d: &mut IntDev<'_>, hmax: ExprId| -> ExprId {
        d.lemma(
            p.fermat_interior_extremum,
            &[f, fp, lo, hi, hd, c, hlc, hch, hmax],
        )
    };

    // --- min branch: apply `fermat_interior_extremum` to `neg ∘ F`, then
    // undo the negation on the conclusion --------------------------------
    let on_min = |d: &mut IntDev<'_>, hmin: ExprId| -> ExprId {
        let neg_f = {
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let fr = d.apply(f, &[r]);
            let nfr = cneg(d, p, fr);
            d.lam_fv(r_fv, carrier, nfr)
        };
        let neg_fp = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let fpx = d.apply(fp, &[x]);
            let nfpx = cneg(d, p, fpx);
            d.lam_fv(x_fv, carrier, nfpx)
        };
        let hd_neg = d.lemma(p.has_derivative_neg, &[f, fp, lo, hi, hd]);

        // hmax_g : ∀ x, le lo x → le x hi → le (neg_f x) (neg_f c), built
        // from hmin via `neg_le_neg` (mirrors `monotone.rs`'s own
        // `declare_constant_of_zero_deriv` use of `has_derivative_neg`).
        let hmax_g = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let f_c = d.apply(f, &[c]);
            let f_x = d.apply(f, &[x]);
            let hmin_x = d.apply(hmin, &[x, h1, h2]); // le (F c) (F x)
            let flipped = d.lemma(p.neg_le_neg, &[f_c, f_x, hmin_x]); // le (neg (F x)) (neg (F c))
            let le_lo_x = cle(d, p, lo, x);
            let le_x_hi = cle(d, p, x, hi);
            let with_h2 = d.lam_fv(h2_fv, le_x_hi, flipped);
            let with_h1 = d.lam_fv(h1_fv, le_lo_x, with_h2);
            d.lam_fv(x_fv, carrier, with_h1)
        };

        // Equiv (neg (F' c)) zero, up to beta on `neg_fp c`.
        let eq_neg_fpc_zero = d.lemma(
            p.fermat_interior_extremum,
            &[neg_f, neg_fp, lo, hi, hd_neg, c, hlc, hch, hmax_g],
        );

        // Undo the negation: F' c ~ neg (neg (F' c)) ~ neg zero ~ zero.
        let neg_fp_c = cneg(d, p, fp_c);
        let nn_fpc = cneg(d, p, neg_fp_c);
        let dn = double_neg(d, p, fp_c); // Equiv (neg (neg (F' c))) (F' c)
        let dn_symm = esymm(d, p, nn_fpc, fp_c, dn); // Equiv (F' c) (neg (neg (F' c)))
        let step = d.lemma(p.neg_congr, &[neg_fp_c, zero_c, eq_neg_fpc_zero]); // Equiv (neg (neg (F' c))) (neg zero)
        let neg_zero_c = cneg(d, p, zero_c);
        let nz = neg_zero_equiv(d, p); // Equiv (neg zero) zero
        echain(
            d,
            p,
            fp_c,
            &[(nn_fpc, dn_symm), (neg_zero_c, step), (zero_c, nz)],
        )
    };

    let body = d.or_elim(hmax_type, hmin_type, target, case, &on_max, &on_min);

    let value = {
        let with_case = d.lam_fv(case_fv, case_ty, body);
        let with_hch = d.lam_fv(hch_fv, hch_ty, with_case);
        let with_hlc = d.lam_fv(hlc_fv, hlc_ty, with_hch);
        let with_c = d.lam_fv(c_fv, carrier, with_hlc);
        let with_heq = d.lam_fv(heq_fv, heq_ty, with_c);
        let with_hd = d.lam_fv(hd_fv, hd_type, with_heq);
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
        let after_heq = d.arrow(heq_ty, with_c);
        let with_hd = d.pi_fv(hd_fv, hd_type, after_heq);
        let with_hi = d.pi_fv(hi_fv, carrier, with_hd);
        let with_lo = d.pi_fv(lo_fv, carrier, with_hi);
        let with_fp = d.pi_fv(fp_fv, fn_carrier, with_lo);
        d.pi_fv(f_fv, fn_carrier, with_fp)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.rolle_interior_extremum,
        uparams: vec![],
        ty,
        value,
    })
}
