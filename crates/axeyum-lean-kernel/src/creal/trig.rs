//! **`CReal.cosOne`** — the first transcendental-function-family constant in
//! this kernel, `cos 1 := Σ_{k≥0} (-1)^k/(2k)!`, built as a `CReal` the same
//! way `creal/exponential.rs` builds `CReal.e`: via `CReal.mk` on an
//! *explicit* regular sequence, never by `Exists`-elimination (`Exists.rec`
//! is `Prop`-only and cannot produce a term whose type mentions the
//! extracted witness).
//!
//! ## Route
//!
//! `CReal.cosTerm k := mul (pow (neg one) k) (expTerm (Nat.add k k))` — the
//! `k`-th term of the alternating series, `(-1)^k/(2k)!`, written with the
//! doubled index as `Nat.add k k` (not `Nat.mul 2 k`) so that
//! [`CRealPrelude::pow_add`] applies to it with **zero** reduction
//! bookkeeping: `pow half (Nat.add k k)` is symbolically `mul (pow half k)
//! (pow half k)`, no `Nat.mul` unfolding needed anywhere.
//!
//! The domination bound this file needs turns out to be *exactly* the one
//! `creal/exponential.rs` already built for `e`, reused unchanged rather than
//! re-derived: `expTerm (Nat.add k k) ≤ expDominant (Nat.add k k) ≤
//! expDominant k`, the last step a fresh but small monotonicity argument
//! (`pow half` squares between `0` and `1`, so doubling the exponent can only
//! shrink it). Composed with a **sign bound** — `abs (pow (neg one) k) ≤ one`
//! for every `k`, by induction, needing no case split on parity — and
//! [`CRealPrelude::abs_mul_le_of_bounds`] (`derivative.rs`'s two-variable
//! product-of-bounds lemma), this gives `abs (cosTerm k) ≤ expDominant k`
//! with **no new domination series**: `CReal.expDominantCauchy`'s own
//! machinery (reused, not re-derived) already closes `Cauchy (sumRange
//! cosTerm)`. Nothing here needed
//! [`CRealPrelude::sum_range_cauchy_of_abs_cauchy`]/
//! [`CRealPrelude::sum_range_converges_of_abs_converges`] after all — the
//! comparison test underneath both
//! ([`CRealPrelude::sum_range_cauchy_of_dominated`], and its raw-witnessed
//! half [`CRealPrelude::sum_range_cauchy_dominated_ordered_normalized`]) never
//! required `f`'s *sign*, only a pointwise bound on `abs (f k)` — so it
//! already covered a signed series, and the `abs`-wrapped convenience lemmas
//! turn out to be unnecessary machinery for this particular route, not a
//! missing piece.
//!
//! ## The concrete-witness constraint, and what it costs
//!
//! `CReal.mk` needs an actual `Regular` **proof term**, and
//! `CRealPrelude::regular_of_scaled_cauchy` needs a **raw**, unwrapped Cauchy
//! modulus (`∀ m n, Within (...) (natDivSucc K m + natDivSucc K n)` for a
//! concrete `K : Nat`) — not `Cauchy`'s own `∃ K, …` form, since the witness
//! `K` inside an `Exists` cannot be extracted as data
//! (`Exists.rec` is `Prop`-only). `CReal.e`'s own construction solves exactly
//! this problem for `Cauchy (sumRange expDominant)` via a private helper,
//! `exponential.rs::exp_dominant_cauchy_body_concrete`, that is not `pub`
//! (this session's other lane owns that file). Since `cosOne`'s own
//! domination series **is** `expDominant` — the same series `e` uses, not a
//! new one — this file reproduces that one private function (and its own
//! private dependencies: `mul_deshift`, `telescope_cauchy_pad2`,
//! `mul_ordered_half_body`, `promote_ordered_half_to_full`,
//! `cauchy_body_transport`, plus the small constant/arithmetic builders
//! `two`/`half`/`pow_half_fn`/`magnitude_of`) rather than editing that file or
//! duplicating its *mathematics* under a new name — matching this
//! development's established precedent of reproducing a sibling module's
//! private helper (`neg_zero_equiv_local`, `double_neg`, `echain`, each
//! duplicated per-file already) rather than widening its visibility. Nothing
//! here is a NEW geometric-series argument; every reproduced function is
//! copied unchanged and called with the exact arguments `e`'s own
//! construction uses, so the returned concrete `(K, proof)` pair for
//! `Cauchy (sumRange expDominant)` is identical to the one `CReal.e` itself
//! is built from.
//!
//! ## What is deliberately NOT built here
//!
//! - **General `cos : CReal → CReal`.** The general argument needs a bound
//!   depending on `|x|` (this file's domination is tied to the *specific*
//!   series for the constant `1`); a much larger climb, per this task's own
//!   brief.
//! - **`CReal.cosOneConverges`** (the analogue of `CReal.e_converges`, tying
//!   `cosOne` back to `Converges cosSeriesPartial cosOne`). `e`'s own analogue
//!   of this step needed a documented stack-overflow bisection
//!   (`declare_e_converges`'s module note: building generically over a bound
//!   `K` rather than the concrete `k_final`, to keep the two sides of a
//!   `def_eq` check from unfolding in lockstep) — real, non-obvious proof
//!   engineering this file does not attempt. `CReal.cosOne` itself (the raw
//!   `CReal.mk`-constructed value, well-typed and kernel-checked) is complete
//!   without it.
//! - **`0 ≤ cosOne ≤ 1`.** Not attempted (see the Kernel Facts note above
//!   about `e`'s own bound needing genuine case-split work at the low
//!   indices); left as a natural next step, now that a Cauchy witness for
//!   `sumRange cosTerm` at a concrete `K` exists.
//! - `π`, `sin`, and anything downstream of a root of `cos` — out of scope
//!   per this task's brief, and `creal/ivt.rs` explicitly refutes the
//!   exact-root construction.

use super::convergence::{
    converges_applied, converges_predicate, div_succ_at, exists_intro, kregular_of_cauchy_proof,
};
use super::product::{index_le, mul_index, mul_shift, regular_between};
use super::series::{assoc_rev_eq, fuse_same_index, sum_range_cauchy_body, within_symm};
use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, div_succ, embed, halves, sample, within};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::RatPrelude;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    den, den_z, iregroup4, normalize, num, one_le_succ, radd, rat_eq_rewrite, rchain, rcongr,
    req_motive, rmul, rneg, rone, rtransport, rzero,
};

/// Height for `cosTerm`/`cosSeriesPartial`: both are thin definitional
/// wrappers, mirroring `exponential.rs::EXP_HEIGHT`.
const TRIG_HEIGHT: u16 = DERIVED_HEIGHT + 1;

/// Admit `CReal.cosTerm`, `CReal.cosSeriesPartial`,
/// `CReal.cosTermAbsLeDominant` and `CReal.cosOne`. Run after
/// `exponential::declare_e_family` (needs `expTerm`, `expDominant`,
/// `exp_term_abs_le_dominant`, `geom_cauchy_ordered_half`,
/// `sum_range_cauchy_dominated_ordered_normalized`, `regular_of_scaled_cauchy`,
/// `speedup`, `mk`, `bound_within`, `mul_sum_range`,
/// `abs_mul_le_of_bounds` — all declared well before this point per
/// `creal.rs`'s own ordering).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_trig(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_cos_term(d, p)?;
    declare_cos_series_partial(d, p)?;
    declare_cos_term_abs_le_dominant(d, p)?;
    // `cos_one_ingredients` is computed ONCE and its (raw, k_final, body)
    // triple is threaded into BOTH `declare_cos_one` and
    // `declare_cos_one_converges` -- mirroring `exponential.rs::
    // declare_e_family`'s own `e_ingredients` sharing exactly, and for the
    // identical reason: `cosOneConverges`'s witness must be built from the
    // SAME concrete values `cosOne` itself was constructed from, not a
    // second, independently-derived (merely value-equal) copy.
    let (raw, k_final, cos_series_partial_body) = cos_one_ingredients(d, p);
    declare_cos_one(d, p, raw, k_final, cos_series_partial_body)?;
    declare_cos_one_converges(d, p, raw, k_final, cos_series_partial_body)?;
    declare_cos_one_le_four(d, p)?;
    declare_neg_four_le_cos_one(d, p)?;
    // `CReal.expTerm_antitone` needs only `expTerm`/`factorial` (declared
    // well above, in `exponential::declare_exponential`), not anything from
    // `alternating::declare_alternating` -- unlike the bracket
    // instantiation below, which DOES need `alternating_lower_bound`/
    // `alternating_upper_bound` and so cannot land in this function. See
    // [`declare_trig_alternating_bounds`], this file's second dispatch entry
    // point, called from `creal.rs` right after `alternating::
    // declare_alternating` for exactly this reason: referencing a name
    // declared in a LATER phase gives `UnknownConst`, not a missing-lemma
    // error, and looks exactly like the lemma does not exist.
    declare_exp_term_antitone(d, p)?;
    // The `Rat.normalize`/`Nat.gcd`-on-literals obstacle this file's own
    // `declare_cos_one_le_exp_term_zero` names as out of scope, solved
    // without touching `Nat.gcd`: see `exp_term_lit_eq_one`'s own doc.
    declare_exp_term_zero_eq_one(d, p)?;
    declare_exp_term_one_eq_one(d, p)
}

/// Second dispatch entry point for this file: the alternating-series
/// sharpening of `cosOne`'s numeric bound, needing
/// [`CRealPrelude::alternating_lower_bound`]/
/// [`CRealPrelude::alternating_upper_bound`]
/// (`alternating::declare_alternating`) — declared in a LATER phase than
/// [`declare_trig`], so this must be called from `creal.rs` AFTER
/// `alternating::declare_alternating`, not folded into `declare_trig`
/// itself. Builds: the bracket instantiated at `cosTerm`'s magnitude
/// sequence (`∀ m, le (E m) cosOne` / `∀ m, le cosOne (O m)`), and the two
/// `m = 0` corollaries this closes for free (`0 ≤ cosOne` and
/// `cosOne ≤ expTerm 0`) — this development's first concrete numeric facts
/// about `cosOne`, sharper than the prior `[-4, 4]` bound (which does not
/// even pin the sign).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_trig_alternating_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_cos_one_alternating_lower(d, p)?;
    declare_cos_one_alternating_upper(d, p)?;
    declare_cos_one_nonneg(d, p)?;
    declare_cos_one_le_exp_term_zero(d, p)
}

/// `CReal.sinOne`, mirroring [`declare_trig`] exactly except for the odd
/// index (`Nat.add (Nat.add k k) 1` in place of `Nat.add k k`). Run after
/// [`declare_trig`] (no ordering dependency on it beyond sharing the file's
/// local builders and `exponential::declare_e_family`'s machinery).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sin_trig(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_sin_term(d, p)?;
    declare_sin_series_partial(d, p)?;
    declare_sin_term_abs_le_dominant(d, p)?;
    let (raw, k_final, sin_series_partial_body) = sin_one_ingredients(d, p);
    declare_sin_one(d, p, raw, k_final, sin_series_partial_body)?;
    declare_sin_one_converges(d, p, raw, k_final, sin_series_partial_body)
}

/// The `sinOne` analogue of [`declare_trig_alternating_bounds`] — same
/// phase-order reason (needs `alternating_lower_bound`/
/// `alternating_upper_bound`, declared in a later phase than
/// [`declare_sin_trig`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sin_trig_alternating_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_sin_one_alternating_lower(d, p)?;
    declare_sin_one_alternating_upper(d, p)?;
    declare_sin_one_nonneg(d, p)?;
    declare_sin_one_le_exp_term_one(d, p)
}

// --- local builders, reproduced verbatim in shape from `exponential.rs`'s
// own private copies (each `creal/*` module keeps its own; see e.g.
// `geometric.rs::echain`, `derivative.rs::cneg`/`cmul`/`czero`). -------------

pub(super) fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

pub(super) fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

pub(super) fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

pub(super) fn one_c(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.one, vec![])
}

pub(super) fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

pub(super) fn cpow(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.pow, &[x, n])
}

pub(super) fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

pub(super) fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

/// `Equiv` chain composition, verbatim in shape to every other `creal/*`
/// module's own private `echain`.
pub(super) fn echain(
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

/// `Equiv a a`.
pub(super) fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// From `h : Equiv a b`, `Equiv b a`.
pub(super) fn esymm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// `Equiv (add (neg x) x) zero` — reproduced verbatim from `derivative.rs`'s
/// own private `neg_add_self`.
pub(super) fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// From `h_ab_zero : Equiv (add a b) zero`, `Equiv b (neg a)` — reproduced
/// verbatim from `derivative.rs`'s own private `neg_unique`.
pub(super) fn neg_unique(
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

    let addnega_a = cadd(d, p, neg_a, a);
    let addnega_a_plus_b = cadd(d, p, addnega_a, b);
    let refl_b = erefl(d, p, b);
    let subst1 = d.lemma(
        p.add_congr,
        &[zero_c, addnega_a, b, b, zero_equiv_nega_a, refl_b],
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

/// `Equiv (neg (neg x)) x` — reproduced verbatim from `derivative.rs`'s own
/// private `double_neg`.
pub(super) fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (neg zero) zero` — reproduced verbatim from `exponential.rs`'s own
/// private `neg_zero_equiv_local` (itself reproduced from `series.rs`).
pub(super) fn neg_zero_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]);
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]);
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]);
    let h3 = d.lemma(p.add_neg, &[zero_c]);
    let t1 = d.lemma(p.equiv_trans, &[nz, padded, flipped, step1, h2]);
    d.lemma(p.equiv_trans, &[nz, flipped, zero_c, t1, h3])
}

/// `le (neg one) one` — the one concrete numeric fact the sign bound needs at
/// its base case. `zero ≤ one` (`zero_lt_one`/`le_of_lt`), negated
/// (`neg_le_neg`) and folded back across `neg zero ~ zero`
/// ([`neg_zero_equiv_local`]).
fn neg_one_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);
    let zlo = d.lemma(p.zero_lt_one, &[]);
    let zero_le_one = d.lemma(p.le_of_lt, &[zero_c, one_cc, zlo]);
    let neg_one = cneg(d, p, one_cc);
    let step1 = d.lemma(p.neg_le_neg, &[zero_c, one_cc, zero_le_one]);
    let neg_zero = cneg(d, p, zero_c);
    let nz_equiv_z = neg_zero_equiv_local(d, p);
    let refl_negone = erefl(d, p, neg_one);
    let step2 = d.lemma(
        p.le_congr,
        &[
            neg_one,
            neg_one,
            neg_zero,
            zero_c,
            refl_negone,
            nz_equiv_z,
            step1,
        ],
    );
    d.lemma(p.le_trans, &[neg_one, zero_c, one_cc, step2, zero_le_one])
}

/// `le (abs (neg one)) one`, from [`neg_one_le_one`] and [`double_neg`].
fn abs_neg_one_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let n1_le_1 = neg_one_le_one(d, p);
    let dn = double_neg(d, p, one_cc);
    let nn = cneg(d, p, neg_one);
    let dn_symm = esymm(d, p, nn, one_cc, dn);
    let refl_one = erefl(d, p, one_cc);
    let one_le_one = d.lemma(p.le_refl, &[one_cc]);
    let step_b = d.lemma(
        p.le_congr,
        &[one_cc, nn, one_cc, one_cc, dn_symm, refl_one, one_le_one],
    );
    d.lemma(p.abs_le, &[neg_one, one_cc, n1_le_1, step_b])
}

/// `le (abs (pow (neg one) k)) one`, for every `k` — the sign of the
/// alternating series never leaves `[-1, 1]`. Induction on `k`: base is
/// `abs (pow (neg one) 0) = abs one ≤ one` ([`neg_one_le_one`], `pow_zero`
/// ι-reduction); step uses [`CRealPrelude::abs_mul_le_of_bounds`] at
/// `(pow (neg one) k, neg one, one, one)` (IH and [`abs_neg_one_le_one`])
/// against `pow (neg one) (succ k) = mul (pow (neg one) k) (neg one)`
/// (`pow_succ` ι-reduction), then folds `mul one one ~ one`.
pub(super) fn sign_abs_le_one(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let neg_one_bound = abs_neg_one_le_one(d, p);

    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId {
        let pw = cpow(d, p, neg_one, m);
        let abs_pw = cabs(d, p, pw);
        cle(d, p, abs_pw, one_cc)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let one_le_one = d.lemma(p.le_refl, &[one_cc]);
        let n1_le_1 = neg_one_le_one(d, p);
        d.lemma(p.abs_le, &[one_cc, one_cc, one_le_one, n1_le_1])
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        // ih : le (abs (pow (neg one) j)) one
        let pw = cpow(d, p, neg_one, j);
        let prod_bound = d.lemma(
            p.abs_mul_le_of_bounds,
            &[pw, neg_one, one_cc, one_cc, ih, neg_one_bound],
        );
        // prod_bound : le (abs (mul pw neg_one)) (mul one one)
        let mul_pw_negone = cmul(d, p, pw, neg_one);
        let mul_one_one = cmul(d, p, one_cc, one_cc);
        let abs_prod = cabs(d, p, mul_pw_negone);
        let mul_one_eq = d.lemma(p.mul_one, &[one_cc]); // Equiv (mul one one) one
        let refl_abs = erefl(d, p, abs_prod);
        d.lemma(
            p.le_congr,
            &[
                abs_prod,
                abs_prod,
                mul_one_one,
                one_cc,
                refl_abs,
                mul_one_eq,
                prod_bound,
            ],
        )
    };
    d.induct(&motive, &base, &step, k)
}

/// `Rat.natDivSucc 1 1` — `1/2`.
fn half_rat(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let one_nat = d.num(1);
    div_succ(d, p, 1, one_nat)
}

/// `CReal.ofRat (Rat.natDivSucc 1 1)` — the constant `1/2`.
fn half(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let hr = half_rat(d, p);
    embed(d, p, hr)
}

/// `le zero half`, reproduced verbatim from `exponential.rs`'s own private
/// `half_nonneg_proof`.
fn half_nonneg_proof(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rp = p.rat;
    let zero_rat = rzero(d, rp);
    let one_nat = d.num(1);
    let half_le_zero = d.lemma(rp.zero_le_nat_div_succ, &[one_nat, one_nat]);
    let hr = half_rat(d, p);
    d.lemma(p.of_rat_le, &[zero_rat, hr, half_le_zero])
}

/// `le half one`, from [`CRealPrelude::rat_index_ratio_le_one`] at index `1`
/// (`Rat.le (natDivSucc 1 1) Rat.one`, DIRECTLY the shape needed — no
/// `natDivSucc 1 0`-to-`Rat.one` bridge required).
fn half_le_one_proof(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rp = p.rat;
    let one_nat = d.num(1);
    let half_le_one_rat = d.lemma(p.rat_index_ratio_le_one, &[one_nat]);
    let hr = half_rat(d, p);
    let one_r = rone(d, rp);
    d.lemma(p.of_rat_le, &[hr, one_r, half_le_one_rat])
}

/// `Rat.normalize (Int.ofNat 2) (Nat.succ Nat.zero) h` — `2`, reproduced
/// verbatim from `exponential.rs`'s own private `two_normalize`. Returns
/// `(rat_term, numerator, denominator_positivity)`.
pub(super) fn two_normalize(d: &mut IntDev<'_>, _p: CRealPrelude) -> (ExprId, ExprId, ExprId) {
    let np = d.prelude();
    let two_nat = d.num(2);
    let two_z = d.of_nat(two_nat);
    let one_nat = d.num(1);
    let h1 = d.lemma(np.le_refl, &[one_nat]);
    let r = normalize(d, two_z, one_nat, h1);
    (r, two_z, h1)
}

/// `CReal.ofRat` of [`two_normalize`] — `CReal`'s constant `2`.
pub(super) fn two(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let (r, _, _) = two_normalize(d, p);
    embed(d, p, r)
}

/// `le zero two`, reproduced verbatim from `exponential.rs`'s own private
/// `two_nonneg_proof`.
fn two_nonneg_proof(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rp = p.rat;
    let zero_rat = rzero(d, rp);
    let (two_r, two_z, h1) = two_normalize(d, p);
    let value = two_r;
    let denom_pos = h1;
    let actual = num(d, value);
    let actual_den = den(d, value);
    let actual_den_z = den_z(d, value);
    let one = d.num(1);
    let denominator_z = d.of_nat(one);
    let zero = d.izero();
    let cross = d.lemma(rp.normalize_cross, &[two_z, one, denom_pos]);
    let product = d.imul(two_z, actual_den_z);
    let product_nonneg = {
        let two_nat = d.num(2);
        let magnitude = NatOps::mul(d, two_nat, actual_den);
        d.lemma(rp.int_zero_le_of_nat, &[magnitude])
    };
    let scaled = d.imul(actual, denominator_z);
    let back = d.isymm(scaled, product, cross);
    let scaled_nonneg = d.int_eq_rewrite(product, scaled, back, product_nonneg, &|d, x| {
        d.ile(zero, x)
    });
    let zero_scaled = d.imul(zero, denominator_z);
    let restore = d.lemma(rp.int_zero_mul, &[denominator_z]);
    let rebalanced = {
        let inverse = d.isymm(zero_scaled, zero, restore);
        d.int_eq_rewrite(zero, zero_scaled, inverse, scaled_nonneg, &|d, x| {
            d.ile(x, scaled)
        })
    };
    let cancelled = d.lemma(
        rp.int_le_of_mul_le_mul_right,
        &[zero, actual, one, denom_pos, rebalanced],
    );
    let proof = d.const_app(rp.nonneg_of_int_nonneg, &[value, cancelled]);
    d.lemma(p.of_rat_le, &[zero_rat, value, proof])
}

/// `λ i, CReal.pow half i`, reproduced verbatim from `exponential.rs`'s own
/// private `pow_half_fn`.
fn pow_half_fn(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let h = half(d, p);
    let body = cpow(d, p, h, i);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `mul two (pow half n)` — the `CReal.pow`-based reading of
/// `CReal.expDominant n`, reproduced verbatim from `exponential.rs`'s own
/// private `exp_dominant_at`.
fn exp_dominant_at(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let h = half(d, p);
    let t = two(d, p);
    let pw = cpow(d, p, h, n);
    cmul(d, p, t, pw)
}

/// `le (expDominant (Nat.add k k)) (expDominant k)`.
///
/// `expDominant (Nat.add k k) = mul two (pow half (Nat.add k k)) ~ mul two
/// (mul (pow half k) (pow half k))` (`CReal.pow_add`, zero reduction cost —
/// see the module documentation). `pow half k ∈ [0, 1]`
/// ([`CRealPrelude::pow_nonneg`]/[`CRealPrelude::pow_le_one`] at
/// [`half_nonneg_proof`]/[`half_le_one_proof`]), so squaring it can only
/// shrink it (`mul_le_mul_of_nonneg_left` against `pow half k ≤ one`, folded
/// by `mul_one`), and multiplying that bound through by the nonnegative `two`
/// closes it.
fn exp_dominant_double_le(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let h = half(d, p);
    let one_cc = one_c(d, p);
    let hk = cpow(d, p, h, k);
    let half_nonneg = half_nonneg_proof(d, p);
    let half_le_one = half_le_one_proof(d, p);
    let hnn = d.lemma(p.pow_nonneg, &[h, half_nonneg, k]);
    let hle1 = d.lemma(p.pow_le_one, &[h, half_nonneg, half_le_one, k]);
    let scale = d.lemma(p.mul_le_mul_of_nonneg_left, &[hk, hk, one_cc, hnn, hle1]);
    // scale : le (mul hk hk) (mul hk one)
    let mulone_hk = d.lemma(p.mul_one, &[hk]); // Equiv (mul hk one) hk
    let hk2 = cmul(d, p, hk, hk);
    let mul_hk_one = cmul(d, p, hk, one_cc);
    let refl_hk2 = erefl(d, p, hk2);
    let hk2_le_hk = d.lemma(
        p.le_congr,
        &[hk2, hk2, mul_hk_one, hk, refl_hk2, mulone_hk, scale],
    );

    let double_k = d.add(k, k);
    let pow_add_eq = d.lemma(p.pow_add, &[h, k, k]); // Equiv (pow h (add k k)) (mul hk hk)
    let pow_double = cpow(d, p, h, double_k);
    let pow_add_symm = esymm(d, p, pow_double, hk2, pow_add_eq); // Equiv hk2 pow_double
    let refl_hk = erefl(d, p, hk);
    let pow_double_le_hk = d.lemma(
        p.le_congr,
        &[hk2, pow_double, hk, hk, pow_add_symm, refl_hk, hk2_le_hk],
    );

    let two_c = two(d, p);
    let two_nonneg = two_nonneg_proof(d, p);
    d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[two_c, pow_double, hk, two_nonneg, pow_double_le_hk],
    )
}

/// `CReal.cosTerm : Nat → CReal := fun k => mul (pow (neg one) k) (expTerm
/// (Nat.add k k))`.
fn declare_cos_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_k = cpow(d, p, neg_one, k);
    let double_k = d.add(k, k);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_term = d.apply(exp_term_c, &[double_k]);
    let body = cmul(d, p, sign_k, e_term);

    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(TRIG_HEIGHT),
    })
}

/// `CReal.cosSeriesPartial : Nat → CReal := CReal.sumRange CReal.cosTerm`.
fn declare_cos_series_partial(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let value = d.const_app(p.sum_range, &[cos_term_c]);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_series_partial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(TRIG_HEIGHT),
    })
}

/// `CReal.cosTermAbsLeDominant : ∀ k, le (abs (cosTerm k)) (expDominant k)`.
///
/// `abs (cosTerm k) = abs (mul (pow (neg one) k) (expTerm (Nat.add k k)))`,
/// bounded via [`CRealPrelude::abs_mul_le_of_bounds`] at
/// `(pow (neg one) k, expTerm (Nat.add k k), one, expDominant (Nat.add k k))`
/// — [`sign_abs_le_one`] for the first bound,
/// [`CRealPrelude::exp_term_abs_le_dominant`] (already built for `e`, reused
/// unchanged) for the second — folding `mul one (expDominant (Nat.add k k))
/// ~ expDominant (Nat.add k k)` via `mul_comm`/`mul_one`, then
/// [`exp_dominant_double_le`] to bring the doubled index back down to `k`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_term_abs_le_dominant(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_k = cpow(d, p, neg_one, k);
    let sign_abs = sign_abs_le_one(d, p, k);

    let double_k = d.add(k, k);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_term = d.apply(exp_term_c, &[double_k]);
    let dom_double = exp_dominant_at(d, p, double_k);
    let dom_k = exp_dominant_at(d, p, k);

    let e_dom_bound = d.lemma(p.exp_term_abs_le_dominant, &[double_k]);
    // e_dom_bound : le (abs e_term) dom_double

    let prod_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[sign_k, e_term, one_cc, dom_double, sign_abs, e_dom_bound],
    );
    // prod_bound : le (abs (mul sign_k e_term)) (mul one_cc dom_double)

    let mul_comm_1e = d.lemma(p.mul_comm, &[one_cc, dom_double]);
    let mul_one_e = d.lemma(p.mul_one, &[dom_double]);
    let mul_one_cc_dom = cmul(d, p, one_cc, dom_double);
    let mul_dom_one = cmul(d, p, dom_double, one_cc);
    let one_dom_equiv = echain(
        d,
        p,
        mul_one_cc_dom,
        &[(mul_dom_one, mul_comm_1e), (dom_double, mul_one_e)],
    );

    let cos_term_k = cmul(d, p, sign_k, e_term);
    let abs_cos_term_k = cabs(d, p, cos_term_k);
    let refl_abs_cos = erefl(d, p, abs_cos_term_k);
    let abs_cos_le_dom_double = d.lemma(
        p.le_congr,
        &[
            abs_cos_term_k,
            abs_cos_term_k,
            mul_one_cc_dom,
            dom_double,
            refl_abs_cos,
            one_dom_equiv,
            prod_bound,
        ],
    );

    let dom_double_le_dom_k = exp_dominant_double_le(d, p, k);

    let final_bound = d.lemma(
        p.le_trans,
        &[
            abs_cos_term_k,
            dom_double,
            dom_k,
            abs_cos_le_dom_double,
            dom_double_le_dom_k,
        ],
    );

    let value = d.lam_fv(k_fv, nat, final_bound);
    let ty = {
        let stmt = cle(d, p, abs_cos_term_k, dom_k);
        d.pi_fv(k_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_term_abs_le_dominant,
        uparams: vec![],
        ty,
        value,
    })
}

// ----------------------------------------------------------------------------
// The concrete Cauchy witness for `Cauchy (sumRange expDominant)`, reproduced
// from `exponential.rs`'s own private helpers (see the module documentation
// for why: `CReal.e`'s own construction needs the identical value, but the
// function producing it is not `pub` and that file is owned by another lane
// this session).
// ----------------------------------------------------------------------------

fn div_succ_sym(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, idx: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, idx])
}

fn bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.bound, &[x])
}

/// `CReal.bound x + 1`, reproduced verbatim from `exponential.rs`'s own
/// private `magnitude_of` (itself reproduced from `product.rs`).
pub(super) fn magnitude_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let base = bound_of(d, p, x);
    d.succ(base)
}

/// `Eq (a*(b-c)) (a*b - a*c)`, reproduced verbatim from `exponential.rs`'s own
/// private `mul_sub_distrib`.
fn mul_sub_distrib(d: &mut IntDev<'_>, rat: RatPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let neg_c = rneg(d, c);
    let b_minus_c = rsub(d, rat, b, c);
    let start = rmul(d, a, b_minus_c);
    let ab = rmul(d, a, b);
    let a_negc = rmul(d, a, neg_c);
    let mid = radd(d, ab, a_negc);
    let ld = d.lemma(rat.left_distrib, &[a, b, neg_c]);
    let mul_neg_ac = d.lemma(rat.mul_neg, &[a, c]);
    let ac = rmul(d, a, c);
    let neg_ac = rneg(d, ac);
    let target = rsub(d, rat, ab, ac);
    let lifted = rcongr(d, a_negc, neg_ac, mul_neg_ac, &|d, t| radd(d, ab, t));
    let (_, chained) = rchain(d, start, &[(mid, ld), (target, lifted)]);
    chained
}

/// `Within (q * seq x high - q * seq x n) (natDivSucc (magnitude_of(c) * 2)
/// n)`, reproduced verbatim from `exponential.rs`'s own private
/// `mul_deshift`. Returns `(magnitude_of(c) * 2, proof)`.
pub(super) fn mul_deshift(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    q: ExprId,
    x: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let two_nat = d.num(2);
    let one_nat = d.num(1);

    let shift = mul_shift(d, p, c, x);
    let high = mul_index(d, shift, n);
    let high_le = index_le(d, p, one_nat, shift, n);
    let n_le = {
        let one_n = div_succ(d, p, 1, n);
        d.lemma(rat.le_refl, &[one_n])
    };
    let reg = regular_between(d, p, x, high, n, high_le, n_le, n);

    let hx = sample(d, p, x, high);
    let nx = sample(d, p, x, n);
    let diff_x = rsub(d, rat, hx, nx);
    let two_at_n = div_succ(d, p, 2, n);

    let c_bound = d.lemma(p.bound_within, &[c, high]);
    let ka = magnitude_of(d, p, c);
    let bound_value_c = div_succ_sym(d, p, ka, zero_nat);
    let ka_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[ka, zero_nat]);

    let (cl, cu) = halves(d, p, q, bound_value_c, c_bound);
    let (xl, xu) = halves(d, p, diff_x, two_at_n, reg);
    let scaled = d.lemma(
        rat.bounds_mul,
        &[
            q,
            bound_value_c,
            diff_x,
            two_at_n,
            ka_nonneg,
            cl,
            cu,
            xl,
            xu,
        ],
    );

    let distrib_eq = mul_sub_distrib(d, rat, q, hx, nx);
    let quantity_before = rmul(d, q, diff_x);
    let q_hx = rmul(d, q, hx);
    let q_nx = rmul(d, q, nx);
    let quantity_after = rsub(d, rat, q_hx, q_nx);
    let bound_before = rmul(d, bound_value_c, two_at_n);
    let distributed = rat_eq_rewrite(
        d,
        quantity_before,
        quantity_after,
        distrib_eq,
        scaled,
        &|d, t| within(d, p, t, bound_before),
    );

    let ka2 = NatOps::mul(d, ka, two_nat);
    let fuse = d.lemma(rat.nat_div_succ_mul, &[ka, two_nat, n]);
    let fused_bound = div_succ_sym(d, p, ka2, n);
    let final_proof = rat_eq_rewrite(d, bound_before, fused_bound, fuse, distributed, &|d, t| {
        within(d, p, quantity_after, t)
    });

    (ka2, final_proof)
}

/// Reproduced verbatim from `exponential.rs`'s own private
/// `telescope_cauchy_pad2`.
#[allow(clippy::too_many_arguments)]
pub(super) fn telescope_cauchy_pad2(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    w: ExprId,
    a: ExprId,
    b: ExprId,
    k: ExprId,
    e: ExprId,
    t1: ExprId,
    t2: ExprId,
    t3: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;

    let q1 = rsub(d, rat, x, y);
    let q2 = rsub(d, rat, y, z);
    let q3 = rsub(d, rat, z, w);
    let bound1 = d.const_app(rat.nat_div_succ, &[e, a]);
    let ka = d.const_app(rat.nat_div_succ, &[k, a]);
    let kb = d.const_app(rat.nat_div_succ, &[k, b]);
    let bound2 = radd(d, ka, kb);
    let bound3 = d.const_app(rat.nat_div_succ, &[e, b]);

    let (l1, u1) = halves(d, p, q1, bound1, t1);
    let (l2, u2) = halves(d, p, q2, bound2, t2);
    let c12 = d.lemma(rat.bounds_add, &[q1, bound1, q2, bound2, l1, u1, l2, u2]);
    let q12 = radd(d, q1, q2);
    let b12 = radd(d, bound1, bound2);

    let (l12, u12) = halves(d, p, q12, b12, c12);
    let (l3, u3) = halves(d, p, q3, bound3, t3);
    let c123 = d.lemma(rat.bounds_add, &[q12, b12, q3, bound3, l12, u12, l3, u3]);
    let q123 = radd(d, q12, q3);
    let b123 = radd(d, b12, bound3);

    let xw = rsub(d, rat, x, w);
    let assoc_q = d.lemma(rat.add_assoc, &[q1, q2, q3]);
    let q23 = radd(d, q2, q3);
    let q1_q23 = radd(d, q1, q23);
    let fuse_inner_q = d.lemma(rat.sub_add_sub, &[y, z, w]);
    let yw = rsub(d, rat, y, w);
    let lift_inner_q = rcongr(d, q23, yw, fuse_inner_q, &|d, t| radd(d, q1, t));
    let q1_yw = radd(d, q1, yw);
    let fuse_outer_q = d.lemma(rat.sub_add_sub, &[x, y, w]);
    let (_, quantity_chain) = rchain(
        d,
        q123,
        &[(q1_q23, assoc_q), (q1_yw, lift_inner_q), (xw, fuse_outer_q)],
    );
    let at_xw = rat_eq_rewrite(d, q123, xw, quantity_chain, c123, &|d, t| {
        within(d, p, t, b123)
    });

    let assoc_b = d.lemma(rat.add_assoc, &[bound1, bound2, bound3]);
    let b23 = radd(d, bound2, bound3);
    let bound1_23 = radd(d, bound1, b23);

    let assoc_inner_b = d.lemma(rat.add_assoc, &[ka, kb, bound3]);
    let kb_bound3 = radd(d, kb, bound3);
    let ka_kbbound3 = radd(d, ka, kb_bound3);
    let lift_assoc_inner = rcongr(d, b23, ka_kbbound3, assoc_inner_b, &|d, t| {
        radd(d, bound1, t)
    });
    let bound1_ka_kbbound3 = radd(d, bound1, ka_kbbound3);

    let (fused_b, fuse_b_eq) = fuse_same_index(d, p, k, e, b);
    let lift_fuse_b = rcongr(d, kb_bound3, fused_b, fuse_b_eq, &|d, t| {
        let inner = radd(d, ka, t);
        radd(d, bound1, inner)
    });
    let ka_fusedb = radd(d, ka, fused_b);
    let bound1_ka_fusedb = radd(d, bound1, ka_fusedb);

    let assoc_rev_1 = assoc_rev_eq(d, p, bound1, ka, fused_b);
    let bound1_ka = radd(d, bound1, ka);
    let bound1ka_fusedb = radd(d, bound1_ka, fused_b);

    let comm_1 = d.lemma(rat.add_comm, &[bound1, ka]);
    let ka_bound1 = radd(d, ka, bound1);
    let lift_comm = rcongr(d, bound1_ka, ka_bound1, comm_1, &|d, t| radd(d, t, fused_b));
    let kabound1_fusedb = radd(d, ka_bound1, fused_b);

    let (fused_a, fuse_a_eq) = fuse_same_index(d, p, k, e, a);
    let lift_fuse_a = rcongr(d, ka_bound1, fused_a, fuse_a_eq, &|d, t| {
        radd(d, t, fused_b)
    });
    let target = radd(d, fused_a, fused_b);

    let (_, bound_chain) = rchain(
        d,
        b123,
        &[
            (bound1_23, assoc_b),
            (bound1_ka_kbbound3, lift_assoc_inner),
            (bound1_ka_fusedb, lift_fuse_b),
            (bound1ka_fusedb, assoc_rev_1),
            (kabound1_fusedb, lift_comm),
            (target, lift_fuse_a),
        ],
    );

    let final_proof = rat_eq_rewrite(d, b123, target, bound_chain, at_xw, &|d, t| {
        within(d, p, xw, t)
    });

    let k_plus_e = d.add(k, e);
    (k_plus_e, final_proof)
}

/// Reproduced verbatim from `exponential.rs`'s own private
/// `mul_ordered_half_body`.
#[allow(clippy::too_many_arguments)]
pub(super) fn mul_ordered_half_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    q: ExprId,
    s: ExprId,
    k_s: ExprId,
    a: ExprId,
    b: ExprId,
    s_ordered_half: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
    hab: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let sa = d.apply(s, &[a]);
    let sb = d.apply(s, &[b]);
    let g_a = cmul(d, p, c, sa);
    let g_b = cmul(d, p, c, sb);

    let (ka2, mdb) = mul_deshift(d, p, c, q, sb, b);
    let (_, mda) = mul_deshift(d, p, c, q, sa, a);

    let sb_b = sample(d, p, sb, b);
    let sa_a = sample(d, p, sa, a);
    let q_sb_b = rmul(d, q, sb_b);
    let q_sa_a = rmul(d, q, sa_a);
    let g_a_a = sample(d, p, g_a, a);
    let ka2_at_a = div_succ_sym(d, p, ka2, a);
    let mda_flip = within_symm(d, p, g_a_a, q_sa_a, ka2_at_a, mda);

    let s_gap = s_ordered_half(d, a, b, hab);
    let ka = magnitude_of(d, p, c);
    let zero_nat = d.num(0);
    let bound_value_c = div_succ_sym(d, p, ka, zero_nat);
    let ka_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[ka, zero_nat]);
    let c_bound_mid = d.lemma(p.bound_within, &[c, b]);
    let seven_b = div_succ_sym(d, p, k_s, b);
    let seven_a = div_succ_sym(d, p, k_s, a);
    let bnd7 = radd(d, seven_b, seven_a);
    let diff_s = rsub(d, rat, sb_b, sa_a);
    let (cl, cu) = halves(d, p, q, bound_value_c, c_bound_mid);
    let (sl, su) = halves(d, p, diff_s, bnd7, s_gap);
    let scaled_mid = d.lemma(
        rat.bounds_mul,
        &[q, bound_value_c, diff_s, bnd7, ka_nonneg, cl, cu, sl, su],
    );
    let distrib_mid = mul_sub_distrib(d, rat, q, sb_b, sa_a);
    let quantity_mid_before = rmul(d, q, diff_s);
    let quantity_mid_after = rsub(d, rat, q_sb_b, q_sa_a);
    let bound_mid_before = rmul(d, bound_value_c, bnd7);
    let distributed_mid = rat_eq_rewrite(
        d,
        quantity_mid_before,
        quantity_mid_after,
        distrib_mid,
        scaled_mid,
        &|d, t| within(d, p, t, bound_mid_before),
    );

    let ld_mid = d.lemma(rat.left_distrib, &[bound_value_c, seven_b, seven_a]);
    let head_mid = rmul(d, bound_value_c, seven_b);
    let tail_mid = rmul(d, bound_value_c, seven_a);
    let mid1 = radd(d, head_mid, tail_mid);
    let fuse_b_mid = d.lemma(rat.nat_div_succ_mul, &[ka, k_s, b]);
    let fuse_a_mid = d.lemma(rat.nat_div_succ_mul, &[ka, k_s, a]);
    let kg_num = NatOps::mul(d, ka, k_s);
    let kg_b = div_succ_sym(d, p, kg_num, b);
    let kg_a = div_succ_sym(d, p, kg_num, a);
    let lift_b_mid = rcongr(d, head_mid, kg_b, fuse_b_mid, &|d, t| radd(d, t, tail_mid));
    let mid2 = radd(d, kg_b, tail_mid);
    let lift_a_mid = rcongr(d, tail_mid, kg_a, fuse_a_mid, &|d, t| radd(d, kg_b, t));
    let mid3 = radd(d, kg_b, kg_a);
    let (_, mid_chain) = rchain(
        d,
        bound_mid_before,
        &[(mid1, ld_mid), (mid2, lift_b_mid), (mid3, lift_a_mid)],
    );
    let mid_final = rat_eq_rewrite(
        d,
        bound_mid_before,
        mid3,
        mid_chain,
        distributed_mid,
        &|d, t| within(d, p, quantity_mid_after, t),
    );

    let g_b_b = sample(d, p, g_b, b);
    let (k_total, proof) = telescope_cauchy_pad2(
        d, p, g_b_b, q_sb_b, q_sa_a, g_a_a, b, a, kg_num, ka2, mdb, mid_final, mda_flip,
    );
    (k_total, proof)
}

/// Promote an ordered-pair `Within` bound (`a ≤ b`) into the full, unordered
/// `sum_range_cauchy_body`-shaped statement, reproduced verbatim from
/// `exponential.rs`'s own private `promote_ordered_half_to_full`.
pub(super) fn promote_ordered_half_to_full(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    func: ExprId,
    k: ExprId,
    ordered_half: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let fm = d.apply(func, &[m]);
    let fn_val = d.apply(func, &[n]);
    let y_m = sample(d, p, fm, m);
    let z_n = sample(d, p, fn_val, n);
    let diff_mn = rsub(d, rat, y_m, z_n);
    let bm = div_succ_sym(d, p, k, m);
    let bn = div_succ_sym(d, p, k, n);
    let bound_mn = radd(d, bm, bn);
    let claim_mn = within(d, p, diff_mn, bound_mn);

    let left_ty = d.le(m, n);
    let right_ty = d.le(n, m);
    let total_mn = {
        let name = d.prelude().le_total;
        d.const_app(name, &[m, n])
    };

    let body = d.or_elim(
        left_ty,
        right_ty,
        claim_mn,
        total_mn,
        &|d, hmn| {
            let raw = ordered_half(d, m, n, hmn);
            let bn2 = div_succ_sym(d, p, k, n);
            let bm2 = div_succ_sym(d, p, k, m);
            let bound_nm = radd(d, bn2, bm2);
            let flipped = within_symm(d, p, z_n, y_m, bound_nm, raw);
            let comm_eq = d.lemma(rat.add_comm, &[bn2, bm2]);
            rat_eq_rewrite(d, bound_nm, bound_mn, comm_eq, flipped, &|d, t| {
                within(d, p, diff_mn, t)
            })
        },
        &|d, hnm| ordered_half(d, n, m, hnm),
    );
    let over_n = d.lam_fv(n_fv, nat, body);
    d.lam_fv(m_fv, nat, over_n)
}

/// Given `heq : ∀n, Equiv (G n) (F n)` and `hbody : sum_range_cauchy_body (G,
/// k)`, build `(k+2, sum_range_cauchy_body (F, k+2))`, reproduced verbatim
/// from `exponential.rs`'s own private `cauchy_body_transport`.
pub(super) fn cauchy_body_transport(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    g: ExprId,
    f: ExprId,
    heq: ExprId,
    k: ExprId,
    hbody: ExprId,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let gm = d.apply(g, &[m]);
    let gn = d.apply(g, &[n]);
    let fm = d.apply(f, &[m]);
    let fn_val = d.apply(f, &[n]);

    let x = sample(d, p, fm, m);
    let y = sample(d, p, gm, m);
    let z = sample(d, p, gn, n);
    let w = sample(d, p, fn_val, n);

    let heq_m_outer = d.apply(heq, &[m]);
    let heq_m = d.apply(heq_m_outer, &[m]);
    let two_at_m = div_succ(d, p, 2, m);
    let t1 = within_symm(d, p, y, x, two_at_m, heq_m);

    let t2 = {
        let outer = d.apply(hbody, &[m]);
        d.apply(outer, &[n])
    };

    let heq_n_outer = d.apply(heq, &[n]);
    let t3 = d.apply(heq_n_outer, &[n]);

    let two_nat_local = d.num(2);
    let (k_plus_2, proof) =
        telescope_cauchy_pad2(d, p, x, y, z, w, m, n, k, two_nat_local, t1, t2, t3);

    let over_n = d.lam_fv(n_fv, nat, proof);
    (k_plus_2, d.lam_fv(m_fv, nat, over_n))
}

/// A CONCRETE `(K, proof : sum_range_cauchy_body (sumRange expDominant) K)`,
/// reproduced verbatim from `exponential.rs`'s own private
/// `exp_dominant_cauchy_body_concrete` — the SAME value `CReal.e`'s own
/// construction uses, so `cosOne`'s domination series does not need a fresh
/// concrete Cauchy witness of its own.
pub(super) fn exp_dominant_cauchy_body_concrete(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let raw_pow_half = pow_half_fn(d, p);
    let s_fn = d.const_app(p.sum_range, &[raw_pow_half]);
    let two_creal = two(d, p);
    let (two_rat, _, _) = two_normalize(d, p);

    let seven_nat = d.num(7);
    let two_nat = d.num(2);
    let ka = magnitude_of(d, p, two_creal);
    let kg_num = NatOps::mul(d, ka, seven_nat);
    let ka2 = NatOps::mul(d, ka, two_nat);
    let k_g = d.add(kg_num, ka2);

    let g_fn = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.apply(s_fn, &[n]);
        let prod = cmul(d, p, two_creal, sn);
        d.lam_fv(n_fv, nat, prod)
    };

    let ordered_half = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, hab: ExprId| -> ExprId {
        let (_, proof) = mul_ordered_half_body(
            d,
            p,
            two_creal,
            two_rat,
            s_fn,
            seven_nat,
            a,
            b,
            &|d, aa, bb, hh| d.lemma(p.geom_cauchy_ordered_half, &[aa, bb, hh]),
            hab,
        );
        proof
    };

    let g_case_proof = promote_ordered_half_to_full(d, p, g_fn, k_g, &ordered_half);

    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let f_fn = d.const_app(p.sum_range, &[exp_dominant_const]);
    let heq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.lemma(p.mul_sum_range, &[two_creal, raw_pow_half, n]);
        d.lam_fv(n_fv, nat, body)
    };

    cauchy_body_transport(d, p, g_fn, f_fn, heq, k_g, g_case_proof)
}

/// `λ n, CReal.seq (f n) n`, reproduced verbatim from `exponential.rs`'s own
/// private `diagonal_seq` (itself reproduced from `convergence.rs`).
fn diagonal_seq(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(f, &[n]);
    let body = sample(d, p, fn_term, n);
    d.lam_fv(n_fv, nat, body)
}

/// `(raw, k_final, cos_series_partial_body)` — the ingredients
/// [`declare_cos_one`] needs, mirroring `exponential.rs::e_ingredients`
/// exactly except for the domination hypothesis
/// (`CReal.cosTermAbsLeDominant` in place of `exp_term_abs_le_dominant`) and
/// the target series (`cosSeriesPartial` in place of `expSeriesPartial`).
fn cos_one_ingredients(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId, ExprId) {
    let (k_dom, hyp2) = exp_dominant_cauchy_body_concrete(d, p);

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let cos_series_partial_c = d.kernel().const_(p.cos_series_partial, vec![]);
    let hyp1 = d.lemma(p.cos_term_abs_le_dominant, &[]);

    let ordered_half = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, hab: ExprId| -> ExprId {
        d.lemma(
            p.sum_range_cauchy_dominated_ordered_normalized,
            &[cos_term_c, exp_dominant_const, k_dom, a, b, hyp1, hyp2, hab],
        )
    };

    let mut k_final = k_dom;
    for _ in 0..8 {
        k_final = d.succ(k_final);
    }

    let cos_series_partial_body =
        promote_ordered_half_to_full(d, p, cos_series_partial_c, k_final, &ordered_half);

    let raw = diagonal_seq(d, p, cos_series_partial_c);
    (raw, k_final, cos_series_partial_body)
}

/// `CReal.cosOne := CReal.mk (speedup (diagonal cosSeriesPartial) K) (…)` —
/// mirrors `exponential.rs::declare_e` exactly. `raw`/`k_final`/
/// `cos_series_partial_body` are the CALLER's (`declare_trig`'s own
/// `cos_one_ingredients` call) — see [`declare_trig`]'s doc for why these
/// must be the SAME `ExprId`s [`declare_cos_one_converges`] uses, not a
/// second, independently-derived copy.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k_final: ExprId,
    cos_series_partial_body: ExprId,
) -> Result<(), KernelError> {
    let cos_series_partial_c = d.kernel().const_(p.cos_series_partial, vec![]);

    let speedup_term = d.const_app(p.speedup, &[raw, k_final]);
    let regularity_proof = d.lemma(
        p.regular_of_scaled_cauchy,
        &[cos_series_partial_c, k_final, cos_series_partial_body],
    );

    let constructor = d.kernel().const_(p.mk, vec![]);
    let value = d.apply(constructor, &[speedup_term, regularity_proof]);
    let ty = creal_ty(d, p);

    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_one,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 40),
    })
}

// ----------------------------------------------------------------------------
// `CReal.cosOneConverges`, and the loose uniform bound `[-4, 4]` on `cosOne`.
// ----------------------------------------------------------------------------

/// `CReal.cosOneConverges : Converges cosSeriesPartial cosOne` — the
/// `e_converges` analogue, reproduced verbatim in SHAPE from
/// `exponential.rs::declare_e_converges` (that function is not `pub`, and
/// this module already reproduces private helpers from that file for the
/// same reason — see the module documentation).
///
/// **The concrete-`k_final` stack overflow this avoids.** Building the
/// per-`n` proof directly against the CONCRETE `k_final` would make
/// `speedup(raw, k_final)` a partially-concrete `Nat` expression (concrete in
/// `k_final`, symbolic in `n`); the kernel's lazy-delta `is_def_eq`, forced to
/// compare `speedup_term(n)` against `seq(l_val, n)` inside `exists_intro`'s
/// argument check, then unfolds both sides in lock-step and never
/// re-synchronizes, driving recursion depth into the thousands (measured for
/// `e`'s own analogous construction: 14.8 s → a 1 GiB stack overflow in
/// RELEASE). Building GENERICALLY over a BOUND `(k, h)` — exactly mirroring
/// [`super::convergence::declare_converges_of_cauchy`]'s own `minor` closure
/// — keeps every `Nat.mul`/`Nat.add` stuck against two free variables
/// simultaneously, so it never fires; substituting the concrete
/// `(k_final, cos_series_partial_body)` afterward is then a plain
/// Pi-application (codomain substitution), never re-entering the per-`n`
/// comparison.
///
/// `raw`/`k_final`/`cos_series_partial_body` are the CALLER's — see
/// [`declare_trig`]'s doc for why these must be the SAME `ExprId`s
/// [`declare_cos_one`] uses.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_one_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k_final: ExprId,
    cos_series_partial_body: ExprId,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let cos_series_partial_const = d.kernel().const_(p.cos_series_partial, vec![]);
    let cos_one_const = d.kernel().const_(p.cos_one, vec![]);

    let generic = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = sum_range_cauchy_body(d, p, cos_series_partial_const, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let kregular_proof = kregular_of_cauchy_proof(d, p, raw, k, hp);
        let speedup_term = d.const_app(p.speedup, &[raw, k]);
        let sc = d.const_app(p.speedup_close, &[raw, k, kregular_proof]);

        let regularity_proof = d.lemma(
            p.regular_of_scaled_cauchy,
            &[cos_series_partial_const, k, hp],
        );
        let constructor = d.kernel().const_(p.mk, vec![]);
        let l_val = d.apply(constructor, &[speedup_term, regularity_proof]);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let raw_n = d.apply(raw, &[n]);
        let speedup_n = d.apply(speedup_term, &[n]);
        let diff_n = rsub(d, rat, raw_n, speedup_n);

        let succ_k = d.succ(k);
        let one_nat = d.num(1);
        let bound_left_n = div_succ_at(d, p, succ_k, n);
        let bound_right_n = div_succ_at(d, p, one_nat, n);
        let sc_n_bound = radd(d, bound_left_n, bound_right_n);

        let sc_n = d.apply(sc, &[n]);

        let fuse = d.lemma(rat.nat_div_succ_add, &[succ_k, one_nat, n]);
        let k2 = NatOps::add(d, succ_k, one_nat);
        let target_bound_n = div_succ_at(d, p, k2, n);
        let step = rat_eq_rewrite(d, sc_n_bound, target_bound_n, fuse, sc_n, &|d, t| {
            within(d, p, diff_n, t)
        });

        let over_n = d.lam_fv(n_fv, nat, step);
        let converges_pred = converges_predicate(d, p, cos_series_partial_const, l_val);
        let converges_proof = exists_intro(d, p, nat, converges_pred, k2, over_n);

        let with_hp = d.lam_fv(hp_fv, hp_ty, converges_proof);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let value = d.apply(generic, &[k_final, cos_series_partial_body]);

    let ty = converges_applied(d, p, cos_series_partial_const, cos_one_const);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_one_converges,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.four := mul two two`, local to this file exactly as
/// `exponential.rs::declare_e_le_four` builds its own `four` inline (not a
/// named `CReal` constant).
fn four(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let t = two(d, p);
    cmul(d, p, t, t)
}

/// `le zero four`, reproduced in shape from `exponential.rs::declare_e_le_four`'s
/// own inline `four_nonneg`.
fn four_nonneg_proof(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let t = two(d, p);
    let two_nn = two_nonneg_proof(d, p);
    d.lemma(p.mul_nonneg, &[t, t, two_nn, two_nn])
}

/// `le (sumRange expDominant n) four`, for a BOUND `n` — reproduced verbatim
/// from the closed-form portion of `exponential.rs::declare_e_le_four`'s own
/// `per_n` closure (the part bounding `sumRange expDominant n` itself, not
/// the `sumRange expTerm n <= sumRange expDominant n` step, which this file
/// does not need: `cosTermAbsLeDominant` already bounds `abs (cosTerm k)`
/// directly against `expDominant k`).
///
/// `sumRange expDominant n ~ mul four (add one (neg (pow half n)))`
/// (`CReal.mul_sumRange`/`CReal.sumRange_pow_half_closed_form`/`mul_assoc`),
/// and `add one (neg (pow half n)) <= one` since `pow half n >= 0`
/// (`CReal.pow_nonneg`/`neg_le_neg`/`add_le_add`), so the whole product is
/// `<= mul four one ~ four`.
fn exp_dominant_sum_le_four(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);
    let two_creal = two(d, p);
    let half_val = half(d, p);
    let four_c = four(d, p);
    let four_nonneg = four_nonneg_proof(d, p);

    let pow_half_fn_ = pow_half_fn(d, p);
    let sum_pow_half_n = d.const_app(p.sum_range, &[pow_half_fn_, n]);
    let sum_expdom_n = d.const_app(p.sum_range, &[exp_dominant_const, n]);
    let mul_two_sum = cmul(d, p, two_creal, sum_pow_half_n);
    let mul_sum_eq = d.lemma(p.mul_sum_range, &[two_creal, pow_half_fn_, n]);
    let mul_sum_eq_symm = d.lemma(p.equiv_symm, &[mul_two_sum, sum_expdom_n, mul_sum_eq]);

    let n_pow = cpow(d, p, half_val, n);
    let neg_pow = cneg(d, p, n_pow);
    let y_n = cadd(d, p, one_cc, neg_pow);
    let mul_two_y = cmul(d, p, two_creal, y_n);
    let closed_form = d.const_app(p.sum_pow_half_closed_form, &[n]);
    let refl_two = d.lemma(p.equiv_refl, &[two_creal]);
    let mul_two_mul_two_y = cmul(d, p, two_creal, mul_two_y);
    let step_congr = d.lemma(
        p.mul_congr,
        &[
            two_creal,
            two_creal,
            sum_pow_half_n,
            mul_two_y,
            refl_two,
            closed_form,
        ],
    );
    // step_congr : Equiv mul_two_sum mul_two_mul_two_y

    let four_raw = cmul(d, p, four_c, y_n);
    let assoc = d.lemma(p.mul_assoc, &[two_creal, two_creal, y_n]);
    // assoc : Equiv four_raw mul_two_mul_two_y
    let assoc_symm = d.lemma(p.equiv_symm, &[four_raw, mul_two_mul_two_y, assoc]);

    let eq_sum_four = {
        let t1 = d.lemma(
            p.equiv_trans,
            &[
                sum_expdom_n,
                mul_two_sum,
                mul_two_mul_two_y,
                mul_sum_eq_symm,
                step_congr,
            ],
        );
        d.lemma(
            p.equiv_trans,
            &[sum_expdom_n, mul_two_mul_two_y, four_raw, t1, assoc_symm],
        )
    };
    // eq_sum_four : Equiv sum_expdom_n four_raw

    // y_n <= one, from 0 <= pow half n.
    let half_nonneg = half_nonneg_proof(d, p);
    let pow_nonneg_n = d.lemma(p.pow_nonneg, &[half_val, half_nonneg, n]);
    let neg_le_neg_step = d.lemma(p.neg_le_neg, &[zero_c, n_pow, pow_nonneg_n]);
    let neg_zero_c = cneg(d, p, zero_c);
    let nz_equiv = neg_zero_equiv_local(d, p);
    let refl_neg_pow = d.lemma(p.equiv_refl, &[neg_pow]);
    let neg_pow_le_zero = d.lemma(
        p.le_congr,
        &[
            neg_pow,
            neg_pow,
            neg_zero_c,
            zero_c,
            refl_neg_pow,
            nz_equiv,
            neg_le_neg_step,
        ],
    );
    let refl_one = d.lemma(p.le_refl, &[one_cc]);
    let grown_y = d.lemma(
        p.add_le_add,
        &[one_cc, one_cc, neg_pow, zero_c, refl_one, neg_pow_le_zero],
    );
    let padded_one = cadd(d, p, one_cc, zero_c);
    let add_zero_eq = d.lemma(p.add_zero, &[one_cc]);
    let refl_y = d.lemma(p.equiv_refl, &[y_n]);
    let y_le_one = d.lemma(
        p.le_congr,
        &[y_n, y_n, padded_one, one_cc, refl_y, add_zero_eq, grown_y],
    );

    // mul four y_n <= mul four one ~ four.
    let mul_le = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[four_c, y_n, one_cc, four_nonneg, y_le_one],
    );
    let mul_four_one = cmul(d, p, four_c, one_cc);
    let mul_one_eq = d.lemma(p.mul_one, &[four_c]);
    let refl_four_raw = d.lemma(p.equiv_refl, &[four_raw]);
    let four_raw_le_four = d.lemma(
        p.le_congr,
        &[
            four_raw,
            four_raw,
            mul_four_one,
            four_c,
            refl_four_raw,
            mul_one_eq,
            mul_le,
        ],
    );

    let eq_sum_four_symm = d.lemma(p.equiv_symm, &[sum_expdom_n, four_raw, eq_sum_four]);
    let refl_four = d.lemma(p.equiv_refl, &[four_c]);
    d.lemma(
        p.le_congr,
        &[
            four_raw,
            sum_expdom_n,
            four_c,
            four_c,
            eq_sum_four_symm,
            refl_four,
            four_raw_le_four,
        ],
    )
}

/// `le (abs (sumRange cosTerm n)) four` (defeq to `le (abs (cosSeriesPartial
/// n)) four`), for a BOUND `n`. `CReal.abs_sumRange_le` (the triangle
/// inequality `|Σf| <= Σ|f|`) composed with `CReal.sumRange_le` at the
/// pointwise `CReal.cosTermAbsLeDominant`, then [`exp_dominant_sum_le_four`].
///
/// The middle-term construction (`abs_cos_term_fn`, `ptwise`) mirrors
/// `series.rs::declare_sum_range_tail_le`'s own `absf_hf`/`pointwise_proof`
/// pattern for composing `abs_sumRange_le` with `sumRange_le` — the only
/// other site in this development chaining these two lemmas.
fn cos_series_partial_abs_le_four(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let cos_term_abs_le_dominant_const = d.kernel().const_(p.cos_term_abs_le_dominant, vec![]);

    let s = d.const_app(p.sum_range, &[cos_term_c, n]);
    let abs_s = cabs(d, p, s);

    // triangle inequality: abs (sumRange cosTerm n) <= sumRange |cosTerm| n.
    let abs_cos_term_fn = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(cos_term_c, &[i]);
        let body = cabs(d, p, ci);
        d.lam_fv(i_fv, nat, body)
    };
    let sum_abs_cos_term_n = d.const_app(p.sum_range, &[abs_cos_term_fn, n]);
    let tri = d.lemma(p.abs_sum_range_le, &[cos_term_c, n]);
    // tri : le abs_s sum_abs_cos_term_n

    // sumRange |cosTerm| n <= sumRange expDominant n, pointwise from
    // cosTermAbsLeDominant.
    let ptwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_fv = d.fresh_fvar();
        let lt_ty = d.lt(i, n);
        let body = d.apply(cos_term_abs_le_dominant_const, &[i]);
        let with_lt = d.lam_fv(lt_fv, lt_ty, body);
        d.lam_fv(i_fv, nat, with_lt)
    };
    let sum_expdom_n = d.const_app(p.sum_range, &[exp_dominant_const, n]);
    let step_b = d.lemma(
        p.sum_range_le,
        &[abs_cos_term_fn, exp_dominant_const, n, ptwise],
    );
    // step_b : le sum_abs_cos_term_n sum_expdom_n

    let t1 = d.lemma(
        p.le_trans,
        &[abs_s, sum_abs_cos_term_n, sum_expdom_n, tri, step_b],
    );
    // t1 : le abs_s sum_expdom_n

    let sum_expdom_le_four = exp_dominant_sum_le_four(d, p, n);
    let four_c = four(d, p);
    d.lemma(
        p.le_trans,
        &[abs_s, sum_expdom_n, four_c, t1, sum_expdom_le_four],
    )
}

/// `CReal.cosOne_le_four : le cosOne (mul two two)` — a LOOSE, UNIFORM bound
/// (no case split; holds at every `n` including `n = 0`, where
/// `cosSeriesPartial 0 = zero` and `sumRange expDominant 0 = zero` both by
/// `sumRange_zero`'s ι-reduction, so the per-`n` fact is trivially true
/// there too — UNLIKE `two_le_e`, which needs the eventual/shift form because
/// `expSeriesPartial 0 = 0 < 2` genuinely violates that bound). `le_abs_self`
/// plus [`cos_series_partial_abs_le_four`], closed against
/// [`declare_cos_one_converges`] by `CReal.converges_upper_bound`.
///
/// **Where the kink would be, and why this bound has none.** `e_le_three`'s
/// kink is mathematical: `expTerm 0 = expTerm 1 = 1`, not yet geometric, so
/// no single uniform formula is both true at every `n` and tight enough to
/// sum to `3`. This file's domination (`abs (cosTerm k) <= expDominant k`,
/// REUSED unchanged from `e`) is uniform in exactly that same sense, but
/// deliberately never tight — `expDominant` bounds `cosTerm`'s TRUE decay
/// (`1/(2k)!`) by as much as ~180x at `k = 3` (`expDominant 3 = 1/4` against
/// `abs (cosTerm 3) = 1/720`) precisely because it is `e`'s own bound, reused
/// rather than re-derived. That looseness is what makes a single uniform
/// formula suffice: the triangle inequality (`abs_sumRange_le`) discards the
/// alternation's cancellation entirely, so nothing here ever needs to notice
/// where the sign pattern is. The genuine kink — where an actual case split
/// analogous to `e_le_three`'s would appear — is one step further out: a
/// bound tight enough for `[0, 1]` or `[1/2, 3/5]` needs to PAIR consecutive
/// terms (`cosTerm (2i) + cosTerm (2i+1) >= 0`, from `abs (cosTerm (2i+1)) <=
/// abs (cosTerm (2i))`, i.e. genuine decrease of the term sequence, not just
/// a uniform envelope), which is real alternating-series machinery this
/// slice does not build. See the module documentation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_one_le_four(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let cos_series_partial_const = d.kernel().const_(p.cos_series_partial, vec![]);
    let cos_one_const = d.kernel().const_(p.cos_one, vec![]);
    let cos_one_converges_proof = d.kernel().const_(p.cos_one_converges, vec![]);
    let four_c = four(d, p);

    let ptwise_upper = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.apply(cos_series_partial_const, &[n]);
        let abs_sn = cabs(d, p, sn);
        let abs_bound = cos_series_partial_abs_le_four(d, p, n);
        let le_abs = d.lemma(p.le_abs_self, &[sn]);
        let body = d.lemma(p.le_trans, &[sn, abs_sn, four_c, le_abs, abs_bound]);
        d.lam_fv(n_fv, nat, body)
    };

    let value = d.const_app(
        p.converges_upper_bound,
        &[
            cos_series_partial_const,
            cos_one_const,
            four_c,
            ptwise_upper,
            cos_one_converges_proof,
        ],
    );
    let ty = cle(d, p, cos_one_const, four_c);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_one_le_four,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.neg_four_le_cosOne : le (neg (mul two two)) cosOne` — the lower
/// half, from the same [`cos_series_partial_abs_le_four`] fact read through
/// `neg_le_abs` instead of `le_abs_self`, then flipped from `le (neg
/// cosSeriesPartial n) four` to `le (neg four) (cosSeriesPartial n)` via
/// `neg_le_neg`/double-negation — the same flip [`sign_abs_le_one`]'s sibling
/// helpers (`neg_one_le_one`, `double_neg`) already use in this file.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_neg_four_le_cos_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let cos_series_partial_const = d.kernel().const_(p.cos_series_partial, vec![]);
    let cos_one_const = d.kernel().const_(p.cos_one, vec![]);
    let cos_one_converges_proof = d.kernel().const_(p.cos_one_converges, vec![]);
    let four_c = four(d, p);
    let neg_four = cneg(d, p, four_c);

    let ptwise_lower = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.apply(cos_series_partial_const, &[n]);
        let neg_sn = cneg(d, p, sn);
        let abs_sn = cabs(d, p, sn);
        let abs_bound = cos_series_partial_abs_le_four(d, p, n);
        let neg_le_abs_step = d.lemma(p.neg_le_abs, &[sn]);
        // neg_le_abs_step : le neg_sn abs_sn
        let neg_sn_le_four = d.lemma(
            p.le_trans,
            &[neg_sn, abs_sn, four_c, neg_le_abs_step, abs_bound],
        );
        // neg_sn_le_four : le neg_sn four_c

        let step = d.lemma(p.neg_le_neg, &[neg_sn, four_c, neg_sn_le_four]);
        // step : le neg_four (neg neg_sn)
        let neg_neg_sn = cneg(d, p, neg_sn);
        let dn = double_neg(d, p, sn);
        // dn : Equiv neg_neg_sn sn
        let refl_neg_four = erefl(d, p, neg_four);
        let body = d.lemma(
            p.le_congr,
            &[neg_four, neg_four, neg_neg_sn, sn, refl_neg_four, dn, step],
        );
        d.lam_fv(n_fv, nat, body)
    };

    let value = d.const_app(
        p.converges_lower_bound,
        &[
            neg_four,
            cos_series_partial_const,
            cos_one_const,
            ptwise_lower,
            cos_one_converges_proof,
        ],
    );
    let ty = cle(d, p, neg_four, cos_one_const);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.neg_four_le_cos_one,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// The alternating-series sharpening: `CReal.expTerm_antitone`, the bracket
// instantiated at `cosTerm`'s magnitude sequence, and the two concrete `m=0`
// corollaries this closes for free. See this task's own brief: the ONLY
// missing input for a real numeric bound on `cosOne` was a genuine
// antitone-reciprocal-of-factorial fact about `CReal.expTerm`, since
// `expTerm n := ofRat (1/n!)` is a raw normalized rational (never built via
// `CReal.inv`) -- so the whole route stays at `Rat`/`Nat` cross-multiplication,
// mirroring `rat_prelude/archimedean.rs::declare_nat_div_succ_antitone`'s
// numerator-1-both-sides shape exactly, with `factorial_le_succ` (below)
// standing in for `Nat.succ_le_succ`.
// ============================================================================

/// `Nat.le (factorial n) (factorial (succ n))` — `n! <= (n+1)!`. Pure
/// `Nat.mul_le_mul_left` at `c := factorial n`, scaling `Nat.le 1 (succ n)`
/// ([`one_le_succ`]) up to `Nat.le (factorial n * 1) (factorial n * succ n)`,
/// then rewriting each side back through `Nat.mul_one`/`Nat.factorial_succ`.
fn factorial_le_succ(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let np = d.prelude();
    let one_nat = d.num(1);
    let succ_n = d.succ(n);
    let fact_n = d.factorial(n);
    let fact_succ_n = d.factorial(succ_n);

    let pos = one_le_succ(d, n); // Le 1 (succ n)
    let step = d.lemma(np.mul_le_mul_left, &[fact_n, one_nat, succ_n, pos]);
    // step : Le (fact_n*1) (fact_n*succ_n)

    let fact_n_mul_1 = d.mul(fact_n, one_nat);
    let fact_n_mul_succ_n = d.mul(fact_n, succ_n);
    let mul_one_eq = d.lemma(np.mul_one, &[fact_n]); // Eq (fact_n*1) fact_n
    let motive1 = d.eq_motive(fact_n_mul_1, &|d, x| NatOps::le(d, x, fact_n_mul_succ_n));
    let step2 = d.transport(fact_n_mul_1, motive1, step, fact_n, mul_one_eq);
    // step2 : Le fact_n (fact_n*succ_n)

    let factorial_succ_eq = d.lemma(np.factorial_succ, &[n]); // Eq fact_succ_n (fact_n*succ_n)
    let factorial_succ_eq_rev = d.symm(fact_succ_n, fact_n_mul_succ_n, factorial_succ_eq);
    let motive2 = d.eq_motive(fact_n_mul_succ_n, &|d, x| NatOps::le(d, fact_n, x));
    d.transport(
        fact_n_mul_succ_n,
        motive2,
        step2,
        fact_succ_n,
        factorial_succ_eq_rev,
    )
    // : Le fact_n fact_succ_n
}

/// `Rat.le (normalize 1 (factorial (succ n)) posA) (normalize 1 (factorial n)
/// posB)` — `1/(n+1)! <= 1/n!`. Mirrors
/// `rat_prelude/archimedean.rs::declare_nat_div_succ_antitone`'s
/// cross-multiplication body verbatim in shape (same numerator-1-both-sides
/// case), substituting [`factorial_le_succ`] for `Nat.succ_le_succ` as the
/// denominator inequality. Returns `(q, r, proof)`; `q`/`r` are built via
/// the exact same `normalize`/`one_le_factorial` calls
/// `exponential.rs::inv_factorial` uses internally, so `embed q`/`embed r`
/// are defeq to `expTerm (succ n)`/`expTerm n` after one delta-unfold of
/// [`CRealPrelude::exp_term`].
#[allow(clippy::too_many_lines)]
fn exp_term_antitone_rat(
    d: &mut IntDev<'_>,
    rp: RatPrelude,
    n: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let nat = rp.int.nat;
    let one_nat = d.num(1);
    let one_z = d.of_nat(one_nat);

    let succ_n = d.succ(n);
    let ea = d.factorial(succ_n);
    let eb = d.factorial(n);
    let eaz = d.of_nat(ea);
    let ebz = d.of_nat(eb);
    let pos_a = d.lemma(nat.one_le_factorial, &[succ_n]);
    let pos_b = d.lemma(nat.one_le_factorial, &[n]);

    let rep_a = normalize(d, one_z, ea, pos_a);
    let rep_b = normalize(d, one_z, eb, pos_b);
    let na = num(d, rep_a);
    let da = den(d, rep_a);
    let daz = den_z(d, rep_a);
    let nb = num(d, rep_b);
    let db = den(d, rep_b);
    let dbz = den_z(d, rep_b);

    // Eq-A : na * eaz = daz.
    let cross_a = d.lemma(rp.normalize_cross, &[one_z, ea, pos_a]);
    let one_z_daz = d.imul(one_z, daz);
    let one_mul_da_nat = d.lemma(nat.one_mul, &[da]);
    let one_mul_da_product = NatOps::mul(d, one_nat, da);
    let one_mul_da = d.nat_eq_to_int(one_mul_da_product, da, one_mul_da_nat, &|d, t| d.of_nat(t));
    let na_eaz = d.imul(na, eaz);
    let (_, eqa) = d.ichain(na_eaz, &[(one_z_daz, cross_a), (daz, one_mul_da)]);

    // Eq-B : nb * ebz = dbz.
    let cross_b = d.lemma(rp.normalize_cross, &[one_z, eb, pos_b]);
    let one_z_dbz = d.imul(one_z, dbz);
    let one_mul_db_nat = d.lemma(nat.one_mul, &[db]);
    let one_mul_db_product = NatOps::mul(d, one_nat, db);
    let one_mul_db = d.nat_eq_to_int(one_mul_db_product, db, one_mul_db_nat, &|d, t| d.of_nat(t));
    let nb_ebz = d.imul(nb, ebz);
    let (_, eqb) = d.ichain(nb_ebz, &[(one_z_dbz, cross_b), (dbz, one_mul_db)]);

    // `Nat.le eb ea`, which IS `Int.le ebz eaz` (both `ofNat`s).
    let hyp_e = factorial_le_succ(d, n);

    // Scale by the (positive) product of the two denominators.
    let da_db = NatOps::mul(d, da, db);
    let scaled_hyp = d.lemma(rp.int_mul_le_mul_right, &[ebz, eaz, da_db, hyp_e]);

    let dadbz = d.imul(daz, dbz);
    let source_lhs = d.imul(ebz, dadbz);
    let source_rhs = d.imul(eaz, dadbz);

    let ea_eb = d.imul(eaz, ebz);
    let na_dbz = d.imul(na, dbz);
    let nb_daz = d.imul(nb, daz);
    let goal_lhs = d.imul(na_dbz, ea_eb);
    let goal_rhs = d.imul(nb_daz, ea_eb);

    // --- LHS: (na*dbz)*(eaz*ebz) = ebz*(daz*dbz) ---
    let goal_lhs_left_head = d.imul(na_dbz, eaz);
    let goal_lhs_left = d.imul(goal_lhs_left_head, ebz);
    let bridge_lhs_forward = d.lemma(rp.int.mul_assoc, &[na_dbz, eaz, ebz]);
    let bridge_lhs = d.isymm(goal_lhs_left, goal_lhs, bridge_lhs_forward);

    let regroup_lhs = iregroup4(d, [na, dbz, eaz, ebz], [na, eaz, dbz, ebz]);
    let regrouped_lhs_head = d.imul(na_eaz, dbz);
    let regrouped_lhs = d.imul(regrouped_lhs_head, ebz);

    let subst_lhs = d.icongr(na_eaz, daz, eqa, &|d, t| {
        let head = d.imul(t, dbz);
        d.imul(head, ebz)
    });
    let subst_lhs_result = d.imul(dadbz, ebz);

    let commute_lhs = d.lemma(rp.int.mul_comm, &[dadbz, ebz]);

    let (_, lhs_chain) = d.ichain(
        goal_lhs,
        &[
            (goal_lhs_left, bridge_lhs),
            (regrouped_lhs, regroup_lhs),
            (subst_lhs_result, subst_lhs),
            (source_lhs, commute_lhs),
        ],
    );

    // --- RHS: (nb*daz)*(eaz*ebz) = eaz*(daz*dbz) ---
    let goal_rhs_left_head = d.imul(nb_daz, eaz);
    let goal_rhs_left = d.imul(goal_rhs_left_head, ebz);
    let bridge_rhs_forward = d.lemma(rp.int.mul_assoc, &[nb_daz, eaz, ebz]);
    let bridge_rhs = d.isymm(goal_rhs_left, goal_rhs, bridge_rhs_forward);

    let regroup_rhs = iregroup4(d, [nb, daz, eaz, ebz], [nb, ebz, daz, eaz]);
    let regrouped_rhs_head = d.imul(nb_ebz, daz);
    let regrouped_rhs = d.imul(regrouped_rhs_head, eaz);

    let subst_rhs = d.icongr(nb_ebz, dbz, eqb, &|d, t| {
        let head = d.imul(t, daz);
        d.imul(head, eaz)
    });
    let dbz_daz = d.imul(dbz, daz);
    let subst_rhs_mid = d.imul(dbz_daz, eaz);

    let swap_db_da = d.lemma(rp.int.mul_comm, &[dbz, daz]);
    let commute_inner_rhs = d.icongr(dbz_daz, dadbz, swap_db_da, &|d, t| d.imul(t, eaz));
    let subst_rhs_final = d.imul(dadbz, eaz);

    let commute_rhs = d.lemma(rp.int.mul_comm, &[dadbz, eaz]);

    let (_, rhs_chain) = d.ichain(
        goal_rhs,
        &[
            (goal_rhs_left, bridge_rhs),
            (regrouped_rhs, regroup_rhs),
            (subst_rhs_mid, subst_rhs),
            (subst_rhs_final, commute_inner_rhs),
            (source_rhs, commute_rhs),
        ],
    );

    let back_lhs = d.isymm(goal_lhs, source_lhs, lhs_chain);
    let at_lhs = d.int_eq_rewrite(source_lhs, goal_lhs, back_lhs, scaled_hyp, &|d, z| {
        d.ile(z, source_rhs)
    });
    let back_rhs = d.isymm(goal_rhs, source_rhs, rhs_chain);
    let scaled_goal = d.int_eq_rewrite(source_rhs, goal_rhs, back_rhs, at_lhs, &|d, z| {
        d.ile(goal_lhs, z)
    });

    let ea_eb_nat = NatOps::mul(d, ea, eb);
    let one_le_ea_eb = d.lemma(nat.one_le_mul, &[ea, eb, pos_a, pos_b]);
    let proof = d.lemma(
        rp.int_le_of_mul_le_mul_right,
        &[na_dbz, nb_daz, ea_eb_nat, one_le_ea_eb, scaled_goal],
    );

    (rep_a, rep_b, proof)
}

/// `CReal.expTerm_antitone : ∀ n, le (expTerm (succ n)) (expTerm n)` —
/// `1/(n+1)! <= 1/n!`, the one missing input this task's brief names: the
/// `hdec` premise `CReal.alternatingLowerBound`/`upperBound` need at
/// `cosTerm`'s magnitude sequence. See [`exp_term_antitone_rat`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_exp_term_antitone(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat_ty = d.nat_ty();
    let rp = p.rat;

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let (q, r, rat_le) = exp_term_antitone_rat(d, rp, n);
    let creal_le = d.lemma(p.of_rat_le, &[q, r, rat_le]);

    let succ_n = d.succ(n);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let exp_term_succ_n = d.apply(exp_term_c, &[succ_n]);
    let exp_term_n = d.apply(exp_term_c, &[n]);

    let value = d.lam_fv(n_fv, nat_ty, creal_le);
    let ty = {
        let stmt = cle(d, p, exp_term_succ_n, exp_term_n);
        d.pi_fv(n_fv, nat_ty, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_term_antitone,
        uparams: vec![],
        ty,
        value,
    })
}

/// `cosTerm`'s magnitude sequence, `a j := expTerm (add j j)`.
fn cos_magnitude_lam(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let dbl = d.add(j, j);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let body = d.apply(exp_term_c, &[dbl]);
    d.lam_fv(j_fv, nat, body)
}

/// `hnn : ∀ k, le zero (expTerm (add k k))` — directly `CReal.exp_term_nonneg`
/// instantiated at the doubled index.
fn cos_magnitude_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let dbl = d.add(k, k);
    let body = d.lemma(p.exp_term_nonneg, &[dbl]);
    d.lam_fv(k_fv, nat, body)
}

/// `hdec : ∀ k, le (expTerm (add (succ k) (succ k))) (expTerm (add k k))` —
/// two applications of [`declare_exp_term_antitone`]'s
/// [`CRealPrelude::exp_term_antitone`], bridged across the index identity
/// `add (succ k) (succ k) = succ (succ (add k k))`: the OUTER `succ` is free
/// (`Nat.add`'s own ι-reduction on its right argument), the inner one needs
/// exactly one `Nat.succ_add` step (`add (succ k) k = succ (add k k)`, since
/// `Nat.add` cannot peel a `succ` off its LEFT argument by ι alone).
fn cos_magnitude_dec(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let np = p.rat.int.nat;
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let skk = d.succ(kk);
    let sskk = d.succ(skk);

    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_sskk = d.apply(exp_term_c, &[sskk]);
    let e_skk = d.apply(exp_term_c, &[skk]);
    let e_kk = d.apply(exp_term_c, &[kk]);

    let step1 = d.lemma(p.exp_term_antitone, &[skk]); // le e_sskk e_skk
    let step2 = d.lemma(p.exp_term_antitone, &[kk]); // le e_skk e_kk
    let composed = d.lemma(p.le_trans, &[e_sskk, e_skk, e_kk, step1, step2]);
    // composed : le e_sskk e_kk, i.e. le (expTerm sskk) (expTerm kk)

    // Bridge `add (succ k) (succ k)` to `sskk`. Only the inner `succ` needs a
    // proof: `add (succ k) k = succ (add k k)` (`Nat.succ_add`).
    let sk = d.succ(k);
    let sk_k = d.add(sk, k); // add (succ k) k
    let bridge = d.lemma(np.succ_add, &[k, k]); // Eq sk_k skk
    let bridge_succ = d.congr(sk_k, skk, bridge, &|d, x| d.succ(x));
    // bridge_succ : Eq (succ sk_k) sskk, and `succ sk_k` is ι-defeq to
    // `add (succ k) (succ k)`.
    let succ_sk_k = d.succ(sk_k);
    let bridge_rev = d.symm(succ_sk_k, sskk, bridge_succ); // Eq sskk (succ sk_k)

    let motive = d.eq_motive(sskk, &|d, x| {
        let ex = d.apply(exp_term_c, &[x]);
        cle(d, p, ex, e_kk)
    });
    let lhs_raw = d.add(sk, sk); // add (succ k) (succ k), ι-defeq to `succ sk_k`
    let result = d.transport(sskk, motive, composed, lhs_raw, bridge_rev);
    // result : le (expTerm lhs_raw) (expTerm kk), and `lhs_raw` beta-matches
    // `a (succ k)` while `kk` beta-matches `a k`.

    d.lam_fv(k_fv, nat, result)
}

/// `CReal.cosOne_alternating_lower : ∀ m, le (sumRange cosTerm (add m m))
/// cosOne` — [`CRealPrelude::alternating_lower_bound`] instantiated at
/// `cosTerm`'s magnitude sequence, closing the `hnn`/`hdec` premises with
/// [`cos_magnitude_nonneg`]/[`cos_magnitude_dec`] and the limit hypothesis
/// with `CReal.cosOneConverges`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_one_alternating_lower(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let a_fn = cos_magnitude_lam(d, p);
    let hnn = cos_magnitude_nonneg(d, p);
    let hdec = cos_magnitude_dec(d, p);
    let l = d.kernel().const_(p.cos_one, vec![]);
    let hconv = d.kernel().const_(p.cos_one_converges, vec![]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let body = d.const_app(p.alternating_lower_bound, &[a_fn, hnn, hdec, l, hconv, m]);
    let value = d.lam_fv(m_fv, nat, body);

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let ty = {
        let mm = d.add(m, m);
        let e_m = d.const_app(p.sum_range, &[cos_term_c, mm]);
        let stmt = cle(d, p, e_m, l);
        d.pi_fv(m_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_one_alternating_lower,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.cosOne_alternating_upper : ∀ m, le cosOne (sumRange cosTerm (succ
/// (add m m)))` — the mirror of [`declare_cos_one_alternating_lower`], off
/// [`CRealPrelude::alternating_upper_bound`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_one_alternating_upper(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let a_fn = cos_magnitude_lam(d, p);
    let hnn = cos_magnitude_nonneg(d, p);
    let hdec = cos_magnitude_dec(d, p);
    let l = d.kernel().const_(p.cos_one, vec![]);
    let hconv = d.kernel().const_(p.cos_one_converges, vec![]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let body = d.const_app(p.alternating_upper_bound, &[a_fn, hnn, hdec, l, hconv, m]);
    let value = d.lam_fv(m_fv, nat, body);

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let ty = {
        let mm = d.add(m, m);
        let smm = d.succ(mm);
        let o_m = d.const_app(p.sum_range, &[cos_term_c, smm]);
        let stmt = cle(d, p, l, o_m);
        d.pi_fv(m_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_one_alternating_upper,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.cosOne_nonneg : le zero cosOne` — [`declare_cos_one_alternating_lower`]
/// at `m := 0`: `sumRange cosTerm (add 0 0)` is ι-defeq to `zero` (both
/// `Nat.add`'s and `CReal.sumRange`'s own base cases), so the general bracket
/// specializes to the sign bound for free, no `Rat`/`CReal` arithmetic at all.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_one_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let zero_nat = d.zero();
    let cos_one_alt_lower_c = d.kernel().const_(p.cos_one_alternating_lower, vec![]);
    let value = d.apply(cos_one_alt_lower_c, &[zero_nat]);
    let zero_c = czero(d, p);
    let cos_one_c = d.kernel().const_(p.cos_one, vec![]);
    let ty = cle(d, p, zero_c, cos_one_c);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_one_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.cosOne_le_exp_term_zero : le cosOne (expTerm 0)` —
/// [`declare_cos_one_alternating_upper`] at `m := 0`:
/// `sumRange cosTerm (succ (add 0 0))` is ι-defeq to `add zero (cosTerm 0)`
/// (both `Nat.add`'s and `CReal.sumRange`'s own recursion steps), and
/// `cosTerm 0` is itself ι-defeq to `mul one (expTerm 0)`
/// (`CReal.pow_zero` closes `pow (neg one) 0` to `one` by `Eq.refl` alone —
/// see [`CRealPrelude::pow_zero`]'s own doc). What is NOT free: folding
/// `add zero (mul one (expTerm 0))` down to `expTerm 0` needs two genuine
/// `Equiv` steps (`add_comm` + `add_zero` for the outer `add`, `one_mul` for
/// the inner `mul`), composed and transported across the inequality with
/// `CReal.le_congr`. `expTerm 0` is mathematically `1` (`1/0! = 1`), but
/// reducing it further to the literal constant `CReal.one` would need
/// `Rat.normalize 1 (factorial 0) _ = Rat.one`, i.e. `Nat.gcd 1 1`
/// computing to `1` — flagged in this task's own brief as the single most
/// likely stall point, and not attempted here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_one_le_exp_term_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let zero_nat = d.zero();
    let cos_one_alt_upper_c = d.kernel().const_(p.cos_one_alternating_upper, vec![]);
    let raw = d.apply(cos_one_alt_upper_c, &[zero_nat]);
    // raw : le cosOne (sumRange cosTerm (succ (add 0 0))), ι-defeq to
    // le cosOne (add zero (cosTerm 0)).

    let cos_one_c = d.kernel().const_(p.cos_one, vec![]);
    let zero_c = czero(d, p);
    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_0 = d.apply(cos_term_c, &[zero_nat]);
    let add_zero_cos_term_0 = cadd(d, p, zero_c, cos_term_0);
    let cos_term_0_add_zero = cadd(d, p, cos_term_0, zero_c);

    let comm = d.lemma(p.add_comm, &[zero_c, cos_term_0]);
    // comm : Equiv add_zero_cos_term_0 cos_term_0_add_zero
    let az = d.lemma(p.add_zero, &[cos_term_0]);
    // az : Equiv cos_term_0_add_zero cos_term_0
    let step1 = echain(
        d,
        p,
        add_zero_cos_term_0,
        &[(cos_term_0_add_zero, comm), (cos_term_0, az)],
    );
    // step1 : Equiv add_zero_cos_term_0 cos_term_0

    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let exp_term_0 = d.apply(exp_term_c, &[zero_nat]);
    let one_cc = one_c(d, p);
    let one_mul_exp_term_0 = cmul(d, p, one_cc, exp_term_0);
    // `cos_term_0` is ι-defeq to `one_mul_exp_term_0` (`pow (neg one) 0`
    // closes to `one` by `Eq.refl`, `CReal.pow_zero`'s own reason). There is
    // no CReal-level `one_mul` (only `mul_one : Equiv (mul x one) x`, one of
    // the 22), so bridge with `mul_comm` first.
    let exp_term_0_mul_one = cmul(d, p, exp_term_0, one_cc);
    let mul_comm_step = d.lemma(p.mul_comm, &[one_cc, exp_term_0]);
    // mul_comm_step : Equiv one_mul_exp_term_0 exp_term_0_mul_one
    let mul_one_step = d.lemma(p.mul_one, &[exp_term_0]);
    // mul_one_step : Equiv exp_term_0_mul_one exp_term_0
    let one_mul_step = echain(
        d,
        p,
        one_mul_exp_term_0,
        &[
            (exp_term_0_mul_one, mul_comm_step),
            (exp_term_0, mul_one_step),
        ],
    );
    // one_mul_step : Equiv one_mul_exp_term_0 exp_term_0
    let step2 = echain(
        d,
        p,
        add_zero_cos_term_0,
        &[(cos_term_0, step1), (exp_term_0, one_mul_step)],
    );
    // step2 : Equiv add_zero_cos_term_0 exp_term_0

    let refl_cos_one = erefl(d, p, cos_one_c);
    let value = d.lemma(
        p.le_congr,
        &[
            cos_one_c,
            cos_one_c,
            add_zero_cos_term_0,
            exp_term_0,
            refl_cos_one,
            step2,
            raw,
        ],
    );
    let ty = cle(d, p, cos_one_c, exp_term_0);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_one_le_exp_term_zero,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// `CReal.sinOne` — `sin 1 := Σ_{k≥0} (-1)^k/(2k+1)!`, mirroring `cosOne`
// exactly except for the index: the odd `Nat.add (Nat.add k k) 1` in place
// of the doubled `Nat.add k k`. Written symbolic-left/literal-right (as
// `cosTerm`'s own doubled index is) so `Nat.add (Nat.add k k) 1` ι-reduces
// to `Nat.succ (Nat.add k k)` for FREE — no `Nat.succ_add`/`Nat.add_comm`
// bookkeeping needed to see the odd index as "one past the even index".
// ============================================================================

/// `le (expDominant (Nat.add (Nat.add k k) 1)) (expDominant k)` — the
/// [`exp_dominant_double_le`] analogue for the odd index. One extra
/// [`CRealPrelude::pow_le_pow_of_le_one`] step past that function: `pow
/// half` is antitone one step at a time for a base in `[0,1]`
/// ([`half_nonneg_proof`]/[`half_le_one_proof`]), so `expDominant (succ (add
/// k k)) ≤ expDominant (add k k)` directly — the odd index's own `Nat.add`
/// ι-reduction already exposes the `succ`, so `CReal.pow_add` is not needed
/// here — then [`exp_dominant_double_le`] finishes the descent from `add k
/// k` down to `k`.
fn exp_dominant_odd_le(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let h = half(d, p);
    let half_nonneg = half_nonneg_proof(d, p);
    let half_le_one = half_le_one_proof(d, p);
    let dbl_k = d.add(k, k);
    let succ_dbl_k = d.succ(dbl_k);

    let pow_step = d.lemma(
        p.pow_le_pow_of_le_one,
        &[h, half_nonneg, half_le_one, dbl_k],
    );
    // pow_step : le (pow h succ_dbl_k) (pow h dbl_k)

    let pow_succ_dbl_k = cpow(d, p, h, succ_dbl_k);
    let pow_dbl_k = cpow(d, p, h, dbl_k);
    let two_c = two(d, p);
    let two_nonneg = two_nonneg_proof(d, p);
    let scale = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[two_c, pow_succ_dbl_k, pow_dbl_k, two_nonneg, pow_step],
    );
    // scale : le (mul two_c pow_succ_dbl_k) (mul two_c pow_dbl_k)
    //       = le (expDominant succ_dbl_k) (expDominant dbl_k)

    let dom_succ_dbl_k = exp_dominant_at(d, p, succ_dbl_k);
    let dom_dbl_k = exp_dominant_at(d, p, dbl_k);
    let dom_k = exp_dominant_at(d, p, k);

    let step_b = exp_dominant_double_le(d, p, k);
    // step_b : le (expDominant dbl_k) (expDominant k)

    d.lemma(
        p.le_trans,
        &[dom_succ_dbl_k, dom_dbl_k, dom_k, scale, step_b],
    )
}

/// `CReal.sinTerm : Nat → CReal := fun k => mul (pow (neg one) k) (expTerm
/// (Nat.add (Nat.add k k) 1))`.
fn declare_sin_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_k = cpow(d, p, neg_one, k);
    let dbl_k = d.add(k, k);
    let one_nat = d.num(1);
    let odd_k = d.add(dbl_k, one_nat);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_term = d.apply(exp_term_c, &[odd_k]);
    let body = cmul(d, p, sign_k, e_term);

    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sin_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(TRIG_HEIGHT),
    })
}

/// `CReal.sinSeriesPartial : Nat → CReal := CReal.sumRange CReal.sinTerm`.
fn declare_sin_series_partial(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let value = d.const_app(p.sum_range, &[sin_term_c]);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sin_series_partial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(TRIG_HEIGHT),
    })
}

/// `CReal.sinTermAbsLeDominant : ∀ k, le (abs (sinTerm k)) (expDominant k)`
/// — the [`declare_cos_term_abs_le_dominant`] analogue, using the odd index
/// and [`exp_dominant_odd_le`] in place of the doubled index and
/// [`exp_dominant_double_le`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_term_abs_le_dominant(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_k = cpow(d, p, neg_one, k);
    let sign_abs = sign_abs_le_one(d, p, k);

    let dbl_k = d.add(k, k);
    let one_nat = d.num(1);
    let odd_k = d.add(dbl_k, one_nat);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_term = d.apply(exp_term_c, &[odd_k]);
    let dom_odd = exp_dominant_at(d, p, odd_k);
    let dom_k = exp_dominant_at(d, p, k);

    let e_dom_bound = d.lemma(p.exp_term_abs_le_dominant, &[odd_k]);
    // e_dom_bound : le (abs e_term) dom_odd

    let prod_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[sign_k, e_term, one_cc, dom_odd, sign_abs, e_dom_bound],
    );
    // prod_bound : le (abs (mul sign_k e_term)) (mul one_cc dom_odd)

    let mul_comm_1e = d.lemma(p.mul_comm, &[one_cc, dom_odd]);
    let mul_one_e = d.lemma(p.mul_one, &[dom_odd]);
    let mul_one_cc_dom = cmul(d, p, one_cc, dom_odd);
    let mul_dom_one = cmul(d, p, dom_odd, one_cc);
    let one_dom_equiv = echain(
        d,
        p,
        mul_one_cc_dom,
        &[(mul_dom_one, mul_comm_1e), (dom_odd, mul_one_e)],
    );

    let sin_term_k = cmul(d, p, sign_k, e_term);
    let abs_sin_term_k = cabs(d, p, sin_term_k);
    let refl_abs_sin = erefl(d, p, abs_sin_term_k);
    let abs_sin_le_dom_odd = d.lemma(
        p.le_congr,
        &[
            abs_sin_term_k,
            abs_sin_term_k,
            mul_one_cc_dom,
            dom_odd,
            refl_abs_sin,
            one_dom_equiv,
            prod_bound,
        ],
    );

    let dom_odd_le_dom_k = exp_dominant_odd_le(d, p, k);

    let final_bound = d.lemma(
        p.le_trans,
        &[
            abs_sin_term_k,
            dom_odd,
            dom_k,
            abs_sin_le_dom_odd,
            dom_odd_le_dom_k,
        ],
    );

    let value = d.lam_fv(k_fv, nat, final_bound);
    let ty = {
        let stmt = cle(d, p, abs_sin_term_k, dom_k);
        d.pi_fv(k_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_term_abs_le_dominant,
        uparams: vec![],
        ty,
        value,
    })
}

/// `(raw, k_final, sin_series_partial_body)` — the [`declare_sin_one`]
/// analogue of [`cos_one_ingredients`]. Calls
/// [`exp_dominant_cauchy_body_concrete`] AGAIN rather than threading
/// `cosOne`'s own `(k_dom, hyp2)` through: that function builds no
/// declarations of its own (only `ExprId` terms), so the only cost of
/// calling it twice is the kernel re-checking an equivalent proof term once
/// more when `sinOne`/`sinOneConverges` are declared — not a second
/// `CReal.e`-style constant.
fn sin_one_ingredients(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId, ExprId) {
    let (k_dom, hyp2) = exp_dominant_cauchy_body_concrete(d, p);

    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let sin_series_partial_c = d.kernel().const_(p.sin_series_partial, vec![]);
    let hyp1 = d.lemma(p.sin_term_abs_le_dominant, &[]);

    let ordered_half = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, hab: ExprId| -> ExprId {
        d.lemma(
            p.sum_range_cauchy_dominated_ordered_normalized,
            &[sin_term_c, exp_dominant_const, k_dom, a, b, hyp1, hyp2, hab],
        )
    };

    let mut k_final = k_dom;
    for _ in 0..8 {
        k_final = d.succ(k_final);
    }

    let sin_series_partial_body =
        promote_ordered_half_to_full(d, p, sin_series_partial_c, k_final, &ordered_half);

    let raw = diagonal_seq(d, p, sin_series_partial_c);
    (raw, k_final, sin_series_partial_body)
}

/// `CReal.sinOne := CReal.mk (speedup (diagonal sinSeriesPartial) K) (…)` —
/// mirrors [`declare_cos_one`] exactly. `raw`/`k_final`/
/// `sin_series_partial_body` are the CALLER's (`declare_sin_trig`'s own
/// [`sin_one_ingredients`] call) — see that function's doc for why these
/// must be the SAME `ExprId`s [`declare_sin_one_converges`] uses.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k_final: ExprId,
    sin_series_partial_body: ExprId,
) -> Result<(), KernelError> {
    let sin_series_partial_c = d.kernel().const_(p.sin_series_partial, vec![]);

    let speedup_term = d.const_app(p.speedup, &[raw, k_final]);
    let regularity_proof = d.lemma(
        p.regular_of_scaled_cauchy,
        &[sin_series_partial_c, k_final, sin_series_partial_body],
    );

    let constructor = d.kernel().const_(p.mk, vec![]);
    let value = d.apply(constructor, &[speedup_term, regularity_proof]);
    let ty = creal_ty(d, p);

    d.kernel().add_declaration(Declaration::Definition {
        name: p.sin_one,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 40),
    })
}

/// `CReal.sinOneConverges : Converges sinSeriesPartial sinOne` — mirrors
/// [`declare_cos_one_converges`] exactly, including building GENERICALLY
/// over a bound `(k, h)` rather than the concrete `k_final` for the same
/// stack-overflow reason documented there.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_one_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k_final: ExprId,
    sin_series_partial_body: ExprId,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let sin_series_partial_const = d.kernel().const_(p.sin_series_partial, vec![]);
    let sin_one_const = d.kernel().const_(p.sin_one, vec![]);

    let generic = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = sum_range_cauchy_body(d, p, sin_series_partial_const, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let kregular_proof = kregular_of_cauchy_proof(d, p, raw, k, hp);
        let speedup_term = d.const_app(p.speedup, &[raw, k]);
        let sc = d.const_app(p.speedup_close, &[raw, k, kregular_proof]);

        let regularity_proof = d.lemma(
            p.regular_of_scaled_cauchy,
            &[sin_series_partial_const, k, hp],
        );
        let constructor = d.kernel().const_(p.mk, vec![]);
        let l_val = d.apply(constructor, &[speedup_term, regularity_proof]);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let raw_n = d.apply(raw, &[n]);
        let speedup_n = d.apply(speedup_term, &[n]);
        let diff_n = rsub(d, rat, raw_n, speedup_n);

        let succ_k = d.succ(k);
        let one_nat = d.num(1);
        let bound_left_n = div_succ_at(d, p, succ_k, n);
        let bound_right_n = div_succ_at(d, p, one_nat, n);
        let sc_n_bound = radd(d, bound_left_n, bound_right_n);

        let sc_n = d.apply(sc, &[n]);

        let fuse = d.lemma(rat.nat_div_succ_add, &[succ_k, one_nat, n]);
        let k2 = NatOps::add(d, succ_k, one_nat);
        let target_bound_n = div_succ_at(d, p, k2, n);
        let step = rat_eq_rewrite(d, sc_n_bound, target_bound_n, fuse, sc_n, &|d, t| {
            within(d, p, diff_n, t)
        });

        let over_n = d.lam_fv(n_fv, nat, step);
        let converges_pred = converges_predicate(d, p, sin_series_partial_const, l_val);
        let converges_proof = exists_intro(d, p, nat, converges_pred, k2, over_n);

        let with_hp = d.lam_fv(hp_fv, hp_ty, converges_proof);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let value = d.apply(generic, &[k_final, sin_series_partial_body]);

    let ty = converges_applied(d, p, sin_series_partial_const, sin_one_const);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_one_converges,
        uparams: vec![],
        ty,
        value,
    })
}

// ----------------------------------------------------------------------------
// The alternating-series sharpening of `sinOne`, mirroring
// `cos_magnitude_lam`/`cos_magnitude_nonneg`/`cos_magnitude_dec` and the
// bracket instantiation exactly, except the magnitude sequence is `sinTerm`'s
// own `b j := expTerm (add (add j j) 1)` (odd index) rather than `cosTerm`'s
// `a j := expTerm (add j j)` (doubled index).
// ----------------------------------------------------------------------------

/// `sinTerm`'s magnitude sequence, `b j := expTerm (add (add j j) 1)`.
fn sin_magnitude_lam(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let dbl = d.add(j, j);
    let one_nat = d.num(1);
    let odd = d.add(dbl, one_nat);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let body = d.apply(exp_term_c, &[odd]);
    d.lam_fv(j_fv, nat, body)
}

/// `hnn : ∀ k, le zero (expTerm (add (add k k) 1))` — directly
/// `CReal.exp_term_nonneg` instantiated at the odd index.
fn sin_magnitude_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let dbl = d.add(k, k);
    let one_nat = d.num(1);
    let odd = d.add(dbl, one_nat);
    let body = d.lemma(p.exp_term_nonneg, &[odd]);
    d.lam_fv(k_fv, nat, body)
}

/// `hdec : ∀ k, le (expTerm (add (add (succ k) (succ k)) 1)) (expTerm (add
/// (add k k) 1))` — the [`cos_magnitude_dec`] analogue for the odd index.
/// One extra `Nat.succ` layer past that function (the odd index is one
/// `succ` further out than the doubled index), closed by the SAME single
/// `Nat.succ_add` bridge, composed with two `CReal.expTerm_antitone`
/// applications rather than [`cos_magnitude_dec`]'s two — the odd index also
/// increases by exactly 2 from `k` to `succ k`, since `2(k+1)+1 = (2k+1) +
/// 2`.
fn sin_magnitude_dec(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let np = p.rat.int.nat;
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let skk = d.succ(kk);
    let sskk = d.succ(skk);
    let ssskk = d.succ(sskk);

    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_ssskk = d.apply(exp_term_c, &[ssskk]);
    let e_sskk = d.apply(exp_term_c, &[sskk]);
    let e_skk = d.apply(exp_term_c, &[skk]);

    let step1 = d.lemma(p.exp_term_antitone, &[sskk]); // le e_ssskk e_sskk
    let step2 = d.lemma(p.exp_term_antitone, &[skk]); // le e_sskk e_skk
    let composed = d.lemma(p.le_trans, &[e_ssskk, e_sskk, e_skk, step1, step2]);
    // composed : le e_ssskk e_skk, i.e. le (expTerm ssskk) (expTerm skk)

    // Bridge `add (succ k) (succ k)` (dbl(succ k)) to `sskk`, exactly as
    // `cos_magnitude_dec` does, then wrap ONE more `succ` on each side to
    // reach the odd index.
    let sk = d.succ(k);
    let sk_k = d.add(sk, k); // add (succ k) k
    let bridge = d.lemma(np.succ_add, &[k, k]); // Eq sk_k skk
    let bridge_succ = d.congr(sk_k, skk, bridge, &|d, x| d.succ(x));
    // bridge_succ : Eq (succ sk_k) sskk
    let succ_sk_k = d.succ(sk_k);
    let bridge_succ2 = d.congr(succ_sk_k, sskk, bridge_succ, &|d, x| d.succ(x));
    // bridge_succ2 : Eq (succ succ_sk_k) ssskk
    let succ_succ_sk_k = d.succ(succ_sk_k);
    let bridge_rev = d.symm(succ_succ_sk_k, ssskk, bridge_succ2);
    // bridge_rev : Eq ssskk succ_succ_sk_k

    let motive = d.eq_motive(ssskk, &|d, x| {
        let ex = d.apply(exp_term_c, &[x]);
        cle(d, p, ex, e_skk)
    });
    let sk_sk = d.add(sk, sk); // add (succ k) (succ k), ι-defeq to succ_sk_k
    let one_nat = d.num(1);
    let lhs_raw = d.add(sk_sk, one_nat); // = odd(succ k), ι-defeq to succ_succ_sk_k
    let result = d.transport(ssskk, motive, composed, lhs_raw, bridge_rev);
    // result : le (expTerm lhs_raw) e_skk, and `lhs_raw` beta-matches
    // `b (succ k)` while `skk` beta-matches `b k` (ι-defeq to `add kk 1`).

    d.lam_fv(k_fv, nat, result)
}

/// `CReal.sinOne_alternating_lower : ∀ m, le (sumRange sinTerm (add m m))
/// sinOne` — mirrors [`declare_cos_one_alternating_lower`] exactly, at
/// `sinTerm`'s own magnitude sequence.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_one_alternating_lower(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let a_fn = sin_magnitude_lam(d, p);
    let hnn = sin_magnitude_nonneg(d, p);
    let hdec = sin_magnitude_dec(d, p);
    let l = d.kernel().const_(p.sin_one, vec![]);
    let hconv = d.kernel().const_(p.sin_one_converges, vec![]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let body = d.const_app(p.alternating_lower_bound, &[a_fn, hnn, hdec, l, hconv, m]);
    let value = d.lam_fv(m_fv, nat, body);

    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let ty = {
        let mm = d.add(m, m);
        let e_m = d.const_app(p.sum_range, &[sin_term_c, mm]);
        let stmt = cle(d, p, e_m, l);
        d.pi_fv(m_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_one_alternating_lower,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sinOne_alternating_upper : ∀ m, le sinOne (sumRange sinTerm (succ
/// (add m m)))` — mirrors [`declare_cos_one_alternating_upper`] exactly.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_one_alternating_upper(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let a_fn = sin_magnitude_lam(d, p);
    let hnn = sin_magnitude_nonneg(d, p);
    let hdec = sin_magnitude_dec(d, p);
    let l = d.kernel().const_(p.sin_one, vec![]);
    let hconv = d.kernel().const_(p.sin_one_converges, vec![]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let body = d.const_app(p.alternating_upper_bound, &[a_fn, hnn, hdec, l, hconv, m]);
    let value = d.lam_fv(m_fv, nat, body);

    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let ty = {
        let mm = d.add(m, m);
        let smm = d.succ(mm);
        let o_m = d.const_app(p.sum_range, &[sin_term_c, smm]);
        let stmt = cle(d, p, l, o_m);
        d.pi_fv(m_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_one_alternating_upper,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sinOne_nonneg : le zero sinOne` —
/// [`declare_sin_one_alternating_lower`] at `m := 0`, mirroring
/// [`declare_cos_one_nonneg`] exactly.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_one_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let zero_nat = d.zero();
    let sin_one_alt_lower_c = d.kernel().const_(p.sin_one_alternating_lower, vec![]);
    let value = d.apply(sin_one_alt_lower_c, &[zero_nat]);
    let zero_c = czero(d, p);
    let sin_one_c = d.kernel().const_(p.sin_one, vec![]);
    let ty = cle(d, p, zero_c, sin_one_c);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_one_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sinOne_le_exp_term_one : le sinOne (expTerm 1)` —
/// [`declare_sin_one_alternating_upper`] at `m := 0`, mirroring
/// [`declare_cos_one_le_exp_term_zero`] exactly except that `sinTerm 0`
/// reduces (by ι alone: `pow (neg one) 0 = one`, and `add (add 0 0) 1 = 1`)
/// to `mul one (expTerm 1)` — odd index `1`, not `0`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_one_le_exp_term_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let zero_nat = d.zero();
    let sin_one_alt_upper_c = d.kernel().const_(p.sin_one_alternating_upper, vec![]);
    let raw = d.apply(sin_one_alt_upper_c, &[zero_nat]);
    // raw : le sinOne (sumRange sinTerm (succ (add 0 0))), ι-defeq to
    // le sinOne (add zero (sinTerm 0)).

    let sin_one_c = d.kernel().const_(p.sin_one, vec![]);
    let zero_c = czero(d, p);
    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let sin_term_0 = d.apply(sin_term_c, &[zero_nat]);
    let add_zero_sin_term_0 = cadd(d, p, zero_c, sin_term_0);
    let sin_term_0_add_zero = cadd(d, p, sin_term_0, zero_c);

    let comm = d.lemma(p.add_comm, &[zero_c, sin_term_0]);
    // comm : Equiv add_zero_sin_term_0 sin_term_0_add_zero
    let az = d.lemma(p.add_zero, &[sin_term_0]);
    // az : Equiv sin_term_0_add_zero sin_term_0
    let step1 = echain(
        d,
        p,
        add_zero_sin_term_0,
        &[(sin_term_0_add_zero, comm), (sin_term_0, az)],
    );
    // step1 : Equiv add_zero_sin_term_0 sin_term_0

    let one_nat = d.num(1);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let exp_term_1 = d.apply(exp_term_c, &[one_nat]);
    let one_cc = one_c(d, p);
    let one_mul_exp_term_1 = cmul(d, p, one_cc, exp_term_1);
    // `sin_term_0` is ι-defeq to `one_mul_exp_term_1` (`pow (neg one) 0`
    // closes to `one` by `Eq.refl`, and `add (add 0 0) 1` closes to `1` by
    // `Eq.refl` too). No `one_mul` in `CRealPrelude` (only `mul_one`), so
    // bridge with `mul_comm` first, exactly as
    // `declare_cos_one_le_exp_term_zero` does.
    let exp_term_1_mul_one = cmul(d, p, exp_term_1, one_cc);
    let mul_comm_step = d.lemma(p.mul_comm, &[one_cc, exp_term_1]);
    // mul_comm_step : Equiv one_mul_exp_term_1 exp_term_1_mul_one
    let mul_one_step = d.lemma(p.mul_one, &[exp_term_1]);
    // mul_one_step : Equiv exp_term_1_mul_one exp_term_1
    let one_mul_step = echain(
        d,
        p,
        one_mul_exp_term_1,
        &[
            (exp_term_1_mul_one, mul_comm_step),
            (exp_term_1, mul_one_step),
        ],
    );
    // one_mul_step : Equiv one_mul_exp_term_1 exp_term_1
    let step2 = echain(
        d,
        p,
        add_zero_sin_term_0,
        &[(sin_term_0, step1), (exp_term_1, one_mul_step)],
    );
    // step2 : Equiv add_zero_sin_term_0 exp_term_1

    let refl_sin_one = erefl(d, p, sin_one_c);
    let value = d.lemma(
        p.le_congr,
        &[
            sin_one_c,
            sin_one_c,
            add_zero_sin_term_0,
            exp_term_1,
            refl_sin_one,
            step2,
            raw,
        ],
    );
    let ty = cle(d, p, sin_one_c, exp_term_1);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_one_le_exp_term_one,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// The `Rat.normalize`-on-literals obstacle
// [`declare_cos_one_le_exp_term_zero`]'s own doc names, solved WITHOUT
// touching `Nat.gcd` at all: `Rat.self_normalize` gives `Eq Rat (normalize
// (num q) (den q) (den_pos q)) q` for ANY `q`, including `q := Rat.one`,
// where `num`/`den` of a `Rat.mk`-built value reduce by ι for free and the
// remaining positivity argument is a `Prop` (definitional PROOF
// IRRELEVANCE identifies it with any other proof of `1 ≤ 1`, `Nat.gcd`
// never enters). Lifted through `CReal.ofRat`'s ordinary function
// congruence (`Eq`, not `Equiv` — `embed` is a plain function).
// ============================================================================

/// `Eq.{1} CReal a b`, reproduced verbatim in shape from `series.rs`'s own
/// private `creal_eq`.
fn creal_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let eq = d.kernel().const_(logic.eq, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} CReal a`.
fn creal_eq_refl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let refl = d.kernel().const_(logic.eq_refl, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(refl, &[carrier, a])
}

/// From `h : Eq Rat a b`, derive `Eq CReal (f a) (f b)` — the `ℚ → CReal`
/// congruence [`exp_term_lit_eq_one`] needs to lift a `Rat`-level equation
/// through `embed`.
fn req_congr_creal(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, CRealPrelude, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, p, a);
    let motive = req_motive(d, a, &|d, x| {
        let fx = f(d, p, x);
        creal_eq(d, p, fa, fx)
    });
    let refl_case = creal_eq_refl(d, p, fa);
    rtransport(d, a, motive, refl_case, b, h)
}

/// `Eq CReal (embed (normalize (ofNat 1) (factorial n) _)) CReal.one` for a
/// Nat LITERAL `n` whose `factorial n` reduces to `1` by ι alone — `n := 0`
/// (the base case) and `n := 1` (`mul 1 (factorial 0)`, `Nat.mul`'s own
/// ι-reduction on a literal right argument) both qualify; a SYMBOLIC `n`
/// does not, since `factorial n` is stuck.
///
/// Route: `Rat.self_normalize` at `q := Rat.one` is a proof of `Eq Rat
/// (normalize (num Rat.one) (den Rat.one) (den_pos Rat.one)) Rat.one`.
/// `num Rat.one`/`den Rat.one` reduce by ι (built via `Rat.mk` directly, not
/// `normalize`) to `ofNat 1`/`1`, and `den_pos Rat.one` — a `Prop` — is
/// definitionally interchangeable with `Nat.one_le_factorial n` by proof
/// irrelevance. So this SAME proof term, stated at the type `Eq Rat
/// (normalize (ofNat 1) (factorial n) (one_le_factorial n)) Rat.one`,
/// type-checks by defeq alone — no `Nat.gcd` reduction anywhere. `rcongr`
/// with `f := embed` lifts it to `CReal`.
fn exp_term_lit_eq_one(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let rat = p.rat;
    let np = d.prelude();

    let rat_one_c = d.kernel().const_(rat.one, vec![]);
    let self_norm = d.lemma(rat.self_normalize, &[rat_one_c]);
    // self_norm : Eq Rat (normalize (num rat_one_c) (den rat_one_c)
    //                       (den_pos rat_one_c)) rat_one_c
    // -- defeq (ι + proof irrelevance) to
    //    Eq Rat (normalize one_int (factorial n) posn) rat_one_c.

    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);
    let posn = d.lemma(np.one_le_factorial, &[n]);
    let factorial_n = d.factorial(n);
    let normalized_at_n = normalize(d, one_int, factorial_n, posn);

    let embed_fn = |d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId| -> ExprId { embed(d, p, x) };
    req_congr_creal(d, p, normalized_at_n, rat_one_c, self_norm, &embed_fn)
    // : Eq CReal (embed normalized_at_n) (embed rat_one_c)
    //   -- defeq to Eq CReal (expTerm n) CReal.one, since `expTerm n :=
    //   embed (normalize (ofNat 1) (factorial n) (one_le_factorial n))`
    //   and `CReal.one := embed Rat.one`.
}

/// `CReal.expTerm_zero_eq_one : Eq CReal (expTerm 0) CReal.one`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_exp_term_zero_eq_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let zero_nat = d.zero();
    let value = exp_term_lit_eq_one(d, p, zero_nat);

    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let exp_term_0 = d.apply(exp_term_c, &[zero_nat]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let ty = creal_eq(d, p, exp_term_0, one_c);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_term_zero_eq_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.expTerm_one_eq_one : Eq CReal (expTerm 1) CReal.one` — the
/// [`declare_exp_term_zero_eq_one`] analogue at `n := 1`, reused for
/// `sinOne_le_exp_term_one`'s own `expTerm 1`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_exp_term_one_eq_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let one_nat = d.num(1);
    let value = exp_term_lit_eq_one(d, p, one_nat);

    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let exp_term_1 = d.apply(exp_term_c, &[one_nat]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let ty = creal_eq(d, p, exp_term_1, one_c);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_term_one_eq_one,
        uparams: vec![],
        ty,
        value,
    })
}
