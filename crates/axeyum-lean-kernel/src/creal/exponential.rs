//! **`CReal.expTerm`/`CReal.expSeriesPartial`**: the rational term `1/n!`
//! embedded into `CReal`, and its `sumRange` partial sums — the raw material
//! for Euler's number `e := lim_k Σ_{n<k} 1/n!`.
//!
//! ## What this file builds, and what it does not (yet)
//!
//! [`declare_exp_term`] builds `CReal.expTerm n := ofRat (1/n!)`, using
//! `Nat.factorial` (`nat_prelude/defs.rs`, consumed here through `IntDev`'s
//! `NatOps` impl — no new `Nat`-level declaration needed) and
//! `Rat.normalize` (`int_prelude/rat.rs`) fed `Nat.one_le_factorial : ∀ n, 1
//! ≤ n!` (`nat_prelude/primes.rs`) as the denominator's positivity witness.
//! `Rat.normalize`'s own reducedness bookkeeping (`gcd`) is entirely internal
//! — this file never touches it.
//!
//! [`declare_exp_series_partial`] is the thin wrapper `CReal.expSeriesPartial
//! := CReal.sumRange CReal.expTerm`, so `expSeriesPartial k` unfolds by two
//! rounds of `Nat.rec` ι-reduction (`sumRange`'s own recursion, then
//! `CReal.add`'s constant-sequence arithmetic once every summand is `ofRat`
//! of a literal) to a concrete `CReal`, checked directly against `ofRat` of
//! the expected rational in `creal_tests.rs`.
//!
//! **UPDATE, this lane: the domination bound is now built** —
//! [`declare_exp_term_le_geom`] proves `CReal.expTerm_le_geom : ∀ n, le
//! (expTerm n) (ofRat (Rat.normalize 2 (2ⁿ) _))`, i.e. `1/n! ≤ 2·(1/2)ⁿ` for
//! every `n`, unconditional (no case split: both sides are `2` at `n = 0`,
//! both `1` at `n = 1`, and the ratio only widens from there). It takes
//! **route (b)** below — `g` stays a raw `Rat.normalize`d rational, never
//! touching `CReal.pow`/`CReal.inv` — via a pure cross-multiplication
//! argument against the `Nat` fact `2ⁿ ≤ 2·n!`
//! ([`two_pow_le_two_mul_factorial`]), mirroring
//! `rat_prelude/archimedean.rs::declare_nat_div_succ_antitone`'s own
//! cross-multiplication technique. **What was actually missing was not a new
//! order lemma or a `Rat`-level geometric-sum identity** (both guesses
//! below, from before this bound existed, turned out to be unnecessary) —
//! it was this comparison itself, which nothing in the prelude had built for
//! two *differently*-shaped `Rat.normalize`s before.
//!
//! **UPDATE, the next lane: `CReal.sumRange_pow_half_closed_form` is now
//! built** — `∀n, Equiv (sumRange (fun i => pow half i) n) (mul two (add one
//! (neg (pow half n))))`, i.e. `Σ_{k<n} (1/2)ᵏ = 2·(1 − (1/2)ⁿ)`, entirely
//! `inv`-free (no `pos_bound`, no `geom_pair_within`). The only defect
//! blocking it for two prior lanes was ONE swapped `equiv_symm` direction
//! feeding the final `echain`'s last link with `Equiv mul_two_y
//! mul_two_a_sum` where the straight-through `equiv_trans` step needed
//! `Equiv mul_two_a_sum mul_two_y` (already available, unreversed, as
//! `step4`) — none of the `Rat.normalize`/rescaling terrain this module's
//! other notes warn about was the cause.
//!
//! **This closed form does NOT by itself give `Cauchy (sumRange expDominant)`
//! (nor `sumRange (pow half ·)`), and closing that gap is more than index
//! bookkeeping.** `CReal.Equiv` is a same-index rational bound
//! (`Within (seq x n - seq y n) (modulus n n)`), while `CReal.mul`'s own
//! representative resamples its FACTORS at a shifted index depending on both
//! factors' magnitude (`product.rs`: `(x·y)_n := x_{(c+1)n+c} · y_{(c+1)n+c}`)
//! — so `seq (sumRange expDominant m) m` is not literally `2·(1 −
//! (1/2)ᵐ)` as a rational, only `Equiv`-related to it. Turning the closed
//! form into an actual `Cauchy` witness needs the same index/modulus
//! bookkeeping `series.rs`'s six-stage dominated-Cauchy pipeline already does
//! for a sequence dominated by an ALREADY-Cauchy `g` — which is exactly the
//! circularity `geometric.rs`'s own module documentation names for the raw
//! `pow half` sequence itself.
//!
//! **A genuinely new fact changed that module's own diagnosis, and this
//! file now closes `CReal.geom_cauchy` on it.** `geometric.rs` named "no
//! lemma bounding `CReal.pow` above by a `natDivSucc` rational" as one of
//! three pieces missing to close `CReal.geom_cauchy` via `geom_pair_within`
//! (`geom_tail_within_le` + `geom_pair_within` are landed there; the
//! harmonic bound on the deferred `seq Yₘ b` leaf was the blocker). That
//! bound **already existed** — `CRealPrelude::pow_half_le_nat_div_succ :
//! ∀n, le (pow half n) (ofRat (natDivSucc 1 n))`, built in `geometric.rs`
//! itself for the IVT bisection modulus (`ivt.rs`) — for the concrete base
//! `1/2` this file needs, and the other two pieces the old diagnosis named
//! (a `pow`-at-two-bases comparison, a Bernoulli inequality) were never
//! needed at all: the base-`1/2` route only ever needed the one harmonic
//! bound.
//!
//! Three declarations close it, all below:
//!
//! - [`declare_geom_half_inv_leaf_bound`] (`CReal.geomHalfInvLeafBound`)
//!   bounds the undischarged leaf `seq Yₘ b` in its full `CReal` form (`Yₘ ≤
//!   2/(m+1)`, not yet sampled). This is the one place `CReal.inv`/`PosBound`
//!   is used: `PosBound half 1` is `le_refl` at `half` itself (`half`'s own
//!   sample is the constant `1/2`), transported to `PosBound (add one (neg
//!   half)) 1` across `Equiv (add one (neg half)) half`
//!   (`one_sub_half_equiv_half`, already built below); the `inv`-value
//!   itself is pinned to the rational constant `2` by cancelling `half` from
//!   both `Equiv (mul half (inv …)) one` (`mul_inv_cancel`) and `Equiv (mul
//!   half (ofRat 2)) one` (a `Rat`-level computation, never
//!   `Rat.normalize`'s `Nat.gcd`) via `le_of_mul_le_mul_left` run in both
//!   directions plus `equiv_of_le_le` — never `inv_congr`. Multiplying
//!   `pow_half_le_nat_div_succ` through by that constant `2` closes it.
//!   Nothing downstream of this declaration touches `CReal.inv`/`PosBound`
//!   again.
//! - [`declare_geom_cauchy_ordered_half`] (`CReal.geomCauchyOrderedHalf`)
//!   applies the leaf bound at index `b`, widens `geom_pair_within`'s two
//!   `shift b` legs down to `b` (`Rat.natDivSucc_le_scaled`), and
//!   reassociates + fuses the resulting seven-`natDivSucc` bound (fifteen
//!   `Rat.add_assoc`/`Rat.add_comm`/`Rat.natDivSucc_add` steps, via
//!   `series.rs`'s own `assoc_rev_eq`/`fuse_same_index`, made `pub(super)`
//!   for this) down to `natDivSucc 7 b + natDivSucc 7 a` — `7` on the `b`
//!   side exactly, `3` padded up to `7` on the `a` side by one
//!   `Rat.natDivSucc_le_add_left`.
//! - [`declare_geom_cauchy`] (`CReal.geomCauchy`, i.e. **`CReal.geom_cauchy`
//!   itself**) runs the `Nat.le_total` split on top of that ordered bound,
//!   verbatim in technique to
//!   `series.rs::declare_sum_range_cauchy_of_dominated`'s own case split
//!   (`within_symm` plus one `Rat.add_comm` rewrite in the `m ≤ n` branch,
//!   none needed in the `n ≤ m` branch), with the fixed witness `K := 7` in
//!   place of that theorem's `k + 8`, and needing no `Cauchy (sumRange g)`
//!   hypothesis to eliminate (there is no `g` here) — `Cauchy (sumRange (fun
//!   n => pow half n))`.
//!
//! **Scaling this up to `Cauchy (sumRange expDominant)`** (the `mul two`
//! wrapper `expDominant` carries) is a further step, not free, because of
//! `CReal.mul`'s own index shift (see below) — not attempted here.
//!
//! Separately, once *some* `Cauchy (sumRange expDominant)` witness exists:
//! `CReal.sumRange_cauchy_dominated_ordered_normalized`
//! (`series.rs`) already gives a raw, UNWRAPPED pointwise Cauchy-shaped bound
//! for one ordered pair `a ≤ b` from exactly this kind of domination (`∀x, le
//! (abs (f x)) (g x)`, plus a Cauchy witness for `sumRange g` in the same raw
//! form) — `exp_term_abs_le_dominant` already supplies the domination
//! hypothesis, so only the nonnegativity-derived `abs` shape and the
//! `Cauchy (sumRange expDominant)` witness are missing. Then the
//! `Nat.le_total` split on top of `sum_range_cauchy_dominated_ordered_normalized`
//! (mirroring what `sum_range_cauchy_of_dominated` does internally, but
//! stopping short of its final `Exists.intro`) gives a concrete-`K` pointwise
//! Cauchy bound for `sumRange expTerm`, which is exactly the shape
//! [`CRealPrelude::regular_of_scaled_cauchy`] consumes to build `CReal.e :=
//! CReal.mk (speedup (diagonal expSeriesPartial) K) (...)` directly — see
//! `creal/convergence.rs` for `regular_of_scaled_cauchy`/`speedup`, and
//! `creal/completeness.rs` for the `CReal.mk`-on-an-explicit-sequence pattern
//! this needs (an `Exists`-elimination into `CReal` data is not available in
//! this kernel; `converges_of_cauchy`'s own `∃ L, …` cannot be unwrapped for
//! this purpose).
//!
//! **Historical note, since the naming below is easy to misread against the
//! code that actually shipped.** This file's original diagnosis (before the
//! domination bound existed) framed the choice as route (a) — bridge
//! `CReal.pow` to a `Rat.pow` via `CReal.ofRat_pow` — versus route (b) — skip
//! `CReal.pow` and `Rat.normalize` a genuinely rational bound directly.
//! `declare_exp_term_le_geom` (route (b)) proves the domination against a
//! **raw `Rat.normalize`d** rational; the separate `CReal.expDominant`
//! (`declare_exp_dominant`, below) then bridges that to a `CReal.pow`-based
//! form (`mul two (pow half n)`) so that `sumRange_pow_half_closed_form` and
//! `pow_half_le_nat_div_succ` — both stated over `CReal.pow` — apply to it.
//! So the shipped construction uses **both**: route (b) for the one-shot
//! comparison, route (a)'s `CReal.pow` shape for everything built since.

use super::convergence::{
    converges_applied, converges_predicate, div_succ_at, exists_elim, exists_intro, exists_ty,
    kregular_of_cauchy_proof,
};
use super::product::{index_le, mul_index, mul_shift, regular_between};
use super::series::{
    assoc_rev_eq, exists_nat_intro, fuse_same_index, sum_range_cauchy_body, within_symm,
};
use super::{
    CRealPrelude, DERIVED_HEIGHT, creal_ty, div_succ, embed, equiv, halves, sample, shift, weaken,
    within,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::RatPrelude;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    den, den_z, iregroup4, nat_rewrite_prop, normalize, num, radd, rat_eq_rewrite, rchain, rcongr,
    rle, rmul, rneg, rone, rpow, rzero,
};

/// Height for `expTerm`/`expSeriesPartial`: both are thin definitional
/// wrappers (one `ofRat` application, one partial application of
/// `sumRange`), so one step above every `Rat`/`CReal` leaf they call is
/// enough — the callees' own heights govern how far *they* unfold.
const EXP_HEIGHT: u16 = DERIVED_HEIGHT + 1;

/// Admit `CReal.expTerm` and `CReal.expSeriesPartial`. See the module
/// documentation for what is deliberately not attempted here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exponential(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_exp_term(d, p)?;
    declare_exp_series_partial(d, p)?;
    declare_exp_term_le_geom(d, p)?;
    declare_exp_dominant(d, p)?;
    declare_exp_term_le_dominant(d, p)?;
    declare_exp_term_nonneg(d, p)?;
    declare_exp_dominant_nonneg(d, p)?;
    declare_exp_term_abs_le_dominant(d, p)?;
    declare_sum_pow_half_closed_form(d, p)
}

/// `Rat.normalize (Int.ofNat (Nat.succ Nat.zero)) (Nat.factorial n)
/// (Nat.one_le_factorial n)` — the rational `1/n!`, already reduced by
/// `Rat.normalize`'s own `gcd` bookkeeping.
fn inv_factorial(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);
    let denominator = d.factorial(n);
    let np = d.prelude();
    let positive = d.lemma(np.one_le_factorial, &[n]);
    normalize(d, one_int, denominator, positive)
}

/// `CReal.expTerm : Nat → CReal := fun n => ofRat (1/n!)`.
fn declare_exp_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let term = inv_factorial(d, n);
    let body = embed(d, p, term);

    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.exp_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXP_HEIGHT),
    })
}

/// `CReal.expSeriesPartial : Nat → CReal := CReal.sumRange CReal.expTerm`.
fn declare_exp_series_partial(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let exp_term = d.kernel().const_(p.exp_term, vec![]);
    let value = d.const_app(p.sum_range, &[exp_term]);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.exp_series_partial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXP_HEIGHT),
    })
}

// --- the domination bound `1/n! ≤ 2·(1/2)ⁿ` --------------------------------
//
// The whole chain below stays at `Rat`/`Nat`, never touching `CReal.pow` or
// `CReal.inv` (route (b) this file's own module documentation names), and is
// closed with one application of [`CRealPrelude::of_rat_le`] at the end. The
// `Nat` engine is `two_pow_le_two_mul_factorial` (`2ⁿ ≤ 2·n!`, unconditional);
// everything above it is bookkeeping to read that fact back through
// `Rat.normalize`'s cross-multiplication definition of `Rat.le`.

/// `Nat.le 1 2`.
fn one_le_two_nat(d: &mut IntDev<'_>) -> ExprId {
    let np = d.prelude();
    let zero = d.zero();
    let one = d.num(1);
    let h0 = d.lemma(np.zero_le, &[one]); // Le 0 1
    d.lemma(np.le_succ_succ, &[zero, one, h0]) // Le (succ 0) (succ 1) = Le 1 2
}

/// `Nat.le 2 (Nat.succ (Nat.succ m))`, for any `m`.
fn nat_two_le_succ_succ(d: &mut IntDev<'_>, m: ExprId) -> ExprId {
    let np = d.prelude();
    let zero = d.zero();
    let one = d.num(1);
    let succ_m = d.succ(m);
    let h0 = d.lemma(np.zero_le, &[m]); // Le 0 m
    let h1 = d.lemma(np.le_succ_succ, &[zero, m, h0]); // Le 1 (succ m)
    d.lemma(np.le_succ_succ, &[one, succ_m, h1]) // Le 2 (succ (succ m))
}

/// `Nat.le a b -> Nat.le (a*c) (b*c)`. `Nat.mul_le_mul_left` only gives
/// `c*a ≤ c*b`; this flips both sides with `mul_comm`.
fn nat_le_mul_right(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, h: ExprId) -> ExprId {
    let np = d.prelude();
    let ca = d.mul(c, a);
    let cb = d.mul(c, b);
    let ac = d.mul(a, c);
    let bc = d.mul(b, c);
    let h_prime = d.lemma(np.mul_le_mul_left, &[c, a, b, h]); // Le ca cb
    let eq_ca = d.lemma(np.mul_comm, &[c, a]); // Eq ca ac
    let motive1 = d.eq_motive(ca, &|d, x| d.le(x, cb));
    let step1 = d.transport(ca, motive1, h_prime, ac, eq_ca); // Le ac cb
    let eq_cb = d.lemma(np.mul_comm, &[c, b]); // Eq cb bc
    let motive2 = d.eq_motive(cb, &|d, x| d.le(ac, x));
    d.transport(cb, motive2, step1, bc, eq_cb) // Le ac bc
}

/// `Nat.le (Nat.pow 2 (Nat.succ j)) (Nat.mul 2 (Nat.factorial (Nat.succ j)))`
/// — the "shifted by one" statement, provable by an UNCONDITIONAL induction
/// on `j` (see [`two_pow_le_two_mul_factorial`]'s doc comment for why the
/// *un*-shifted statement's step is not unconditional, and why shifting by
/// one repairs exactly that).
fn aux_bound(d: &mut IntDev<'_>, j: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId {
        let two = d.num(2);
        let succ_m = d.succ(m);
        let p = d.pow(two, succ_m);
        let f = d.factorial(succ_m);
        let mf = d.mul(two, f);
        d.le(p, mf)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let two = d.num(2);
        let np = d.prelude();
        d.lemma(np.le_refl, &[two])
        // motive(zero) = Le (pow 2 1) (mul 2 (factorial 1)) = Le 2 2 by
        // computation alone (pow 2 1 ≡ 2, factorial 1 ≡ 1, mul 2 1 ≡ 2).
    };
    let step = |d: &mut IntDev<'_>, k: ExprId, ih: ExprId| -> ExprId {
        // ih : Le (pow 2 (succ k)) (mul 2 (factorial (succ k)))
        let np = d.prelude();
        let two = d.num(2);
        let succ_k = d.succ(k);
        let f_val = d.factorial(succ_k); // F := factorial (succ k)
        let mul2f = d.mul(two, f_val); // 2*F

        // Scale `ih` by 2 on the right: Le ((pow 2 (succ k))*2) ((2*F)*2).
        let p_val = d.pow(two, succ_k); // P := pow 2 (succ k)
        let h_scaled = nat_le_mul_right(d, p_val, mul2f, two, ih);
        let two_f_two = d.mul(mul2f, two); // (2*F)*2

        // Reassociate to `2*(F*2)` via `mul_assoc`.
        let f_two = d.mul(f_val, two); // F*2
        let two_f2 = d.mul(two, f_two); // 2*(F*2)
        let eq_assoc = d.lemma(np.mul_assoc, &[two, f_val, two]); // Eq ((2*F)*2) (2*(F*2))
        let p_two = d.mul(p_val, two); // P*2
        let motive_r = d.eq_motive(two_f_two, &|d, x| d.le(p_two, x));
        let h_scaled2 = d.transport(two_f_two, motive_r, h_scaled, two_f2, eq_assoc);
        // h_scaled2 : Le (P*2) (2*(F*2))

        // `2 ≤ succ (succ k)`, multiplied through `F` on the left and then
        // `2` on the left again, to reach `2*(F*2) ≤ 2*(F*succ(succ k))`.
        let succ_succ_k = d.succ(succ_k);
        let two_le_ss = nat_two_le_succ_succ(d, k); // Le 2 (succ (succ k))
        let h2 = d.lemma(np.mul_le_mul_left, &[f_val, two, succ_succ_k, two_le_ss]);
        // h2 : Le (F*2) (F*(succ (succ k)))
        let f_ss = d.mul(f_val, succ_succ_k);
        let h3 = d.lemma(np.mul_le_mul_left, &[two, f_two, f_ss, h2]);
        // h3 : Le (2*(F*2)) (2*(F*(succ (succ k))))
        let two_f_ss = d.mul(two, f_ss);
        d.lemma(np.le_trans, &[p_two, two_f2, two_f_ss, h_scaled2, h3])
        // : Le (P*2) (2*(F*(succ (succ k))))
        //   ≡ Le (pow 2 (succ (succ k))) (mul 2 (factorial (succ (succ k))))
        //   by one ι-step each side (`pow_succ`, `factorial_succ`).
    };
    d.induct(&motive, &base, &step, j)
}

/// `Nat.le (Nat.pow 2 n) (Nat.mul 2 (Nat.factorial n))` — `2ⁿ ≤ 2·n!`,
/// unconditional on `n`.
///
/// The naive induction on this exact statement is **not** clean: doubling
/// the inductive hypothesis `2ⁿ ≤ 2·n!` gives `2ⁿ⁺¹ ≤ 4·n!`, and closing
/// `4·n! ≤ 2·(n+1)·n!` needs `2 ≤ n+1`, which FAILS at `n=0` (`4·0! = 4 >
/// 2 = 2·1·0!`). Shifting the statement by one repairs this: proving it at
/// `succ j` from a hypothesis already at `succ j` needs `2 ≤ succ(succ j) =
/// j+2`, true for every `j` including `j=0` — see [`aux_bound`]. This
/// theorem is that shifted statement plus the one base case (`n=0`) it
/// does not cover.
fn two_pow_le_two_mul_factorial(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let two = d.num(2);
        let p = d.pow(two, x);
        let f = d.factorial(x);
        let mf = d.mul(two, f);
        d.le(p, mf)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId { one_le_two_nat(d) };
    let step = |d: &mut IntDev<'_>, j: ExprId, _ih: ExprId| -> ExprId { aux_bound(d, j) };
    d.induct(&motive, &base, &step, n)
}

/// `1/n! ≤ 2/2ⁿ`, as a pure `Rat` fact proved by cross-multiplication against
/// [`two_pow_le_two_mul_factorial`]. Returns `(q, r, proof)`: `q` is the same
/// term [`inv_factorial`] builds, `r = Rat.normalize 2 (2ⁿ) _`, and
/// `proof : Rat.le q r`.
///
/// Mirrors `rat_prelude/archimedean.rs::declare_nat_div_succ_antitone`,
/// generalized off that theorem's "both numerators are 1" shortcut: only
/// `q`'s numerator is 1 here, so `r`'s side keeps its own `2·` factor through
/// the chain instead of cancelling it via `one_mul`.
#[allow(clippy::too_many_lines)]
fn exp_term_le_dominant_rat(
    d: &mut IntDev<'_>,
    rp: RatPrelude,
    n: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let np = d.prelude();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let one_z = d.of_nat(one_nat);
    let two_z = d.of_nat(two_nat);

    let d1 = d.factorial(n); // n!
    let d2 = d.pow(two_nat, n); // 2^n
    let h1 = d.lemma(np.one_le_factorial, &[n]);
    let h2 = {
        let lt02 = one_le_two_nat(d); // Le 1 2, defeq to `Lt 0 2`
        d.lemma(np.pow_pos, &[two_nat, n, lt02])
    };

    let q = normalize(d, one_z, d1, h1);
    let r = normalize(d, two_z, d2, h2);

    let na = num(d, q);
    let daz = den_z(d, q);
    let nb = num(d, r);
    let dbz = den_z(d, r);
    let da = den(d, q);
    let db = den(d, r);
    let d1z = d.of_nat(d1);
    let d2z = d.of_nat(d2);

    // eqa : na * d1z = daz (numerator 1, simplifies via `one_mul`).
    let cross_a = d.lemma(rp.normalize_cross, &[one_z, d1, h1]);
    let one_z_daz = d.imul(one_z, daz);
    let na_d1z = d.imul(na, d1z);
    let one_mul_da_nat = d.lemma(np.one_mul, &[da]);
    let one_mul_da_product = NatOps::mul(d, one_nat, da);
    let one_mul_da = d.nat_eq_to_int(one_mul_da_product, da, one_mul_da_nat, &|d, t| d.of_nat(t));
    let (_, eqa) = d.ichain(na_d1z, &[(one_z_daz, cross_a), (daz, one_mul_da)]);

    // eqb : nb * d2z = two_z * dbz (kept as-is: numerator 2, no shortcut).
    let eqb = d.lemma(rp.normalize_cross, &[two_z, d2, h2]);
    let nb_d2z = d.imul(nb, d2z);

    // The `Nat` engine, defeq to `Int.le d2z (two_z*d1z)`.
    let h_nat = two_pow_le_two_mul_factorial(d, n);
    let two_z_d1z = d.imul(two_z, d1z);
    let dadb_nat = NatOps::mul(d, da, db);
    let scaled_hyp = d.lemma(rp.int_mul_le_mul_right, &[d2z, two_z_d1z, dadb_nat, h_nat]);
    let dadbz = d.imul(daz, dbz);
    let source_lhs = d.imul(d2z, dadbz);
    let source_rhs = d.imul(two_z_d1z, dadbz);

    // Goal (after unfolding `Rat.le`): `Int.le (na*dbz) (nb*daz)`.
    let na_dbz = d.imul(na, dbz);
    let nb_daz = d.imul(nb, daz);
    let na_dbz_d1z = d.imul(na_dbz, d1z);
    let goal_lhs = d.imul(na_dbz_d1z, d2z); // ((na*dbz)*d1z)*d2z
    let nb_daz_d1z = d.imul(nb_daz, d1z);
    let goal_rhs = d.imul(nb_daz_d1z, d2z); // ((nb*daz)*d1z)*d2z

    // --- LHS: ((na*dbz)*d1z)*d2z = d2z*(daz*dbz) ---
    let regroup_lhs = iregroup4(d, [na, dbz, d1z, d2z], [na, d1z, dbz, d2z]);
    let na_d1z_dbz = d.imul(na_d1z, dbz);
    let regrouped_lhs = d.imul(na_d1z_dbz, d2z); // ((na*d1z)*dbz)*d2z
    let subst_lhs = d.icongr(na_d1z, daz, eqa, &|d, t| {
        let head = d.imul(t, dbz);
        d.imul(head, d2z)
    });
    let daz_dbz_d2z = d.imul(dadbz, d2z); // (daz*dbz)*d2z
    let commute_lhs = d.lemma(rp.int.mul_comm, &[dadbz, d2z]); // Eq ((daz*dbz)*d2z) (d2z*(daz*dbz))
    let (_, lhs_chain) = d.ichain(
        goal_lhs,
        &[
            (regrouped_lhs, regroup_lhs),
            (daz_dbz_d2z, subst_lhs),
            (source_lhs, commute_lhs),
        ],
    );

    // --- RHS: ((nb*daz)*d1z)*d2z = (two_z*d1z)*(daz*dbz) ---
    let regroup_rhs1 = iregroup4(d, [nb, daz, d1z, d2z], [nb, d2z, daz, d1z]);
    let nb_d2z_daz = d.imul(nb_d2z, daz);
    let regrouped_rhs1 = d.imul(nb_d2z_daz, d1z); // ((nb*d2z)*daz)*d1z
    let two_z_dbz = d.imul(two_z, dbz);
    let subst_rhs = d.icongr(nb_d2z, two_z_dbz, eqb, &|d, t| {
        let head = d.imul(t, daz);
        d.imul(head, d1z)
    });
    let two_z_dbz_daz = d.imul(two_z_dbz, daz);
    let mid_rhs = d.imul(two_z_dbz_daz, d1z); // ((two_z*dbz)*daz)*d1z
    let regroup_rhs2 = iregroup4(d, [two_z, dbz, daz, d1z], [two_z, d1z, daz, dbz]);
    let two_z_d1z_daz = d.imul(two_z_d1z, daz);
    let regrouped_rhs2 = d.imul(two_z_d1z_daz, dbz); // ((two_z*d1z)*daz)*dbz
    let assoc_rhs = d.lemma(rp.int.mul_assoc, &[two_z_d1z, daz, dbz]);
    // Eq (((two_z*d1z)*daz)*dbz) ((two_z*d1z)*(daz*dbz))
    let (_, rhs_chain) = d.ichain(
        goal_rhs,
        &[
            (regrouped_rhs1, regroup_rhs1),
            (mid_rhs, subst_rhs),
            (regrouped_rhs2, regroup_rhs2),
            (source_rhs, assoc_rhs),
        ],
    );

    let back_lhs = d.isymm(goal_lhs, source_lhs, lhs_chain); // Eq source_lhs goal_lhs
    let at_lhs = d.int_eq_rewrite(source_lhs, goal_lhs, back_lhs, scaled_hyp, &|d, z| {
        d.ile(z, source_rhs)
    });
    let back_rhs = d.isymm(goal_rhs, source_rhs, rhs_chain); // Eq source_rhs goal_rhs
    let scaled_goal = d.int_eq_rewrite(source_rhs, goal_rhs, back_rhs, at_lhs, &|d, z| {
        d.ile(goal_lhs, z)
    });

    // Reshape `(na_dbz*d1z)*d2z ≤ (nb_daz*d1z)*d2z` (left-associated, what the
    // regroup/substitute chains above produce) into `na_dbz*(d1z*d2z) ≤
    // nb_daz*(d1z*d2z)` (a SINGLE multiplication by `d1z*d2z` on each side) —
    // `int_le_of_mul_le_mul_right`'s conclusion shape is `a*(ofNat c)`, not
    // `(a*x)*y`, and these are only propositionally (not definitionally)
    // equal: `Int.mul` does not auto-associate. `d1z*d2z` is itself defeq to
    // `ofNat (d1*d2)` (one ι-step on `Int.mul`'s `ofNat`/`ofNat` case), so
    // this is the only reshaping actually needed.
    let d1z_d2z = d.imul(d1z, d2z);
    let na_dbz_reshaped = d.imul(na_dbz, d1z_d2z);
    let assoc_lhs_final = d.lemma(rp.int.mul_assoc, &[na_dbz, d1z, d2z]);
    // Eq (goal_lhs) (na_dbz_reshaped)
    let reshaped1 = d.int_eq_rewrite(
        goal_lhs,
        na_dbz_reshaped,
        assoc_lhs_final,
        scaled_goal,
        &|d, z| d.ile(z, goal_rhs),
    );
    let nb_daz_reshaped = d.imul(nb_daz, d1z_d2z);
    let assoc_rhs_final = d.lemma(rp.int.mul_assoc, &[nb_daz, d1z, d2z]);
    // Eq (goal_rhs) (nb_daz_reshaped)
    let reshaped2 = d.int_eq_rewrite(
        goal_rhs,
        nb_daz_reshaped,
        assoc_rhs_final,
        reshaped1,
        &|d, z| d.ile(na_dbz_reshaped, z),
    );
    // reshaped2 : Int.le (na_dbz*(d1z*d2z)) (nb_daz*(d1z*d2z))

    // Cancel the common (positive) factor `d1*d2`.
    let d1d2_nat = NatOps::mul(d, d1, d2);
    let one_le_d1d2 = d.lemma(np.one_le_mul, &[d1, d2, h1, h2]);
    let proof = d.lemma(
        rp.int_le_of_mul_le_mul_right,
        &[na_dbz, nb_daz, d1d2_nat, one_le_d1d2, reshaped2],
    );
    (q, r, proof)
}

/// `CReal.le x y` — local helper, matching every other `creal/*` module's
/// own private `cle` (see e.g. `geometric.rs`).
fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

/// `CReal.expTerm_le_geom : ∀ n, le (expTerm n) (ofRat (Rat.normalize 2 (2ⁿ)
/// _))` — the paper's `1/n! ≤ 2·(1/2)ⁿ`, for every `n`, no case split. See
/// [`exp_term_le_dominant_rat`] for the `Rat`-level proof and
/// [`two_pow_le_two_mul_factorial`] for the `Nat` engine underneath it.
fn declare_exp_term_le_geom(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rp = p.rat;

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let (q, r, rat_le) = exp_term_le_dominant_rat(d, rp, n);
    let rhs = embed(d, p, r);
    let creal_le = d.lemma(p.of_rat_le, &[q, r, rat_le]);

    let exp_term_n = {
        let exp_term = d.kernel().const_(p.exp_term, vec![]);
        d.kernel().app(exp_term, n)
    };

    let value = d.lam_fv(n_fv, nat, creal_le);
    let ty = {
        let stmt = cle(d, p, exp_term_n, rhs);
        d.pi_fv(n_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_term_le_geom,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// This lane: the domination bound `expTerm_le_geom` bridged to `CReal.pow`
// (`CReal.expDominant`, `CReal.exp_term_le_dominant`), and nonnegativity of
// `expTerm`/`expDominant` (`CReal.exp_term_nonneg`,
// `CReal.exp_dominant_nonneg`), combined into the `abs`-domination shape
// `CReal.sumRange_cauchy_of_dominated` needs.
// ============================================================================

/// `CReal.mul x y`.
fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

/// `CReal.neg x`.
fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `CReal.zero`.
fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `CReal.abs x`.
fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

/// `CReal.pow x n`.
fn cpow(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.pow, &[x, n])
}

/// `Rat.natDivSucc 1 1` — `1/2`, as a `Rat` term.
fn half_rat(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let one_nat = d.num(1);
    div_succ(d, p, 1, one_nat)
}

/// `CReal.ofRat (Rat.natDivSucc 1 1)` — the constant `1/2`.
fn half(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let hr = half_rat(d, p);
    embed(d, p, hr)
}

/// `Rat.normalize (Int.ofNat 2) (Nat.succ Nat.zero) h`, `h : Nat.le 1 1` —
/// `2`, built directly through `normalize` (not `Rat.natDivSucc`) so it
/// matches `Rat.normalize_mul_normalize`'s own argument shape on the nose.
/// Returns `(rat_term, numerator, denominator_positivity)`.
fn two_normalize(d: &mut IntDev<'_>, _p: CRealPrelude) -> (ExprId, ExprId, ExprId) {
    let np = d.prelude();
    let two_nat = d.num(2);
    let two_z = d.of_nat(two_nat);
    let one_nat = d.num(1);
    let h1 = d.lemma(np.le_refl, &[one_nat]);
    let r = normalize(d, two_z, one_nat, h1);
    (r, two_z, h1)
}

/// `CReal.ofRat` of [`two_normalize`] — `CReal`'s constant `2`.
fn two(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let (r, _, _) = two_normalize(d, p);
    embed(d, p, r)
}

/// `mul two (pow half n)` — the `CReal.pow`-based reading of
/// [`declare_exp_term_le_geom`]'s own bound, `2 · (1/2)ⁿ`.
fn exp_dominant_at(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let h = half(d, p);
    let t = two(d, p);
    let pw = cpow(d, p, h, n);
    cmul(d, p, t, pw)
}

/// `CReal.expDominant : Nat → CReal := fun n => mul two (pow half n)`.
fn declare_exp_dominant(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let body = exp_dominant_at(d, p, n);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.exp_dominant,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXP_HEIGHT),
    })
}

/// `Equiv (ofRat a) (ofRat b)`, from `Eq Rat a b`.
fn ofrat_congr(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, eqp: ExprId) -> ExprId {
    let oa = embed(d, p, a);
    let refl = d.lemma(p.equiv_refl, &[oa]);
    rat_eq_rewrite(d, a, b, eqp, refl, &|d, t| {
        let ot = embed(d, p, t);
        equiv(d, p, oa, ot)
    })
}

/// `Equiv (expDominant n) (ofRat r)`, `r := Rat.normalize 2 (2ⁿ) h2` — the
/// EXACT rational [`exp_term_le_dominant_rat`] builds (same `d2`, `h2`).
///
/// Chain: `pow half n ≈ ofRat (Rat.pow half_rat n)` ([`CRealPrelude::of_rat_pow`])
/// `= ofRat (normalize 1 (2ⁿ) h2)` (`Rat.pow_natDivSucc_two`, reusing `h2`
/// for its internal witness — both prove `1 ≤ 2ⁿ`, and `Rat.normalize`'s
/// witness slot is a `Prop`, so proof irrelevance identifies the two forms).
/// Multiplying both sides by `two` and simplifying
/// `Rat.mul (natDivSucc 2 0) (normalize 1 (2ⁿ) h2) = normalize 2 (2ⁿ) h2`
/// (`Rat.normalize_mul_normalize` + `Rat.normalize_congr`) lands on `r`.
///
/// Returns `(r, equiv_proof : Equiv (expDominant n) (ofRat r))`.
fn exp_dominant_equiv_r(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> (ExprId, ExprId) {
    let rp = p.rat;
    let np = d.prelude();

    let two_nat = d.num(2);
    let d2 = d.pow(two_nat, n);
    let h2 = {
        let lt02 = one_le_two_nat(d);
        d.lemma(np.pow_pos, &[two_nat, n, lt02])
    };
    let one_nat = d.num(1);
    let one_z = d.of_nat(one_nat);
    let (two_r, two_z, h1) = two_normalize(d, p);

    // A: `Equiv (pow half n) (ofRat (Rat.pow half_rat n))`.
    let hr = half_rat(d, p);
    let h_val = half(d, p);
    let pow_h_n = cpow(d, p, h_val, n);
    let rat_pow_h_n = rpow(d, rp, hr, n);
    let a_equiv = d.lemma(p.of_rat_pow, &[hr, n]);

    // B: `Rat.pow half_rat n = normalize 1 (2ⁿ) h2`.
    let target = normalize(d, one_z, d2, h2);
    let bridge_eq = d.lemma(rp.pow_nat_div_succ_two, &[n]);
    let b_step = ofrat_congr(d, p, rat_pow_h_n, target, bridge_eq);
    let ofrat_pow = embed(d, p, rat_pow_h_n);
    let ofrat_target = embed(d, p, target);
    let ab_equiv = d.lemma(
        p.equiv_trans,
        &[pow_h_n, ofrat_pow, ofrat_target, a_equiv, b_step],
    );

    // C: multiply both sides by `two`.
    let dominant = exp_dominant_at(d, p, n);
    let ofrat_two = embed(d, p, two_r);
    let refl_two = d.lemma(p.equiv_refl, &[ofrat_two]);
    let c_equiv = d.lemma(
        p.mul_congr,
        &[
            ofrat_two,
            ofrat_two,
            pow_h_n,
            ofrat_target,
            refl_two,
            ab_equiv,
        ],
    );
    let mul_two_target = cmul(d, p, ofrat_two, ofrat_target);

    // D: `Equiv (mul (ofRat two_r) (ofRat target)) (ofRat (Rat.mul two_r target))`.
    let d_step = d.lemma(p.of_rat_mul, &[two_r, target]);
    let rat_mul_two_target = rmul(d, two_r, target);
    let ofrat_mul = embed(d, p, rat_mul_two_target);
    let d_equiv = d.lemma(
        p.equiv_trans,
        &[dominant, mul_two_target, ofrat_mul, c_equiv, d_step],
    );

    // E: `Rat.mul two_r target = Rat.normalize 2 (2ⁿ) h2`.
    let nat_mul_1_d2 = NatOps::mul(d, one_nat, d2);
    let step_mul_norm = d.lemma(
        rp.normalize_mul_normalize,
        &[two_z, one_nat, h1, one_z, d2, h2],
    );
    let one_mul_eq = d.lemma(np.one_mul, &[d2]);
    let one_mul_rev = NatOps::symm(d, nat_mul_1_d2, d2, one_mul_eq);
    let h3 = nat_rewrite_prop(d, d2, nat_mul_1_d2, one_mul_rev, h2, &|d, t| {
        d.le(one_nat, t)
    });
    let one_mul_int = d.nat_eq_to_int(nat_mul_1_d2, d2, one_mul_eq, &|d, t| d.of_nat(t));
    let d2_z = d.of_nat(d2);
    let nat_mul_1_d2_z = d.of_nat(nat_mul_1_d2);
    let cross_fwd = d.icongr(nat_mul_1_d2_z, d2_z, one_mul_int, &|d, t| d.imul(two_z, t));
    let lhs_cross = d.imul(two_z, nat_mul_1_d2_z);
    let rhs_cross = d.imul(two_z, d2_z);
    let cross = d.isymm(lhs_cross, rhs_cross, cross_fwd);
    let e_congr = d.lemma(
        rp.normalize_congr,
        &[two_z, nat_mul_1_d2, h3, two_z, d2, h2, cross],
    );
    let r = normalize(d, two_z, d2, h2);
    let normalize_mid = normalize(d, two_z, nat_mul_1_d2, h3);
    let (_, e_eq) = rchain(
        d,
        rat_mul_two_target,
        &[(normalize_mid, step_mul_norm), (r, e_congr)],
    );

    let e_equiv = ofrat_congr(d, p, rat_mul_two_target, r, e_eq);
    let ofrat_r = embed(d, p, r);
    let final_equiv = d.lemma(
        p.equiv_trans,
        &[dominant, ofrat_mul, ofrat_r, d_equiv, e_equiv],
    );
    (r, final_equiv)
}

/// `CReal.exp_term_le_dominant : ∀ n, le (expTerm n) (expDominant n)` —
/// [`declare_exp_term_le_geom`]'s bound, transported along
/// [`exp_dominant_equiv_r`]'s `Equiv` into the `CReal.pow`-based reading.
fn declare_exp_term_le_dominant(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let exp_term_n = {
        let exp_term = d.kernel().const_(p.exp_term, vec![]);
        d.kernel().app(exp_term, n)
    };
    let (r, dom_equiv) = exp_dominant_equiv_r(d, p, n);
    let rhs = embed(d, p, r);
    let dominant = exp_dominant_at(d, p, n);

    let le_geom = d.lemma(p.exp_term_le_geom, &[n]);
    let refl_term = d.lemma(p.equiv_refl, &[exp_term_n]);
    let dom_equiv_rev = d.lemma(p.equiv_symm, &[dominant, rhs, dom_equiv]);
    let concl = d.lemma(
        p.le_congr,
        &[
            exp_term_n,
            exp_term_n,
            rhs,
            dominant,
            refl_term,
            dom_equiv_rev,
            le_geom,
        ],
    );

    let value = d.lam_fv(n_fv, nat, concl);
    let ty = {
        let stmt = cle(d, p, exp_term_n, dominant);
        d.pi_fv(n_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_term_le_dominant,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.le Rat.zero (Rat.normalize 1 n! h)`, mirroring
/// `rat_prelude/group.rs`'s `zero_le_natDivSucc` cross-multiplication
/// technique, generalized off `natDivSucc`'s fixed `succ j` denominator
/// shape to an arbitrary positive denominator (`Nat.factorial n`, witnessed
/// by `Nat.one_le_factorial`).
fn expterm_nonneg_proof(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> (ExprId, ExprId) {
    let rp = p.rat;
    let np = d.prelude();
    let one_nat = d.num(1);
    let one_z = d.of_nat(one_nat);
    let factorial_n = d.factorial(n);
    let positive = d.lemma(np.one_le_factorial, &[n]);
    let value = normalize(d, one_z, factorial_n, positive);

    let actual = num(d, value);
    let actual_den = den(d, value);
    let actual_den_z = den_z(d, value);
    let denominator_z = d.of_nat(factorial_n);
    let zero = d.izero();

    let cross = d.lemma(rp.normalize_cross, &[one_z, factorial_n, positive]);
    let product = d.imul(one_z, actual_den_z);
    let product_nonneg = {
        let magnitude = NatOps::mul(d, one_nat, actual_den);
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
        &[zero, actual, factorial_n, positive, rebalanced],
    );
    let proof = d.const_app(rp.nonneg_of_int_nonneg, &[value, cancelled]);
    (value, proof)
}

/// `CReal.exp_term_nonneg : ∀ n, le zero (expTerm n)`.
fn declare_exp_term_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let (rat_value, rat_nonneg) = expterm_nonneg_proof(d, p, n);
    let zero_rat = crate::rat_prelude::ops::rzero(d, p.rat);
    let creal_nonneg = d.lemma(p.of_rat_le, &[zero_rat, rat_value, rat_nonneg]);

    let exp_term_n = {
        let exp_term = d.kernel().const_(p.exp_term, vec![]);
        d.kernel().app(exp_term, n)
    };

    let proof_value = d.lam_fv(n_fv, nat, creal_nonneg);
    let ty = {
        let z = czero(d, p);
        let stmt = cle(d, p, z, exp_term_n);
        d.pi_fv(n_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_term_nonneg,
        uparams: vec![],
        ty,
        value: proof_value,
    })
}

/// `le zero half`, via `Rat.zero_le_natDivSucc 1 1` and `CReal.of_rat_le`.
///
/// Extracted from [`declare_exp_dominant_nonneg`] so [`declare_e_le_four`] can
/// reuse it without re-deriving.
fn half_nonneg_proof(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rp = p.rat;
    let zero_rat = crate::rat_prelude::ops::rzero(d, rp);
    let one_nat = d.num(1);
    let half_le_zero = d.lemma(rp.zero_le_nat_div_succ, &[one_nat, one_nat]);
    let hr = half_rat(d, p);
    d.lemma(p.of_rat_le, &[zero_rat, hr, half_le_zero])
}

/// `le zero two`: `two_r := normalize 2 1 h1` (the SAME construction
/// [`two`]/[`exp_dominant_at`] use), by `expterm_nonneg_proof`'s
/// cross-multiplication technique with numerator `2` and denominator `1`.
///
/// Extracted from [`declare_exp_dominant_nonneg`] so [`declare_e_le_four`] can
/// reuse it without re-deriving.
fn two_nonneg_proof(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rp = p.rat;
    let zero_rat = crate::rat_prelude::ops::rzero(d, rp);
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

/// `CReal.exp_dominant_nonneg : ∀ n, le zero (expDominant n)` — from
/// [`CRealPrelude::mul_nonneg`], `0 ≤ two` ([`two_nonneg_proof`]) and
/// [`CRealPrelude::pow_nonneg`] at `0 ≤ half` ([`half_nonneg_proof`]).
fn declare_exp_dominant_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let half_nonneg = half_nonneg_proof(d, p);
    let h = half(d, p);
    let two_nonneg = two_nonneg_proof(d, p);
    let t = two(d, p);

    // `0 ≤ pow half n`, then `0 ≤ mul two (pow half n)`.
    let pow_nonneg = d.lemma(p.pow_nonneg, &[h, half_nonneg, n]);
    let pow_h_n = cpow(d, p, h, n);
    let mul_nonneg = d.lemma(p.mul_nonneg, &[t, pow_h_n, two_nonneg, pow_nonneg]);

    let dominant = exp_dominant_at(d, p, n);
    let proof_value = d.lam_fv(n_fv, nat, mul_nonneg);
    let ty = {
        let z = czero(d, p);
        let stmt = cle(d, p, z, dominant);
        d.pi_fv(n_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_dominant_nonneg,
        uparams: vec![],
        ty,
        value: proof_value,
    })
}

/// `CReal.exp_term_abs_le_dominant : ∀ n, le (abs (expTerm n)) (expDominant n)`
/// — the exact `abs`-domination shape [`CRealPrelude::sum_range_cauchy_of_dominated`]
/// and [`CRealPrelude::sum_range_converges_of_dominated`] need. From
/// [`declare_exp_term_le_dominant`] and nonnegativity via
/// [`CRealPrelude::abs_le`]: `neg (expTerm n) ≤ 0 ≤ expDominant n`.
fn declare_exp_term_abs_le_dominant(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let exp_term_n = {
        let exp_term = d.kernel().const_(p.exp_term, vec![]);
        d.kernel().app(exp_term, n)
    };
    let dominant = exp_dominant_at(d, p, n);

    let le_dom = d.lemma(p.exp_term_le_dominant, &[n]);
    let term_nonneg = d.lemma(p.exp_term_nonneg, &[n]);
    let dom_nonneg = d.lemma(p.exp_dominant_nonneg, &[n]);

    // `neg (expTerm n) ≤ neg zero`, then `neg zero ≈ zero ≤ expDominant n`.
    let zero = czero(d, p);
    let neg_le = d.lemma(p.neg_le_neg, &[zero, exp_term_n, term_nonneg]);
    let neg_zero = cneg(d, p, zero);
    let zero_rat = crate::rat_prelude::ops::rzero(d, p.rat);
    let nz_equiv = d.lemma(p.of_rat_neg, &[zero_rat]);
    // `nz_equiv : Equiv (neg zero) (ofRat (Rat.neg Rat.zero))`, and
    // `Rat.neg Rat.zero` is defeq `Rat.zero` (`Int.neg Int.zero ≡
    // Int.zero`), so this already is, up to defeq, `Equiv (neg zero) zero`.
    let refl_dom = d.lemma(p.equiv_refl, &[dominant]);
    let neg_zero_le_dom = d.lemma(
        p.le_congr,
        &[
            neg_zero, zero, dominant, dominant, nz_equiv, refl_dom, dom_nonneg,
        ],
    );
    let neg_exp_term_n = cneg(d, p, exp_term_n);
    let neg_term_le_dom = d.lemma(
        p.le_trans,
        &[neg_exp_term_n, neg_zero, dominant, neg_le, neg_zero_le_dom],
    );

    let abs_le = d.lemma(p.abs_le, &[exp_term_n, dominant, le_dom, neg_term_le_dom]);

    let value = d.lam_fv(n_fv, nat, abs_le);
    let ty = {
        let abs_term = cabs(d, p, exp_term_n);
        let stmt = cle(d, p, abs_term, dominant);
        d.pi_fv(n_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_term_abs_le_dominant,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// Toward `Cauchy (sumRange expTerm)`/`Converges expSeriesPartial`: a closed
// form for `sumRange (pow half)` (needing `2 · (1 − 1/2) ≈ 1`, an honest new
// concrete `Rat` fact — see [`rat_two_mul_half_eq_one`]'s own doc for why the
// obvious `Eq.refl` does NOT close it), and `pow half n → 0`.
// ============================================================================

/// `Rat.mul (Rat.normalize 2 1 h_a) (Rat.normalize 1 2 h_b) = Rat.one`, i.e.
/// `2 · (1/2) = 1`.
///
/// **This does NOT hold by `Eq.refl`** — confirmed empirically (a throwaway
/// probe declaration built exactly this claim via `rrefl` and the kernel
/// rejected it with `TypeMismatch`): `Rat.normalize`'s reduction to lowest
/// terms goes through `Nat.gcd`, which (unlike `Nat.pow`/`Nat.mul`/`Nat.add`
/// on LITERAL arguments) does not unfold via ι alone, even for concrete
/// inputs. So `Rat.normalize (Int.ofNat 2) 2 h` is not *definitionally*
/// `Rat.one`, and closing this needs an actual argument.
///
/// Route: [`RatPrelude::normalize_mul_normalize`] turns the product into
/// `Rat.normalize (Int.mul 2 1) (Nat.mul 1 2) h_c` — both `Int.mul 2 1` and
/// `Nat.mul 1 2` are LITERAL-LITERAL and reduce by ι alone (no symbolic
/// operand, so the "symbolic side" trap does not apply), landing on
/// `Rat.normalize 2 2 h_c`. Then `Rat.normalize 2 2 h_c = Rat.one` by
/// [`RatPrelude::eq_of_cross`]: `Rat.one` is a **direct** `Rat.mk` (not
/// itself built through `normalize` — `rat_prelude/defs.rs::declare_constants`
/// — so `num`/`den` project off it by ι alone, unlike the `Nat.gcd`-bound
/// projections off `Rat.normalize 2 2 h_c`), and the cross condition reduces
/// to `num (normalize 2 2 h_c) = den_z (normalize 2 2 h_c)`, itself gotten
/// from [`RatPrelude::normalize_cross`] (`num · 2 = 2 · den_z`) by
/// [`RatPrelude::int_mul_right_cancel`] (cancelling the shared `2`).
///
/// Returns `(two_r, half_r, proof : Eq Rat (Rat.mul two_r half_r) Rat.one)`.
/// `Rat.normalize (Int.ofNat k) k h_k = Rat.one`, for any concrete `k` with
/// `h_k : 1 ≤ k` — the reusable engine [`rat_two_mul_half_eq_one`] and
/// [`rat_half_add_half_eq_one`] both instantiate (`k := 2`, `k := 4`).
///
/// By cross-multiplication: `Rat.one` is a **direct** `Rat.mk` (not itself
/// built through `normalize` — `rat_prelude/defs.rs::declare_constants` —
/// so `num`/`den` project off it by ι alone, unlike the `Nat.gcd`-bound
/// projections off `Rat.normalize k k h_k`), and the cross condition reduces
/// to `num (normalize k k h_k) = den_z (normalize k k h_k)`, itself gotten
/// from [`RatPrelude::normalize_cross`] (`num · k = k · den_z`) by
/// [`RatPrelude::int_mul_right_cancel`] (cancelling the shared `k`).
fn rat_normalize_self_eq_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k_nat: ExprId,
    h_k: ExprId,
) -> ExprId {
    let rp = p.rat;
    let np = d.prelude();
    let one_nat = d.num(1);
    let k_z = d.of_nat(k_nat);
    let value = normalize(d, k_z, k_nat, h_k);

    let n = num(d, value);
    let dd = den(d, value);
    let dz = den_z(d, value);
    let cross = d.lemma(rp.normalize_cross, &[k_z, k_nat, h_k]);
    let comm = d.lemma(rp.int.mul_comm, &[k_z, dz]);
    let lhs0 = d.imul(n, k_z);
    let mid0 = d.imul(k_z, dz);
    let rhs0 = d.imul(dz, k_z);
    let (_, cr2) = d.ichain(lhs0, &[(mid0, cross), (rhs0, comm)]);
    // cr2 : n*k_z = dz*k_z
    let nd_eq = d.lemma(rp.int_mul_right_cancel, &[n, dz, k_nat, h_k, cr2]);
    // nd_eq : Eq Int n dz

    let one_z = d.of_nat(one_nat);
    let one = rone(d, rp);
    let lhs_goal = d.imul(n, one_z);
    let lhs_mid = d.imul(dz, one_z);
    let lhs_congr = d.icongr(n, dz, nd_eq, &|d, t| d.imul(t, one_z));
    let mul_one_dd = d.lemma(np.mul_one, &[dd]);
    let dd_one = NatOps::mul(d, dd, one_nat);
    let mul_one_dd_int = d.nat_eq_to_int(dd_one, dd, mul_one_dd, &|d, t| d.of_nat(t));
    let (_, lhs_final) = d.ichain(lhs_goal, &[(lhs_mid, lhs_congr), (dz, mul_one_dd_int)]);
    // lhs_final : n*one_z = dz

    let rhs_goal = d.imul(one_z, dz);
    let one_mul_dd = d.lemma(np.one_mul, &[dd]);
    let one_dd = NatOps::mul(d, one_nat, dd);
    let one_mul_dd_int = d.nat_eq_to_int(one_dd, dd, one_mul_dd, &|d, t| d.of_nat(t));
    let dz_eq_rhs = d.isymm(rhs_goal, dz, one_mul_dd_int);
    // dz_eq_rhs : dz = one_z*dz

    let (_, full_cross) = d.ichain(lhs_goal, &[(dz, lhs_final), (rhs_goal, dz_eq_rhs)]);
    // full_cross : n*one_z = one_z*dz
    //            = num(value)*ofNat(den(one)) = num(one)*ofNat(den(value))
    //   (up to defeq: den(one) ≡ one_nat, num(one) ≡ one_z, both by ι on
    //   `Rat.one`'s own `mk` projections).
    d.lemma(rp.eq_of_cross, &[value, one, full_cross])
}

/// `Rat.mul (Rat.normalize 2 1 h_a) (Rat.normalize 1 2 h_b) = Rat.one`, i.e.
/// `2 · (1/2) = 1`.
///
/// **This does NOT hold by `Eq.refl`** — confirmed empirically (a throwaway
/// probe declaration built exactly this claim via `rrefl` and the kernel
/// rejected it with `TypeMismatch`): `Rat.normalize`'s reduction to lowest
/// terms goes through `Nat.gcd`, which (unlike `Nat.pow`/`Nat.mul`/`Nat.add`
/// on LITERAL arguments) does not unfold via ι alone, even for concrete
/// inputs. So `Rat.normalize (Int.ofNat 2) 2 h` is not *definitionally*
/// `Rat.one`, and closing this needs an actual argument.
///
/// Route: [`RatPrelude::normalize_mul_normalize`] turns the product into
/// `Rat.normalize (Int.mul 2 1) (Nat.mul 1 2) h_c` — both `Int.mul 2 1` and
/// `Nat.mul 1 2` are LITERAL-LITERAL and reduce by ι alone (no symbolic
/// operand, so the "symbolic side" trap does not apply), landing on
/// `Rat.normalize 2 2 h_c`; [`rat_normalize_self_eq_one`] closes the rest.
///
/// Returns `(two_r, half_r, proof : Eq Rat (Rat.mul two_r half_r) Rat.one)`.
fn rat_two_mul_half_eq_one(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId, ExprId) {
    let rp = p.rat;
    let np = d.prelude();

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let two_z = d.of_nat(two_nat);
    let one_z = d.of_nat(one_nat);

    let h_a = d.lemma(np.le_refl, &[one_nat]); // 1 ≤ 1
    let two_r = normalize(d, two_z, one_nat, h_a);
    let h_b = d.lemma(np.le_succ, &[one_nat]); // 1 ≤ 2
    let half_r = normalize(d, one_z, two_nat, h_b);

    let step_mul_norm = d.lemma(
        rp.normalize_mul_normalize,
        &[two_z, one_nat, h_a, one_z, two_nat, h_b],
    );
    // step_mul_norm : Eq (mul two_r half_r) (normalize (Int.mul two_z one_z)
    // (Nat.mul one_nat two_nat) _) -- both LITERAL-LITERAL, ι-reduce to
    // `two_z`/`two_nat`, so this is already, up to defeq, `Eq (mul two_r
    // half_r) (normalize two_z two_nat h_c)` for any witness `h_c`.
    let h_c = d.lemma(np.le_succ, &[one_nat]); // 1 ≤ 2, a fresh witness
    let value = normalize(d, two_z, two_nat, h_c);
    let value_eq_one = rat_normalize_self_eq_one(d, p, two_nat, h_c);

    let one = rone(d, rp);
    let mul_two_half = rmul(d, two_r, half_r);
    let (_, proof) = rchain(
        d,
        mul_two_half,
        &[(value, step_mul_norm), (one, value_eq_one)],
    );
    (two_r, half_r, proof)
}

/// `Rat.add half_r half_r = Rat.one`, i.e. `1/2 + 1/2 = 1` — the same
/// engine as [`rat_two_mul_half_eq_one`], via
/// [`RatPrelude::normalize_add_normalize`] in place of `_mul_normalize`,
/// landing on `Rat.normalize 4 4 _` instead of `2 2`.
///
/// Returns `(half_r, proof : Eq Rat (Rat.add half_r half_r) Rat.one)`.
fn rat_half_add_half_eq_one(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId) {
    let rp = p.rat;
    let np = d.prelude();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let one_z = d.of_nat(one_nat);
    let h_b = d.lemma(np.le_succ, &[one_nat]); // 1 ≤ 2
    let half_r = normalize(d, one_z, two_nat, h_b);

    let step_add_norm = d.lemma(
        rp.normalize_add_normalize,
        &[one_z, two_nat, h_b, one_z, two_nat, h_b],
    );
    // step_add_norm : Eq (add half_r half_r) (normalize
    //   (Int.mul one_z (ofNat two_nat) + Int.mul one_z (ofNat two_nat))
    //   (Nat.mul two_nat two_nat) h_d)
    // numerator: 1*2+1*2 (LITERAL-LITERAL throughout) ι-reduces to 4;
    // denominator: 2*2 ι-reduces to 4. So this is already, up to defeq,
    // `Eq (add half_r half_r) (normalize 4 4 h_d)` for any witness `h_d`.
    let four_nat = d.num(4);
    let four_z = d.of_nat(four_nat);
    // `1 ≤ 4`, via `1 ≤ 2 ≤ 3 ≤ 4` (chained `le_succ`/`le_trans`).
    let two_nat2 = d.num(2);
    let three_nat = d.num(3);
    let s1 = d.lemma(np.le_succ, &[two_nat2]); // 2 ≤ 3
    let s2 = d.lemma(np.le_succ, &[three_nat]); // 3 ≤ 4
    let two_le_four = d.lemma(np.le_trans, &[two_nat2, three_nat, four_nat, s1, s2]);
    let h_d = d.lemma(np.le_trans, &[one_nat, two_nat, four_nat, h_b, two_le_four]);
    let value = normalize(d, four_z, four_nat, h_d);
    let value_eq_one = rat_normalize_self_eq_one(d, p, four_nat, h_d);

    let one = rone(d, rp);
    let add_hh = radd(d, half_r, half_r);
    let (_, proof) = rchain(d, add_hh, &[(value, step_add_norm), (one, value_eq_one)]);
    (half_r, proof)
}

/// `CReal.add x y`.
fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

/// `Equiv` chain composition, verbatim in shape to every other `creal/*`
/// module's own private `echain` (see e.g. `geometric.rs::echain`).
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

/// `Equiv (add x (neg x)) zero` reproduced at `x := half`, chained through
/// `add_comm` so it applies to `add (neg half) half` (the order `add_neg`
/// itself does not cover).
fn neg_half_add_half_equiv_zero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let h = half(d, p);
    let neg_h = cneg(d, p, h);
    let comm = d.lemma(p.add_comm, &[neg_h, h]); // Equiv (add neg_h h) (add h neg_h)
    let an = d.lemma(p.add_neg, &[h]); // Equiv (add h neg_h) zero
    let start = cadd(d, p, neg_h, h);
    let mid = cadd(d, p, h, neg_h);
    let zero = czero(d, p);
    echain(d, p, start, &[(mid, comm), (zero, an)])
}

/// `Equiv (add one (neg half)) half` — from the group tautology
/// `Equiv (add (add one (neg half)) half) one` (true for *any* constant in
/// place of `half`, via `add_assoc`/`add_neg`/`add_zero`) combined with
/// `Equiv (add half half) one` ([`rat_half_add_half_eq_one`] lifted through
/// `CReal.ofRat_add`), then cancelling the shared `half` on the right by
/// adding `neg half` to both sides.
fn one_sub_half_equiv_half(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let one_c = d.kernel().const_(p.one, vec![]);
    let h = half(d, p);
    let neg_h = cneg(d, p, h);
    let a = cadd(d, p, one_c, neg_h); // a := 1 - half
    let zero = czero(d, p);
    let nh_h = cadd(d, p, neg_h, h);
    let hh = cadd(d, p, h, h);
    let a_h = cadd(d, p, a, h);

    // g_taut : Equiv (add a half) one.
    let g_taut = {
        let assoc = d.lemma(p.add_assoc, &[one_c, neg_h, h]);
        // Equiv (add (add one neg_h) h) (add one (add neg_h h))
        let nh_h_zero = neg_half_add_half_equiv_zero(d, p);
        let refl_one = d.lemma(p.equiv_refl, &[one_c]);
        let congr1 = d.lemma(
            p.add_congr,
            &[one_c, one_c, nh_h, zero, refl_one, nh_h_zero],
        );
        // Equiv (add one (add neg_h h)) (add one zero)
        let az = d.lemma(p.add_zero, &[one_c]); // Equiv (add one zero) one
        let mid1 = cadd(d, p, one_c, nh_h);
        let mid2 = cadd(d, p, one_c, zero);
        echain(d, p, a_h, &[(mid1, assoc), (mid2, congr1), (one_c, az)])
    };

    // g_new : Equiv (add half half) one.
    let g_new = {
        let (half_r, rat_eq) = rat_half_add_half_eq_one(d, p);
        let add_proof = d.lemma(p.of_rat_add, &[half_r, half_r]);
        let add_hh_r = radd(d, half_r, half_r);
        let one_r = rone(d, p.rat);
        let ofrat_eq = ofrat_congr(d, p, add_hh_r, one_r, rat_eq);
        let mid = embed(d, p, add_hh_r);
        echain(d, p, hh, &[(mid, add_proof), (one_c, ofrat_eq)])
    };

    // Equiv (add a half) (add half half), then cancel `half` on the right.
    let g_new_rev = d.lemma(p.equiv_symm, &[hh, one_c, g_new]);
    let m = echain(d, p, a_h, &[(one_c, g_taut), (hh, g_new_rev)]);
    // m : Equiv (add a half) (add half half)

    let refl_neg_h = d.lemma(p.equiv_refl, &[neg_h]);
    let a_h_nh = cadd(d, p, a_h, neg_h);
    let hh_nh = cadd(d, p, hh, neg_h);
    let m2 = d.lemma(p.add_congr, &[a_h, hh, neg_h, neg_h, m, refl_neg_h]);
    // m2 : Equiv (add (add a half) neg_h) (add (add half half) neg_h)

    let h_nh = cadd(d, p, h, neg_h);
    let lhs_to_a = {
        let assoc = d.lemma(p.add_assoc, &[a, h, neg_h]);
        // Equiv (add (add a h) neg_h) (add a (add h neg_h))
        let hn_zero = d.lemma(p.add_neg, &[h]); // Equiv (add h neg_h) zero
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        let congr = d.lemma(p.add_congr, &[a, a, h_nh, zero, refl_a, hn_zero]);
        let az = d.lemma(p.add_zero, &[a]);
        let mid1 = cadd(d, p, a, h_nh);
        let mid2 = cadd(d, p, a, zero);
        echain(d, p, a_h_nh, &[(mid1, assoc), (mid2, congr), (a, az)])
    };
    let rhs_to_half = {
        let assoc = d.lemma(p.add_assoc, &[h, h, neg_h]);
        let hn_zero = d.lemma(p.add_neg, &[h]);
        let refl_h = d.lemma(p.equiv_refl, &[h]);
        let congr = d.lemma(p.add_congr, &[h, h, h_nh, zero, refl_h, hn_zero]);
        let az = d.lemma(p.add_zero, &[h]);
        let mid1 = cadd(d, p, h, h_nh);
        let mid2 = cadd(d, p, h, zero);
        echain(d, p, hh_nh, &[(mid1, assoc), (mid2, congr), (h, az)])
    };

    let lhs_to_a_rev = d.lemma(p.equiv_symm, &[a, a_h_nh, lhs_to_a]);
    echain(
        d,
        p,
        a,
        &[(a_h_nh, lhs_to_a_rev), (hh_nh, m2), (h, rhs_to_half)],
    )
}

/// `Equiv (mul two (add one (neg half))) one`, i.e. `2 · (1 − 1/2) = 1` — the
/// cancellation [`declare_exp_term_le_geom`]'s module documentation named as
/// missing to extract `sumRange (pow half)` from
/// [`CRealPrelude::mul_sub_one_geom`]'s multiplied-through form, closed
/// **without ever touching `CReal.inv`/`CRealPrelude::pos_bound`**: via
/// [`one_sub_half_equiv_half`] (`1 − half ≈ half`) and
/// [`rat_two_mul_half_eq_one`] (`2 · half = 1`, lifted through
/// `CReal.ofRat_mul`).
fn two_mul_one_sub_half_equiv_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let t = two(d, p);
    let h = half(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let neg_h = cneg(d, p, h);
    let a = cadd(d, p, one_c, neg_h);

    let a_equiv_half = one_sub_half_equiv_half(d, p);
    let refl_two = d.lemma(p.equiv_refl, &[t]);
    let step1 = d.lemma(p.mul_congr, &[t, t, a, h, refl_two, a_equiv_half]);
    // step1 : Equiv (mul two a) (mul two half)

    let (two_r, half_r, rat_eq) = rat_two_mul_half_eq_one(d, p);
    let mul_proof = d.lemma(p.of_rat_mul, &[two_r, half_r]);
    let mul_r = rmul(d, two_r, half_r);
    let one_r = rone(d, p.rat);
    let ofrat_eq = ofrat_congr(d, p, mul_r, one_r, rat_eq);
    let mul_two_half = cmul(d, p, t, h);
    let embed_mul_r = embed(d, p, mul_r);
    let step2 = echain(
        d,
        p,
        mul_two_half,
        &[(embed_mul_r, mul_proof), (one_c, ofrat_eq)],
    );
    // step2 : Equiv (mul two half) one

    let mul_two_a = cmul(d, p, t, a);
    echain(d, p, mul_two_a, &[(mul_two_half, step1), (one_c, step2)])
}

/// `λ i, CReal.pow half i` — verbatim in shape to `geometric.rs::pow_fn`.
fn pow_half_fn(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let h = half(d, p);
    let body = cpow(d, p, h, i);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `CReal.sumRange_pow_half_closed_form : ∀ n, Equiv (sumRange (fun i => pow
/// half i) n) (mul two (add one (neg (pow half n))))` — the closed form of
/// the base-`1/2` geometric partial sum, `Σ_{k<n} (1/2)ᵏ = 2·(1 − (1/2)ⁿ)`,
/// derived **without** `CReal.inv`/`CRealPrelude::pos_bound`/
/// `geometric.rs::geom_pair_within`: multiply
/// [`CRealPrelude::mul_sub_one_geom`]'s conclusion through by `two` and
/// cancel `mul two (add one (neg half))` down to `one` via
/// [`two_mul_one_sub_half_equiv_one`].
fn declare_sum_pow_half_closed_form(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let f = pow_half_fn(d, p);
    let sum_n = d.const_app(p.sum_range, &[f, n]);
    let h = half(d, p);
    let pow_h_n = cpow(d, p, h, n);
    let one_c = d.kernel().const_(p.one, vec![]);
    let neg_pow = cneg(d, p, pow_h_n);
    let y_n = cadd(d, p, one_c, neg_pow);
    let t = two(d, p);

    // Step g1 : Equiv (mul a sum_n) y_n, a := add one (neg half).
    let g1 = d.lemma(p.mul_sub_one_geom, &[h, n]);
    let neg_h = cneg(d, p, h);
    let a = cadd(d, p, one_c, neg_h);

    // Step 2/3/4: Equiv (mul (mul two a) sum_n) (mul two y_n).
    let refl_two = d.lemma(p.equiv_refl, &[t]);
    let mul_a_sum = cmul(d, p, a, sum_n);
    let mul_two_y = cmul(d, p, t, y_n);
    let step2 = d.lemma(p.mul_congr, &[t, t, mul_a_sum, y_n, refl_two, g1]);
    // step2 : Equiv (mul two (mul a sum_n)) (mul two y_n)
    let assoc = d.lemma(p.mul_assoc, &[t, a, sum_n]);
    // assoc : Equiv (mul (mul two a) sum_n) (mul two (mul a sum_n))
    let mul_two_a = cmul(d, p, t, a);
    let mul_two_mul_a_sum = cmul(d, p, t, mul_a_sum);
    let mul_two_a_sum = cmul(d, p, mul_two_a, sum_n);
    let step4 = echain(
        d,
        p,
        mul_two_a_sum,
        &[(mul_two_mul_a_sum, assoc), (mul_two_y, step2)],
    );
    // step4 : Equiv (mul (mul two a) sum_n) (mul two y_n)

    // Step 5/6: Equiv (mul (mul two a) sum_n) (mul one sum_n).
    let two_a_one = two_mul_one_sub_half_equiv_one(d, p);
    let refl_sum = d.lemma(p.equiv_refl, &[sum_n]);
    let mul_one_sum = cmul(d, p, one_c, sum_n);
    let step6 = d.lemma(
        p.mul_congr,
        &[mul_two_a, one_c, sum_n, sum_n, two_a_one, refl_sum],
    );
    // step6 : Equiv (mul (mul two a) sum_n) (mul one sum_n)

    // Step 7: Equiv (mul one sum_n) sum_n.
    let comm = d.lemma(p.mul_comm, &[one_c, sum_n]);
    let mul_sum_one = cmul(d, p, sum_n, one_c);
    let mo = d.lemma(p.mul_one, &[sum_n]);
    let step7 = echain(d, p, mul_one_sum, &[(mul_sum_one, comm), (sum_n, mo)]);

    // Combine: sum_n ~ (mul (mul two a) sum_n) ~ (mul two y_n).
    let step6_7 = echain(d, p, mul_two_a_sum, &[(mul_one_sum, step6), (sum_n, step7)]);
    // step6_7 : Equiv (mul (mul two a) sum_n) sum_n
    let step6_7_rev = d.lemma(p.equiv_symm, &[mul_two_a_sum, sum_n, step6_7]);
    // sum_n ~ mul_two_a_sum ~ mul_two_y. `step4` already runs
    // `mul_two_a_sum -> mul_two_y` (the direction `echain` needs for a
    // `current -> next` link) -- an earlier version of this chain fed
    // `equiv_symm` a THIRD time here, building `Equiv mul_two_y
    // mul_two_a_sum` (the wrong direction) and feeding that into the
    // `(mul_two_y, _)` slot, which needs `mul_two_a_sum -> mul_two_y`. That
    // was the whole `TypeMismatch`: the swapped proof against the
    // straight-through step `equiv_trans` expects.
    let concl = echain(
        d,
        p,
        sum_n,
        &[(mul_two_a_sum, step6_7_rev), (mul_two_y, step4)],
    );

    let value = d.lam_fv(n_fv, nat, concl);
    let ty = {
        let stmt = equiv(d, p, sum_n, mul_two_y);
        d.pi_fv(n_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_pow_half_closed_form,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.geom_cauchy` family -------------------------------------------
//
// See this file's own module documentation ("A genuinely new fact changes
// that module's own diagnosis") for the overall plan. This section builds
// it: [`declare_geom_half_inv_leaf_bound`] first (the one `CReal.inv`-using
// piece, self-contained), then [`declare_geom_cauchy_ordered_half`] (the
// index-bookkeeping normalization on top of it), then
// [`declare_geom_cauchy`] (the `Nat.le_total` assembly into `CReal.Cauchy`
// itself).

/// `CReal.inv x k h`.
fn cinv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId, h: ExprId) -> ExprId {
    d.const_app(p.inv, &[x, k, h])
}

/// `Rat.natDivSucc 2 0` — the rational `2`, kept in the `natDivSucc` shape
/// [`RatPrelude::nat_div_succ_mul`]'s first-factor slot expects, rather than
/// the `Rat.normalize`-based shape [`two`]/[`two_normalize`] above build (a
/// shape used nowhere in this derivation).
fn two_ds(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_nat = d.num(0);
    div_succ(d, p, 2, zero_nat)
}

/// `CReal.ofRat (Rat.natDivSucc 2 0)` — the constant `2`, in the shape
/// [`two_ds`] builds.
fn two_c(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let t = two_ds(d, p);
    embed(d, p, t)
}

/// `Eq Rat (mul (natDivSucc 2 0) (natDivSucc 1 1)) Rat.one`, i.e. `2 · 1/2 =
/// 1` — via `natDivSucc`'s own algebraic interface
/// (`Rat.natDivSucc_mul`/`Rat.natDivSucc_scale`/`CReal.ratUnitEqOne`), never
/// by unfolding `Rat.normalize`'s `Nat.gcd` (which does not reduce by ι even
/// on literals — see [`rat_two_mul_half_eq_one`]'s own doc for the
/// `Rat.normalize`-based route this avoids).
///
/// `Rat.natDivSucc_mul(2,1,1) : mul (natDivSucc 2 0) (natDivSucc 1 1) =
/// natDivSucc (2*1) 1`, `2*1` a literal-literal `Nat.mul` that ι-reduces to
/// `2`; `Rat.natDivSucc_scale(1,0) : natDivSucc 2 ((1+1)*0+1) = natDivSucc 1
/// 0`, `(1+1)*0+1` likewise literal-literal, reducing to `1`; and
/// `CReal.ratUnitEqOne : natDivSucc 1 0 = Rat.one` closes it.
fn two_ds_mul_half_rat_eq_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let zero_nat = d.num(0);
    let mul_eq = d.lemma(rat.nat_div_succ_mul, &[two_nat, one_nat, one_nat]);
    let scale_eq = d.lemma(rat.nat_div_succ_scale, &[one_nat, zero_nat]);
    let unit_eq = d.lemma(p.rat_unit_eq_one, &[]);
    let td = two_ds(d, p);
    let hr = half_rat(d, p);
    let mul_expr = rmul(d, td, hr);
    let two_one = div_succ(d, p, 2, one_nat);
    let one_zero = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_r = rone(d, rat);
    let (_, proof) = rchain(
        d,
        mul_expr,
        &[(two_one, mul_eq), (one_zero, scale_eq), (one_r, unit_eq)],
    );
    proof
}

/// `CReal.geomHalfInvLeafBound`. See the field documentation
/// ([`CRealPrelude::geom_half_inv_leaf_bound`]) for the statement and the
/// derivation.
fn declare_geom_half_inv_leaf_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let one_c = d.kernel().const_(p.one, vec![]);
    let h = half(d, p);
    let neg_h = cneg(d, p, h);
    let a_real = cadd(d, p, one_c, neg_h); // a_real = 1 - half

    // `PosBound half 1`: `half` IS `ofRat (natDivSucc 1 1)` by construction
    // (`half`/`half_rat` above), so this is `le_refl` at that shared term.
    let hp_half = d.lemma(p.le_refl, &[h]);

    // `PosBound a_real 1`, transported from `hp_half` across `Equiv half
    // a_real` (`one_sub_half_equiv_half`, reversed).
    let eq_a_half = one_sub_half_equiv_half(d, p); // Equiv a_real half
    let eq_half_a = d.lemma(p.equiv_symm, &[a_real, h, eq_a_half]); // Equiv half a_real
    let refl_half = d.lemma(p.equiv_refl, &[h]);
    let h_pos_a_real = d.lemma(
        p.le_congr,
        &[h, h, h, a_real, refl_half, eq_half_a, hp_half],
    ); // le half a_real == PosBound a_real 1 (unfolded)

    let inv_expr = cinv(d, p, a_real, one_nat, h_pos_a_real);

    // `Equiv (mul half inv_expr) one`, transported from `mul_inv_cancel` at
    // `a_real` across `Equiv a_real half`.
    let cancel_a_real = d.lemma(p.mul_inv_cancel, &[a_real, one_nat, h_pos_a_real]);
    // cancel_a_real : Equiv (mul a_real inv_expr) one
    let refl_inv = d.lemma(p.equiv_refl, &[inv_expr]);
    let mul_a_real_inv = cmul(d, p, a_real, inv_expr);
    let mul_half_inv = cmul(d, p, h, inv_expr);
    let mul_congr_half = d.lemma(
        p.mul_congr,
        &[a_real, h, inv_expr, inv_expr, eq_a_half, refl_inv],
    );
    // mul_congr_half : Equiv mul_a_real_inv mul_half_inv
    let mul_congr_half_rev = d.lemma(
        p.equiv_symm,
        &[mul_a_real_inv, mul_half_inv, mul_congr_half],
    );
    // mul_congr_half_rev : Equiv mul_half_inv mul_a_real_inv
    let half_inv_one = d.lemma(
        p.equiv_trans,
        &[
            mul_half_inv,
            mul_a_real_inv,
            one_c,
            mul_congr_half_rev,
            cancel_a_real,
        ],
    );
    // half_inv_one : Equiv mul_half_inv one_c

    // `Equiv (mul half two_c) one`, a pure `Rat`-level computation lifted
    // through `of_rat_mul`.
    let tc = two_c(d, p);
    let td = two_ds(d, p);
    let hr = half_rat(d, p);
    let two_half_eq = two_ds_mul_half_rat_eq_one(d, p); // Eq (mul td hr) one_r
    let mul_tc_half = cmul(d, p, tc, h);
    let mul_half_tc = cmul(d, p, h, tc);
    let rmul_td_hr = rmul(d, td, hr);
    let embed_mul_td_hr = embed(d, p, rmul_td_hr);
    let of_rat_mul_two_half = d.lemma(p.of_rat_mul, &[td, hr]);
    // of_rat_mul_two_half : Equiv mul_tc_half embed_mul_td_hr
    let one_r_here = rone(d, rat);
    let ofrat_two_half_eq = ofrat_congr(d, p, rmul_td_hr, one_r_here, two_half_eq);
    // ofrat_two_half_eq : Equiv embed_mul_td_hr one_c (defeq to `ofRat one_r`)
    let two_half_one = d.lemma(
        p.equiv_trans,
        &[
            mul_tc_half,
            embed_mul_td_hr,
            one_c,
            of_rat_mul_two_half,
            ofrat_two_half_eq,
        ],
    );
    // two_half_one : Equiv mul_tc_half one_c
    let comm_two_half = d.lemma(p.mul_comm, &[tc, h]);
    // comm_two_half : Equiv mul_tc_half mul_half_tc
    let comm_two_half_rev = d.lemma(p.equiv_symm, &[mul_tc_half, mul_half_tc, comm_two_half]);
    // comm_two_half_rev : Equiv mul_half_tc mul_tc_half
    let half_two_one = d.lemma(
        p.equiv_trans,
        &[
            mul_half_tc,
            mul_tc_half,
            one_c,
            comm_two_half_rev,
            two_half_one,
        ],
    );
    // half_two_one : Equiv mul_half_tc one_c

    // Cancel `half` from `Equiv mul_half_inv mul_half_tc` (both ~ `one_c`)
    // via `le_of_mul_le_mul_left` in both directions.
    let half_two_one_rev = d.lemma(p.equiv_symm, &[mul_half_tc, one_c, half_two_one]);
    // half_two_one_rev : Equiv one_c mul_half_tc
    let both_one = d.lemma(
        p.equiv_trans,
        &[
            mul_half_inv,
            one_c,
            mul_half_tc,
            half_inv_one,
            half_two_one_rev,
        ],
    );
    // both_one : Equiv mul_half_inv mul_half_tc
    let both_one_rev = d.lemma(p.equiv_symm, &[mul_half_inv, mul_half_tc, both_one]);
    let le1 = d.lemma(p.le_of_equiv, &[mul_half_inv, mul_half_tc, both_one]);
    let le2 = d.lemma(p.le_of_equiv, &[mul_half_tc, mul_half_inv, both_one_rev]);
    let cancel1 = d.lemma(
        p.le_of_mul_le_mul_left,
        &[h, inv_expr, tc, one_nat, hp_half, le1],
    ); // le inv_expr tc
    let cancel2 = d.lemma(
        p.le_of_mul_le_mul_left,
        &[h, tc, inv_expr, one_nat, hp_half, le2],
    ); // le tc inv_expr
    let inv_equiv_two = d.lemma(p.equiv_of_le_le, &[inv_expr, tc, cancel1, cancel2]);
    // inv_equiv_two : Equiv inv_expr tc

    // `y_a := mul inv_expr (pow half a) ~ mul tc (pow half a)`, then bound
    // the right side via `pow_half_le_nat_div_succ` scaled by `tc`.
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let pow_half_a = cpow(d, p, h, a);
    let refl_pow = d.lemma(p.equiv_refl, &[pow_half_a]);
    let y_a = cmul(d, p, inv_expr, pow_half_a);
    let two_pow = cmul(d, p, tc, pow_half_a);
    let y_a_equiv = d.lemma(
        p.mul_congr,
        &[
            inv_expr,
            tc,
            pow_half_a,
            pow_half_a,
            inv_equiv_two,
            refl_pow,
        ],
    );
    // y_a_equiv : Equiv y_a two_pow

    let bound_rat_1a = div_succ(d, p, 1, a);
    let pow_le = d.lemma(p.pow_half_le_nat_div_succ, &[a]);
    // pow_le : le pow_half_a (ofRat bound_rat_1a)
    let zero_nat = d.num(0);
    let zero_le_td = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, zero_nat]);
    let rzero_here = rzero(d, rat);
    let zero_le_tc = d.lemma(p.of_rat_le, &[rzero_here, td, zero_le_td]);
    let embed_bound_1a = embed(d, p, bound_rat_1a);
    let mul_le = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[tc, pow_half_a, embed_bound_1a, zero_le_tc, pow_le],
    );
    // mul_le : le two_pow (mul tc embed_bound_1a)

    let bound_a_rat = div_succ(d, p, 2, a);
    let bound_a = embed(d, p, bound_a_rat);
    let mul_eq2 = d.lemma(rat.nat_div_succ_mul, &[two_nat, one_nat, a]);
    // mul_eq2 : Eq (mul td bound_rat_1a) (natDivSucc (2*1) a) ~ bound_a_rat
    let mul_tc_bound1a = cmul(d, p, tc, embed_bound_1a);
    let rmul_td_1a = rmul(d, td, bound_rat_1a);
    let embed_mul_td_1a = embed(d, p, rmul_td_1a);
    let of_rat_mul_two_bound = d.lemma(p.of_rat_mul, &[td, bound_rat_1a]);
    // of_rat_mul_two_bound : Equiv mul_tc_bound1a embed_mul_td_1a
    let ofrat_bound_eq = ofrat_congr(d, p, rmul_td_1a, bound_a_rat, mul_eq2);
    // ofrat_bound_eq : Equiv embed_mul_td_1a bound_a
    let rhs_equiv = d.lemma(
        p.equiv_trans,
        &[
            mul_tc_bound1a,
            embed_mul_td_1a,
            bound_a,
            of_rat_mul_two_bound,
            ofrat_bound_eq,
        ],
    );
    // rhs_equiv : Equiv mul_tc_bound1a bound_a
    let refl_two_pow = d.lemma(p.equiv_refl, &[two_pow]);
    let two_pow_le_bound = d.lemma(
        p.le_congr,
        &[
            two_pow,
            two_pow,
            mul_tc_bound1a,
            bound_a,
            refl_two_pow,
            rhs_equiv,
            mul_le,
        ],
    );
    // two_pow_le_bound : le two_pow bound_a

    let y_a_equiv_rev = d.lemma(p.equiv_symm, &[y_a, two_pow, y_a_equiv]);
    let refl_bound_a = d.lemma(p.equiv_refl, &[bound_a]);
    let hv = d.lemma(
        p.le_congr,
        &[
            two_pow,
            y_a,
            bound_a,
            bound_a,
            y_a_equiv_rev,
            refl_bound_a,
            two_pow_le_bound,
        ],
    );
    // hv : le y_a bound_a

    let value = d.lam_fv(a_fv, nat, hv);
    let ty = {
        let stmt = cle(d, p, y_a, bound_a);
        d.pi_fv(a_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_half_inv_leaf_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// Rebuild `a_real := add one (neg half)` and `h_pos_a_real : PosBound
/// a_real 1`, the same recipe [`declare_geom_half_inv_leaf_bound`] uses
/// internally. Every call here is a plain constant application at fixed
/// arguments — no fresh free variable is minted — so this reconstruction is
/// deterministic and lands on the identical term
/// [`CRealPrelude::geom_half_inv_leaf_bound`]'s own stored type mentions,
/// letting a call to that theorem plug directly into an expression built
/// from this pair with no extra `Equiv`/`Eq` bridge.
fn geom_half_a_real_pos_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId) {
    let one_nat = d.num(1);
    let one_c = d.kernel().const_(p.one, vec![]);
    let h = half(d, p);
    let neg_h = cneg(d, p, h);
    let a_real = cadd(d, p, one_c, neg_h);
    let hp_half = d.lemma(p.le_refl, &[h]);
    let eq_a_half = one_sub_half_equiv_half(d, p);
    let eq_half_a = d.lemma(p.equiv_symm, &[a_real, h, eq_a_half]);
    let refl_half = d.lemma(p.equiv_refl, &[h]);
    let h_pos_a_real = d.lemma(
        p.le_congr,
        &[h, h, h, a_real, refl_half, eq_half_a, hp_half],
    );
    let _ = one_nat;
    (a_real, h_pos_a_real)
}

/// `CReal.geomCauchyOrderedHalf`. See the field documentation
/// ([`CRealPrelude::geom_cauchy_ordered_half`]) for the statement and the
/// derivation.
#[allow(clippy::too_many_lines)]
fn declare_geom_cauchy_ordered_half(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let h = half(d, p);
    let (a_real, h_pos_a_real) = geom_half_a_real_pos_bound(d, p);

    let half_rat_term = half_rat(d, p);
    let half_le_zero = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, one_nat]);
    let rzero_here = rzero(d, rat);
    let h0 = d.lemma(p.of_rat_le, &[rzero_here, half_rat_term, half_le_zero]);

    let f = pow_half_fn(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hle_ty = d.le(a, b);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let raw = d.lemma(
        p.geom_pair_within,
        &[h, h0, one_nat, h_pos_a_real, a, b, hle],
    );

    // Reconstruct `diff`/`total` exactly as `geom_pair_within`'s own body
    // builds them, so `weaken` below sees the SAME `bound` its `proof`
    // argument (`raw`) actually carries.
    let sum_f_b = d.const_app(p.sum_range, &[f, b]);
    let sum_f_a = d.const_app(p.sum_range, &[f, a]);
    let y_pt = sample(d, p, sum_f_b, b);
    let z_pt = sample(d, p, sum_f_a, a);
    let diff = rsub(d, rat, y_pt, z_pt);

    let t = shift(d, b);
    let t1 = div_succ(d, p, 1, t);
    let b1 = div_succ(d, p, 1, b);
    let a1 = div_succ(d, p, 1, a);
    let pow_half_a = cpow(d, p, h, a);
    let inv_expr = cinv(d, p, a_real, one_nat, h_pos_a_real);
    let y_a = cmul(d, p, inv_expr, pow_half_a);
    let v = sample(d, p, y_a, b);
    let b2 = div_succ(d, p, 2, b);

    let bxy = radd(d, t1, b1);
    let byz = radd(d, v, b2);
    let bzw = radd(d, a1, t1);
    let bxy_byz = radd(d, bxy, byz);
    let total = radd(d, bxy_byz, bzw);

    // --- widen: `t1 -> b1` (twice) and `v -> v_bound` -------------------
    let wt = d.lemma(rat.nat_div_succ_le_scaled, &[one_nat, one_nat, b]);
    // wt : le t1 b1

    let hv_at_a = d.lemma(p.geom_half_inv_leaf_bound, &[a]);
    // hv_at_a : le y_a (ofRat (natDivSucc 2 a))
    let raw_v = d.apply(hv_at_a, &[b]);
    // raw_v : (defeq) Rat.le (Rat.sub v a2) b2
    let a2 = div_succ(d, p, 2, a);
    let y_leaf_le = d.lemma(rat.le_of_sub_le, &[v, a2, b2, raw_v]);
    // y_leaf_le : le v (radd a2 b2) = le v vb
    let vb = radd(d, a2, b2);

    let bxy_w = radd(d, b1, b1);
    let byz_w = radd(d, vb, b2);
    let bzw_w = radd(d, a1, b1);

    let refl_b1 = d.lemma(rat.le_refl, &[b1]);
    let refl_a1 = d.lemma(rat.le_refl, &[a1]);
    let refl_b2 = d.lemma(rat.le_refl, &[b2]);

    let step1 = d.lemma(rat.add_le_add, &[t1, b1, b1, b1, wt, refl_b1]);
    // step1 : le bxy bxy_w
    let step2 = d.lemma(rat.add_le_add, &[v, vb, b2, b2, y_leaf_le, refl_b2]);
    // step2 : le byz byz_w
    let step3 = d.lemma(rat.add_le_add, &[bxy, bxy_w, byz, byz_w, step1, step2]);
    // step3 : le bxy_byz (radd bxy_w byz_w)
    let step4 = d.lemma(rat.add_le_add, &[a1, a1, t1, b1, refl_a1, wt]);
    // step4 : le bzw bzw_w
    let bxy_byz_w = radd(d, bxy_w, byz_w);
    let order = d.lemma(
        rat.add_le_add,
        &[bxy_byz, bxy_byz_w, bzw, bzw_w, step3, step4],
    );
    // order : le total wider
    let wider = radd(d, bxy_byz_w, bzw_w);
    // wider = ((b1+b1)+(vb+b2))+(a1+b1) = ((b1+b1)+((a2+b2)+b2))+(a1+b1)

    // --- reassociate + fuse: `wider` -> `natDivSucc 7 b + natDivSucc 7 a` -----
    let m_right = radd(d, b2, b2); // b2+b2
    let m = radd(d, bxy_w, m_right); // (b1+b1)+(b2+b2)
    let a2_plus_m_right = radd(d, a2, m_right);

    // s1 : ((b1+b1)+(a2+(b2+b2)))+(a1+b1)
    let step_r1 = d.lemma(rat.add_assoc, &[a2, b2, b2]);
    // step_r1 : Eq vb a2_plus_m_right
    let s1_inner = radd(d, bxy_w, a2_plus_m_right);
    let s1 = radd(d, s1_inner, bzw_w);
    let step_r1_lifted = rcongr(d, byz_w, a2_plus_m_right, step_r1, &|d, t| {
        let inner = radd(d, bxy_w, t);
        radd(d, inner, bzw_w)
    });
    // step_r1_lifted : Eq wider s1

    // s2 : (((b1+b1)+a2)+(b2+b2))+(a1+b1)
    let bxy_w_plus_a2 = radd(d, bxy_w, a2);
    let step_r2 = assoc_rev_eq(d, p, bxy_w, a2, m_right);
    // step_r2 : Eq s1_inner (bxy_w_plus_a2+m_right)
    let s2_inner = radd(d, bxy_w_plus_a2, m_right);
    let s2 = radd(d, s2_inner, bzw_w);
    let step_r2_lifted = rcongr(d, s1_inner, s2_inner, step_r2, &|d, t| radd(d, t, bzw_w));
    // step_r2_lifted : Eq s1 s2

    // s3 : ((a2+(b1+b1))+(b2+b2))+(a1+b1)
    let a2_plus_bxy_w = radd(d, a2, bxy_w);
    let step_r3 = d.lemma(rat.add_comm, &[bxy_w, a2]);
    // step_r3 : Eq bxy_w_plus_a2 a2_plus_bxy_w
    let s3_inner = radd(d, a2_plus_bxy_w, m_right);
    let s3 = radd(d, s3_inner, bzw_w);
    let step_r3_lifted = rcongr(d, bxy_w_plus_a2, a2_plus_bxy_w, step_r3, &|d, t| {
        let inner = radd(d, t, m_right);
        radd(d, inner, bzw_w)
    });
    // step_r3_lifted : Eq s2 s3

    // s4 : (a2+m)+(a1+b1)
    let step_r4 = d.lemma(rat.add_assoc, &[a2, bxy_w, m_right]);
    // step_r4 : Eq s3_inner (a2+m)
    let a2_plus_m = radd(d, a2, m);
    let s4 = radd(d, a2_plus_m, bzw_w);
    let step_r4_lifted = rcongr(d, s3_inner, a2_plus_m, step_r4, &|d, t| radd(d, t, bzw_w));
    // step_r4_lifted : Eq s3 s4

    // s5 : a2+(m+(a1+b1))
    let step_r5 = d.lemma(rat.add_assoc, &[a2, m, bzw_w]);
    // step_r5 : Eq s4 (a2+(m+bzw_w)) -- top-level, no lifting needed
    let m_plus_bzw_w = radd(d, m, bzw_w);
    let s5 = radd(d, a2, m_plus_bzw_w);

    // s6 : a2+((m+a1)+b1)
    let step_r6 = assoc_rev_eq(d, p, m, a1, b1);
    // step_r6 : Eq m_plus_bzw_w ((m+a1)+b1)
    let m_plus_a1 = radd(d, m, a1);
    let m_plus_a1_plus_b1 = radd(d, m_plus_a1, b1);
    let s6 = radd(d, a2, m_plus_a1_plus_b1);
    let step_r6_lifted = rcongr(d, m_plus_bzw_w, m_plus_a1_plus_b1, step_r6, &|d, t| {
        radd(d, a2, t)
    });
    // step_r6_lifted : Eq s5 s6

    // s7 : a2+((a1+m)+b1)
    let step_r7 = d.lemma(rat.add_comm, &[m, a1]);
    // step_r7 : Eq m_plus_a1 (a1+m)
    let a1_plus_m = radd(d, a1, m);
    let a1_plus_m_plus_b1 = radd(d, a1_plus_m, b1);
    let s7 = radd(d, a2, a1_plus_m_plus_b1);
    let step_r7_lifted = rcongr(d, m_plus_a1, a1_plus_m, step_r7, &|d, t| {
        let inner = radd(d, t, b1);
        radd(d, a2, inner)
    });
    // step_r7_lifted : Eq s6 s7

    // s8 : a2+(a1+(m+b1))
    let step_r8 = d.lemma(rat.add_assoc, &[a1, m, b1]);
    // step_r8 : Eq a1_plus_m_plus_b1 (a1+(m+b1))
    let m_plus_b1 = radd(d, m, b1);
    let a1_plus_m_plus_b1_r = radd(d, a1, m_plus_b1);
    let s8 = radd(d, a2, a1_plus_m_plus_b1_r);
    let step_r8_lifted = rcongr(
        d,
        a1_plus_m_plus_b1,
        a1_plus_m_plus_b1_r,
        step_r8,
        &|d, t| radd(d, a2, t),
    );
    // step_r8_lifted : Eq s7 s8

    // s9 : (a2+a1)+(m+b1)
    let step_r9 = assoc_rev_eq(d, p, a2, a1, m_plus_b1);
    // step_r9 : Eq s8 ((a2+a1)+m_plus_b1) -- top-level, no lifting needed
    let a2_plus_a1 = radd(d, a2, a1);
    let s9 = radd(d, a2_plus_a1, m_plus_b1);

    // s10 : a3+(m+b1)
    let (a3, step_r10) = fuse_same_index(d, p, two_nat, one_nat, a);
    // step_r10 : Eq a2_plus_a1 a3
    let s10 = radd(d, a3, m_plus_b1);
    let step_r10_lifted = rcongr(d, a2_plus_a1, a3, step_r10, &|d, t| radd(d, t, m_plus_b1));
    // step_r10_lifted : Eq s9 s10

    // s11 : a3+((bb2+m_right)+b1)
    let (bb2, step_r11) = fuse_same_index(d, p, one_nat, one_nat, b);
    // step_r11 : Eq bxy_w bb2
    let bb2_plus_m_right = radd(d, bb2, m_right);
    let bb2_plus_m_right_plus_b1 = radd(d, bb2_plus_m_right, b1);
    let s11 = radd(d, a3, bb2_plus_m_right_plus_b1);
    let step_r11_lifted = rcongr(d, bxy_w, bb2, step_r11, &|d, t| {
        let inner_m = radd(d, t, m_right);
        let inner_mb1 = radd(d, inner_m, b1);
        radd(d, a3, inner_mb1)
    });
    // step_r11_lifted : Eq s10 s11

    // s12 : a3+((bb2+bb4)+b1)
    let (bb4, step_r12) = fuse_same_index(d, p, two_nat, two_nat, b);
    // step_r12 : Eq m_right bb4
    let bb2_plus_bb4 = radd(d, bb2, bb4);
    let bb2_plus_bb4_plus_b1 = radd(d, bb2_plus_bb4, b1);
    let s12 = radd(d, a3, bb2_plus_bb4_plus_b1);
    let step_r12_lifted = rcongr(d, m_right, bb4, step_r12, &|d, t| {
        let inner_m = radd(d, bb2, t);
        let inner_mb1 = radd(d, inner_m, b1);
        radd(d, a3, inner_mb1)
    });
    // step_r12_lifted : Eq s11 s12

    // s13 : a3+(bb6+b1)
    let four_nat = d.num(4);
    let (bb6, step_r13) = fuse_same_index(d, p, two_nat, four_nat, b);
    // step_r13 : Eq bb2_plus_bb4 bb6
    let bb6_plus_b1 = radd(d, bb6, b1);
    let s13 = radd(d, a3, bb6_plus_b1);
    let step_r13_lifted = rcongr(d, bb2_plus_bb4, bb6, step_r13, &|d, t| {
        let inner_mb1 = radd(d, t, b1);
        radd(d, a3, inner_mb1)
    });
    // step_r13_lifted : Eq s12 s13

    // s14 : a3+b7
    let six_nat = d.num(6);
    let (b7, step_r14) = fuse_same_index(d, p, six_nat, one_nat, b);
    // step_r14 : Eq bb6_plus_b1 b7
    let s14 = radd(d, a3, b7);
    let step_r14_lifted = rcongr(d, bb6_plus_b1, b7, step_r14, &|d, t| radd(d, a3, t));
    // step_r14_lifted : Eq s13 s14

    // s15 : b7+a3
    let step_r15 = d.lemma(rat.add_comm, &[a3, b7]);
    // step_r15 : Eq s14 s15 -- top-level, no lifting needed
    let s15 = radd(d, b7, a3);

    let (_, wider_to_s15) = rchain(
        d,
        wider,
        &[
            (s1, step_r1_lifted),
            (s2, step_r2_lifted),
            (s3, step_r3_lifted),
            (s4, step_r4_lifted),
            (s5, step_r5),
            (s6, step_r6_lifted),
            (s7, step_r7_lifted),
            (s8, step_r8_lifted),
            (s9, step_r9),
            (s10, step_r10_lifted),
            (s11, step_r11_lifted),
            (s12, step_r12_lifted),
            (s13, step_r13_lifted),
            (s14, step_r14_lifted),
            (s15, step_r15),
        ],
    );

    let le_wider_s15 = {
        let refl_wider = d.lemma(rat.le_refl, &[wider]);
        rat_eq_rewrite(d, wider, s15, wider_to_s15, refl_wider, &|d, t| {
            rle(d, rat, wider, t)
        })
    };

    let a7 = div_succ(d, p, 7, a);
    let three_nat = d.num(3);
    let pad_le = d.lemma(rat.nat_div_succ_le_add_left, &[three_nat, four_nat, a]);
    // pad_le : le a3 a7 (3+4 reduces to 7)
    let refl_b7 = d.lemma(rat.le_refl, &[b7]);
    let le_s15_target = d.lemma(rat.add_le_add, &[b7, b7, a3, a7, refl_b7, pad_le]);
    let target = radd(d, b7, a7);
    let le_wider_target = d.lemma(
        rat.le_trans,
        &[wider, s15, target, le_wider_s15, le_s15_target],
    );
    let final_order = d.lemma(
        rat.le_trans,
        &[total, wider, target, order, le_wider_target],
    );

    let result = weaken(d, p, diff, total, target, raw, final_order);

    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, result);
        let over_b = d.lam_fv(b_fv, nat, with_hle);
        d.lam_fv(a_fv, nat, over_b)
    };
    let ty = {
        let claim = within(d, p, diff, target);
        let after_hle = d.arrow(hle_ty, claim);
        let over_b = d.pi_fv(b_fv, nat, after_hle);
        d.pi_fv(a_fv, nat, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_cauchy_ordered_half,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.geomCauchy`. See the field documentation
/// ([`CRealPrelude::geom_cauchy`]) for the statement and the derivation —
/// verbatim in *technique* to
/// `series.rs::declare_sum_range_cauchy_of_dominated`'s own `Nat.le_total`
/// case split, at the single fixed witness `K := 7` in place of that
/// theorem's `k + 8`.
fn declare_geom_cauchy(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let f = pow_half_fn(d, p);
    let sum_f = d.const_app(p.sum_range, &[f]);
    let target = d.const_app(p.cauchy, &[sum_f]);
    let seven_nat = d.num(7);

    let case_proof = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let sum_f_m = d.const_app(p.sum_range, &[f, m]);
        let sum_f_n = d.const_app(p.sum_range, &[f, n]);
        let y_m = sample(d, p, sum_f_m, m);
        let z_n = sample(d, p, sum_f_n, n);
        let diff_mn = rsub(d, rat, y_m, z_n);
        let bm = div_succ(d, p, 7, m);
        let bn = div_succ(d, p, 7, n);
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
            // m <= n: `geom_cauchy_ordered_half` at (a := m, b := n) gives
            // `Within (z_n - y_m) (bn + bm)`; flip the difference, then
            // reorder the bound.
            &|d, hmn| {
                let raw = d.lemma(p.geom_cauchy_ordered_half, &[m, n, hmn]);
                let bn2 = div_succ(d, p, 7, n);
                let bm2 = div_succ(d, p, 7, m);
                let bound_nm = radd(d, bn2, bm2);
                let flipped = within_symm(d, p, z_n, y_m, bound_nm, raw);
                let comm_eq = d.lemma(rat.add_comm, &[bn2, bm2]);
                rat_eq_rewrite(d, bound_nm, bound_mn, comm_eq, flipped, &|d, t| {
                    within(d, p, diff_mn, t)
                })
            },
            // n <= m: `geom_cauchy_ordered_half` at (a := n, b := m) lands
            // exactly on `Within (y_m - z_n) (bm + bn)` -- no rewrite.
            &|d, hnm| d.lemma(p.geom_cauchy_ordered_half, &[n, m, hnm]),
        );
        let over_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(m_fv, nat, over_n)
    };

    let predicate_f = {
        let kf_fv = d.fresh_fvar();
        let kf = d.kernel().fvar(kf_fv);
        let body = sum_range_cauchy_body(d, p, sum_f, kf);
        d.lam_fv(kf_fv, nat, body)
    };
    let target_proof = exists_nat_intro(d, p, predicate_f, seven_nat, case_proof);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_cauchy,
        uparams: vec![],
        ty: target,
        value: target_proof,
    })
}

/// Admit `CReal.geom_half_inv_leaf_bound`, `CReal.geom_cauchy_ordered_half`
/// and `CReal.geom_cauchy`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_geom_cauchy_family(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_geom_half_inv_leaf_bound(d, p)?;
    declare_geom_cauchy_ordered_half(d, p)?;
    declare_geom_cauchy(d, p)
}

// ============================================================================
// `Cauchy (sumRange expDominant)`, and `Converges expSeriesPartial` — carrying
// `geomCauchy` through `CReal.mul`'s index shift.
// ============================================================================
//
// `expDominant n := mul two (pow half n)`, so `sumRange expDominant m` is
// only `Equiv` to `mul two (sumRange (pow half ·) m)` (`CReal.mul_sumRange`,
// already landed) — `CReal.mul`'s own representative resamples its factors
// at a shifted index depending on both factors' magnitude (`product.rs`), so
// the two sides are not literally the same rational at any index. Two
// candidate routes were open for scaling `geomCauchy` through that shift:
//
// (a) re-derive `product.rs`'s `mulShift`/`mul_index`/`regular_between`
//     bookkeeping by hand for the specific pair `(two, sumRange (pow half
//     ·) m)`, building a bespoke "`Cauchy f` scaled by a constant" witness;
// (b) reuse the machinery `convergence.rs::declare_converges_mul` already
//     built for exactly this shape (a fixed sequence times a convergent
//     one), and separately transport the result across `mul_sumRange`'s
//     `Equiv`.
//
// Route (b) needs no new index-shift bookkeeping at all: `CReal.converges_mul`
// already proves `Converges f L → Converges g M → Converges (fun n => mul (f
// n) (g n)) (mul L M)`, handling `CReal.mul`'s shift internally (via
// `product::product_gap`/`regular_between`, reused there). Taking `f := const
// two` (via `CReal.converges_of_const`) and `g := sumRange (pow half ·)`
// (convergent, from `CReal.geomCauchy` + `CReal.converges_of_cauchy`) gives
// `Converges (fun n => mul two (sumRange (pow half ·) n)) (mul two L)` for
// free. `CReal.converges_cauchy` turns that into `Cauchy (fun n => mul two
// (sumRange (pow half ·) n))` — call it `Cauchy G`.
//
// What is genuinely new, and is [`declare_cauchy_of_pointwise_equiv`] below:
// **`Cauchy G` is not yet `Cauchy (sumRange expDominant)`** — `G n` and
// `sumRange expDominant n` are only `Equiv`, via `mul_sumRange`, not equal.
// Scaling a `Cauchy` witness across a pointwise `Equiv` is itself a genuinely
// GENERAL lemma (nothing about `mul`, `two`, or the geometric series is
// specific to it): `∀ G F, (∀n, Equiv (G n) (F n)) → Cauchy G → Cauchy F`,
// with the witness padded by one regularity unit (`natDivSucc 2 ·`) on each
// side, exactly the way `convergence.rs::converges_gap_at` pads a
// `Converges`-shaped middle term — except the middle term here is a genuine
// two-index `Cauchy` bound (`k@m + k@n`), not `converges_gap_at`'s
// single-index `Converges` bound, so that helper does not fit verbatim and
// [`telescope_cauchy_pad2`] rebuilds the combine/reassemble step generically.
//
// So: **no bespoke `CReal.mul`-index-shift proof was needed for the
// EXISTENTIAL `Cauchy (sumRange expDominant)` below.** The general lemma
// this lane needed and built is `Cauchy` transport across a pointwise
// `Equiv`; the "scaling by a constant" half of that job was already
// available off the shelf via `converges_mul`/`converges_of_const`.
//
// **`CReal.e` itself needs more than existence, though — it needs the
// witness `K` as DATA — and route (b) cannot supply that** (`Exists.rec` is
// Prop-only, so `K` cannot be unwrapped out of `Converges`'s own `∃K, …`).
// So the later section of this file ("A CONCRETE … `Cauchy` witness…", below
// [`declare_exp_dominant_cauchy`]) DOES redo route (a) by hand after all —
// `mul_deshift` — but only for `c := two`, exploiting that `CReal.ofRat`'s
// representative is a literal constant (so there is no `c`-side regularity
// gap to bound, unlike a fully general "arbitrary `c`" version, which this
// file does not attempt).

/// Combine three `Within` proofs telescoping `x − w`:
///
/// - `t1 : Within (x − y) (natDivSucc e a)`
/// - `t2 : Within (y − z) (natDivSucc k a + natDivSucc k b)`
/// - `t3 : Within (z − w) (natDivSucc e b)`
///
/// into `Within (x − w) (natDivSucc (k+e) a + natDivSucc (k+e) b)`, returning
/// `(k+e, proof)`.
///
/// [`declare_cauchy_of_pointwise_equiv`]/[`cauchy_body_transport`] call this
/// with `e := 2` (`G`'s `Cauchy` witness widened by one `Equiv`-derived
/// regularity unit on each of `m`/`n`); [`mul_ordered_half_body`] calls it
/// with a general `e` (`CReal.mul`'s own de-shift unit, `magnitude_of(c)*2`,
/// via [`mul_deshift`]) — hence the parameter, rather than a literal `2`
/// baked in. Built the same way `convergence.rs::converges_gap_at` combines a
/// `Converges`-shaped middle bound (`fuse_at` + `Rat.sub_add_sub` twice), but
/// generalized: `converges_gap_at`'s own middle hypothesis is single-index
/// (`Within (seq u n − seq v n) (natDivSucc k n)`), which is why that helper
/// cannot be reused verbatim against a genuinely two-index `Cauchy` middle
/// term (`k@a + k@b`) — combining it needs the raw `Rat.bounds_add` +
/// `Rat.add_assoc`/`Rat.add_comm` reassembly below rather than `fuse_at`.
fn telescope_cauchy_pad2(
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

    // combine (x−y) + (y−z).
    let (l1, u1) = halves(d, p, q1, bound1, t1);
    let (l2, u2) = halves(d, p, q2, bound2, t2);
    let c12 = d.lemma(rat.bounds_add, &[q1, bound1, q2, bound2, l1, u1, l2, u2]);
    let q12 = radd(d, q1, q2);
    let b12 = radd(d, bound1, bound2);

    // combine that with (z−w).
    let (l12, u12) = halves(d, p, q12, b12, c12);
    let (l3, u3) = halves(d, p, q3, bound3, t3);
    let c123 = d.lemma(rat.bounds_add, &[q12, b12, q3, bound3, l12, u12, l3, u3]);
    let q123 = radd(d, q12, q3);
    let b123 = radd(d, b12, bound3);

    // Quantity identity: (q1+q2)+q3 = x-w.
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

    // Bound reassembly: ((2@a) + (k@a+k@b)) + (2@b) -> (k+2)@a + (k+2)@b.
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

/// `CReal.cauchyOfPointwiseEquiv : ∀ G F, (∀ n, Equiv (G n) (F n)) → Cauchy G
/// → Cauchy F`.
///
/// See the module documentation above for why this is the piece that was
/// actually missing (not a bespoke `CReal.mul` index-shift lemma). Widens the
/// `Cauchy G` witness `k` to `k+2` by inserting one `Equiv`-derived
/// regularity unit on each side of `G`'s own middle term
/// (`telescope_cauchy_pad2`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cauchy_of_pointwise_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = d.arrow(nat, carrier);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let heq_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let gn = d.apply(g, &[n]);
        let fn_val = d.apply(f, &[n]);
        let claim = equiv(d, p, gn, fn_val);
        d.pi_fv(n_fv, nat, claim)
    };
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let cauchy_g_ty = d.const_app(p.cauchy, &[g]);
    let hcauchy_fv = d.fresh_fvar();
    let hcauchy = d.kernel().fvar(hcauchy_fv);

    let target = d.const_app(p.cauchy, &[f]);

    let predicate_g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = sum_range_cauchy_body(d, p, g, k);
        d.lam_fv(k_fv, nat, body)
    };

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hbody_ty = sum_range_cauchy_body(d, p, g, k);
        let hbody_fv = d.fresh_fvar();
        let hbody = d.kernel().fvar(hbody_fv);

        let (k_plus_2, case_proof) = {
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
        };

        let predicate_f = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let body = sum_range_cauchy_body(d, p, f, k2);
            d.lam_fv(k2_fv, nat, body)
        };
        let target_proof = exists_nat_intro(d, p, predicate_f, k_plus_2, case_proof);

        let with_hbody = d.lam_fv(hbody_fv, hbody_ty, target_proof);
        d.lam_fv(k_fv, nat, with_hbody)
    };

    let proof_body = exists_elim(d, p, nat, predicate_g, target, hcauchy, minor);

    let value = {
        let with_hcauchy = d.lam_fv(hcauchy_fv, cauchy_g_ty, proof_body);
        let with_heq = d.lam_fv(heq_fv, heq_ty, with_hcauchy);
        let with_f = d.lam_fv(f_fv, seq_ty, with_heq);
        d.lam_fv(g_fv, seq_ty, with_f)
    };
    let ty = {
        let after_hcauchy = d.arrow(cauchy_g_ty, target);
        let after_heq = d.arrow(heq_ty, after_hcauchy);
        let with_f = d.pi_fv(f_fv, seq_ty, after_heq);
        d.pi_fv(g_fv, seq_ty, with_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cauchy_of_pointwise_equiv,
        uparams: vec![],
        ty,
        value,
    })
}

// ----------------------------------------------------------------------------
// A CONCRETE (non-existential) `Cauchy` witness for `sumRange expDominant`,
// and from it for `sumRange expTerm` -- what `CReal.e` itself needs.
// ----------------------------------------------------------------------------
//
// [`declare_exp_dominant_cauchy`] above gives `Cauchy (sumRange expDominant)`
// (an `Exists Nat …`), which is enough for
// `CReal.sumRange_converges_of_dominated`/`sumRange_cauchy_of_dominated`, but
// **not** enough to build `CReal.e`: `CReal.mk` needs an explicit `Nat → Rat`
// sequence, and `speedup (diagonal expSeriesPartial) K` needs `K` as DATA — an
// `∃K, …` witness cannot be unwrapped into `K` itself (`Exists.rec` is
// Prop-only). So this section rebuilds `Cauchy (sumRange expDominant)` with an
// EXPLICIT numerator, by doing the `CReal.mul` index-shift bookkeeping route
// (a) named (and set aside) in this file's earlier module documentation —
// there is no way around it once the witness itself, not just its existence,
// is needed as data.
//
// `mul_deshift` de-shifts `CReal.mul`'s own representative for `mul c x`
// (`c` fixed) back to the "naive" product `q · seq x n` at the SAME index
// `n`, for `q` any term the caller asserts equals `seq c` everywhere — sound
// here because `c := two := CReal.ofRat …` has a literally constant
// representative (`CReal.ofRat`'s value ignores its index entirely), so
// `seq c high` and `seq c n` are the SAME term (`q`) up to nothing more than
// unfolding — no `c`-side regularity gap to bound, unlike the fully general
// "arbitrary `c`" version this file's earlier module documentation
// considered and did not attempt. `g_ordered_half_body` uses it twice (once
// per side of an ordered pair) plus `CReal.geomCauchy_ordered_half` scaled by
// the same trick, combined via [`telescope_cauchy_pad2`]; then
// `promote_ordered_half_to_full` — the same `Nat.le_total` case-split
// `CReal.geomCauchy` and `CReal.sumRange_cauchy_of_dominated` both use —
// turns the ordered pair into the full, concrete `sum_range_cauchy_body`
// `CReal.e`'s construction needs.

/// `Rat.natDivSucc k idx`, with a symbolic numerator `k`. `div_succ` (already
/// imported) only takes a literal `u32`.
fn div_succ_sym(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, idx: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, idx])
}

/// `CReal.bound x`.
fn bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.bound, &[x])
}

/// `CReal.bound x + 1` — reproduced verbatim from `product.rs`'s own private
/// `magnitude_of` (that module's precedent for reproducing a sibling's
/// private helper rather than widening its visibility).
fn magnitude_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let base = bound_of(d, p, x);
    d.succ(base)
}

/// `Eq (a*(b-c)) (a*b - a*c)`, via `Rat.left_distrib` (stated over `+`) and
/// `Rat.mul_neg` (`a*(-c) = -(a*c)`), bridging `Rat.sub`'s `add … (neg …)`
/// unfolding the same way this file's other rewrites lean on defeq rather
/// than an explicit `Rat.sub`-shaped distributivity lemma (there is none).
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
/// n)`, `high := mul_index (mul_shift c x) n` — `CReal.mul`'s own
/// representative for `mul c x` at `n`, de-shifted back down to the "naive"
/// product `q * seq x n` at the SAME index. `q` is any term the caller
/// asserts equals `seq c` at any index — sound for the constant `c := two`
/// this file uses it for (see the section documentation above), and it is
/// the ONLY place that assumption is used: everything else here is generic
/// `CReal.mul`/`CReal.bound_within`/`product::regular_between` bookkeeping.
///
/// Returns `(magnitude_of(c) * 2, proof)`.
fn mul_deshift(
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

/// `Within (seq (mul c (s b)) b - seq (mul c (s a)) a) (natDivSucc K b +
/// natDivSucc K a)`, `K := magnitude_of(c) * k_s + magnitude_of(c) * 2`,
/// given `a ≤ b` and `s_ordered_half(a,b,hab) : Within (seq (s b) b - seq (s
/// a) a) (natDivSucc k_s b + natDivSucc k_s a)`.
///
/// The three-bracket telescope `seq(mul c (s b))b − q·seq(s b)b`,
/// `q·seq(s b)b − q·seq(s a)a`, `q·seq(s a)a − seq(mul c (s a))a`
/// ([`mul_deshift`] twice, `s_ordered_half` scaled by `q` once, combined by
/// [`telescope_cauchy_pad2`]) — the concrete-witness analogue of
/// `CReal.converges_mul`'s role in [`declare_exp_dominant_cauchy`] above,
/// needed here because that route only ever produces an existential `Cauchy`.
#[allow(clippy::too_many_arguments)]
fn mul_ordered_half_body(
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

    // The middle term: `geomCauchy_ordered_half`(a,b,hab)-shaped, scaled by
    // `q` the same way `mul_deshift` scales its own regularity gap.
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
/// `sum_range_cauchy_body`-shaped statement `∀ m n, Within (seq (func m) m −
/// seq (func n) n) (natDivSucc k m + natDivSucc k n)`, via `Nat.le_total`.
/// Verbatim in technique to `exponential.rs::declare_geom_cauchy`'s own case
/// split (`within_symm` plus one `Rat.add_comm` rewrite in the `m ≤ n`
/// branch; the `n ≤ m` branch lands on the target shape directly) —
/// generalized off the concrete witness `7` so both
/// [`mul_ordered_half_body`]'s promotion and `CReal.sumRange_cauchy_of_dominated`'s
/// own analogous step (reproduced here rather than reused — it is a private
/// `fn` there) can share it.
fn promote_ordered_half_to_full(
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

/// `CReal.expDominantCauchy : Cauchy (sumRange expDominant)`.
///
/// Built via route (b) in the module documentation above: `CReal.geomCauchy`
/// gives `Cauchy (sumRange (pow half ·))`; `CReal.converges_of_cauchy` lifts
/// it to `Converges (sumRange (pow half ·)) L` for some `L` (eliminated
/// immediately, into the Prop goal `Cauchy (sumRange expDominant)` — never
/// into data); `CReal.converges_of_const`/`CReal.converges_mul` give
/// `Converges (fun n => mul two (sumRange (pow half ·) n)) (mul two L)`;
/// `CReal.converges_cauchy` turns that into `Cauchy (fun n => mul two
/// (sumRange (pow half ·) n))`; and
/// [`CRealPrelude::cauchy_of_pointwise_equiv`] transports it across
/// `CReal.mul_sumRange`'s `Equiv` onto `Cauchy (sumRange expDominant)`.
///
/// This never touches `CReal.inv`/`CRealPrelude::pos_bound` — the containment
/// `geomCauchy`'s own route has (`inv` reached only by
/// `geomHalfInvLeafBound`/`geomCauchyOrderedHalf`) is preserved, since
/// nothing here calls either.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_exp_dominant_cauchy(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);

    let f = pow_half_fn(d, p);
    let sum_f = d.const_app(p.sum_range, &[f]);
    let geom_cauchy_proof = d.lemma(p.geom_cauchy, &[]);

    let ex_conv = d.lemma(p.converges_of_cauchy, &[sum_f, geom_cauchy_proof]);

    let two_creal = two(d, p);
    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let sum_g_dominant = d.const_app(p.sum_range, &[exp_dominant_const]);
    let target = d.const_app(p.cauchy, &[sum_g_dominant]);

    let predicate_l = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let body = converges_applied(d, p, sum_f, l);
        d.lam_fv(l_fv, carrier, body)
    };

    let minor = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let hl_ty = converges_applied(d, p, sum_f, l);
        let hl_fv = d.fresh_fvar();
        let hl = d.kernel().fvar(hl_fv);

        let const_two_fn = {
            let ignore_fv = d.fresh_fvar();
            d.lam_fv(ignore_fv, nat, two_creal)
        };
        let h_const = d.lemma(p.converges_of_const, &[two_creal]);

        let h_prod = d.lemma(
            p.converges_mul,
            &[const_two_fn, sum_f, two_creal, l, h_const, hl],
        );

        let fg = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let cn = d.apply(const_two_fn, &[n]);
            let sn = d.apply(sum_f, &[n]);
            let prod = cmul(d, p, cn, sn);
            d.lam_fv(n_fv, nat, prod)
        };
        let mul_two_l = cmul(d, p, two_creal, l);

        let h_cauchy_g = d.lemma(p.converges_cauchy, &[fg, mul_two_l, h_prod]);

        let heq = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = d.lemma(p.mul_sum_range, &[two_creal, f, n]);
            d.lam_fv(n_fv, nat, body)
        };

        let cauchy_f_proof = d.lemma(
            p.cauchy_of_pointwise_equiv,
            &[fg, sum_g_dominant, heq, h_cauchy_g],
        );

        let with_hl = d.lam_fv(hl_fv, hl_ty, cauchy_f_proof);
        d.lam_fv(l_fv, carrier, with_hl)
    };

    let proof_body = exists_elim(d, p, carrier, predicate_l, target, ex_conv, minor);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_dominant_cauchy,
        uparams: vec![],
        ty: target,
        value: proof_body,
    })
}

/// `CReal.expSeriesPartialConverges : Exists CReal (fun L => Converges
/// expSeriesPartial L)` — `CReal.sumRange_converges_of_dominated` applied to
/// `CReal.exp_term_abs_le_dominant` and [`CRealPrelude::exp_dominant_cauchy`].
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_exp_series_partial_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let exp_term_const = d.kernel().const_(p.exp_term, vec![]);
    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let exp_series_partial_const = d.kernel().const_(p.exp_series_partial, vec![]);

    let hyp1 = d.lemma(p.exp_term_abs_le_dominant, &[]);
    let hyp2 = d.lemma(p.exp_dominant_cauchy, &[]);

    let proof = d.lemma(
        p.sum_range_converges_of_dominated,
        &[exp_term_const, exp_dominant_const, hyp1, hyp2],
    );

    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let body = converges_applied(d, p, exp_series_partial_const, l);
    let predicate = d.lam_fv(l_fv, carrier, body);
    let ty = exists_ty(d, p, carrier, predicate);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_series_partial_converges,
        uparams: vec![],
        ty,
        value: proof,
    })
}

/// Admit `CReal.cauchyOfPointwiseEquiv`, `CReal.expDominantCauchy` and
/// `CReal.expSeriesPartialConverges`. Run **after**
/// [`declare_geom_cauchy_family`] (needs `geomCauchy`/`geomCauchyOrderedHalf`)
/// and after `series::declare_series`/`convergence::declare_convergence`/
/// `convergence::declare_cauchy_convergence` (needs `mul_sumRange`,
/// `sum_range_converges_of_dominated`, `converges_mul`, `converges_cauchy`,
/// `converges_of_const`, `converges_of_cauchy` — all declared well before
/// `exponential::declare_exponential` runs, per `creal.rs`'s own ordering).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exp_convergence(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_cauchy_of_pointwise_equiv(d, p)?;
    declare_exp_dominant_cauchy(d, p)?;
    declare_exp_series_partial_converges(d, p)
}

// ----------------------------------------------------------------------------
// `CReal.e` — via `CReal.mk` on an explicit regular sequence, never an
// `Exists`-elimination into data.
// ----------------------------------------------------------------------------

/// `λ n, CReal.seq (f n) n` — the raw diagonal `regular_of_scaled_cauchy`
/// consumes. Reproduced verbatim from `convergence.rs`'s own private
/// `diagonal` (that module's own precedent for reusing a sibling's private
/// helper by reproduction rather than widening its visibility).
fn diagonal_seq(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(f, &[n]);
    let body = sample(d, p, fn_term, n);
    d.lam_fv(n_fv, nat, body)
}

/// A CONCRETE `(K, proof : sum_range_cauchy_body (sumRange expDominant) K)`.
///
/// Not a kernel declaration on its own — an internal-plumbing artifact
/// [`declare_e`] consumes directly (the coverage assertion in
/// `creal_tests.rs` only needs to see what is actually exported). Built via
/// [`mul_ordered_half_body`] (`c := two`, `q := two`'s own rational,
/// `s := pow_half_fn`, scaled `CReal.geomCauchy_ordered_half` at `k_s := 7`)
/// plus [`promote_ordered_half_to_full`]'s `Nat.le_total` promotion.
fn exp_dominant_cauchy_body_concrete(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId) {
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

    // `G := fun n => mul two (S n)`, `S := sumRange (pow half ·)`.
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

    // Concrete `Cauchy G` at `k_g` -- `G` itself, not yet `sumRange
    // expDominant` (only `Equiv`, via `CReal.mul_sumRange`).
    let g_case_proof = promote_ordered_half_to_full(d, p, g_fn, k_g, &ordered_half);

    // Transport across `mul_sumRange`'s `Equiv` onto `F := sumRange
    // expDominant` -- the same transport [`declare_cauchy_of_pointwise_equiv`]
    // performs, but concrete (`cauchy_body_transport`, not wrapped in
    // `Exists`), because `K` is needed as DATA here.
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

/// Given `heq : ∀n, Equiv (G n) (F n)` and `hbody : sum_range_cauchy_body (G,
/// k)`, build `(k+2, sum_range_cauchy_body (F, k+2))`. The concrete-witness
/// core of [`declare_cauchy_of_pointwise_equiv`]'s own case split
/// (reproduced rather than shared — that declaration is already landed and
/// kernel-verified; this file's convention elsewhere is to reproduce a small
/// private helper rather than risk the tested one), extracted so a caller
/// needing `K` as DATA — not hidden inside `Cauchy`'s own `∃K, …` — can use
/// it directly. [`exp_dominant_cauchy_body_concrete`] is that caller.
fn cauchy_body_transport(
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

/// `CReal.e := CReal.mk (speedup (diagonal expSeriesPartial) K) (…)`, `K :=
/// exp_dominant_cauchy_body_concrete`'s witness `+8` (as 8 nested `Nat.succ`,
/// matching `CReal.sumRange_cauchy_dominated_ordered_normalized`'s own
/// internal `K' := k+8` up to defeq — see that theorem's doc and
/// `CReal.sumRange_cauchy_of_dominated`'s own case split, which relies on
/// exactly this defeq rather than re-deriving `K'`'s closed form by hand).
///
/// The shared ingredients `CReal.e`'s definition AND `CReal.e_converges`'s
/// proof both need: `(raw, k_final, exp_series_partial_body)`, where `raw :=
/// diagonal expSeriesPartial`, `k_final` is the Cauchy witness `e`'s
/// definition speeds up by, and `exp_series_partial_body :
/// sum_range_cauchy_body (expSeriesPartial, k_final)`.
///
/// **MUST be called EXACTLY ONCE, by `declare_e_family`, and the resulting
/// `ExprId`s threaded as PARAMETERS into both [`declare_e`] and
/// [`declare_e_converges`]** -- one derivation, not two, is simply the right
/// hygiene. NOTE, since it is easy to over-credit this: sharing the
/// `ExprId`s does NOT by itself fix the stack overflow a previous version of
/// this file had. That overflow's actual cause and fix are documented on
/// [`declare_e_converges`] (building generically over a bound `K` rather
/// than the concrete `k_final`); this function's job is only to make sure
/// both callers start from the identical witness.
///
/// Bisection method used to isolate the fault (2026-08-26):
/// `creal::creal_tests::creal_prelude_builds` with `declare_e_family`'s
/// dispatch calls disabled one at a time (`declare_e` alone: ~15s, matching
/// the untouched baseline; adding `declare_e_converges` reproduced the
/// overflow), then a probe that declared each of `declare_e_converges`'s
/// intermediate terms against its OWN freshly-inferred type -- fast at
/// every step up to and including the per-`n` `Within` proof, narrowing the
/// fault to the FINAL `converges_predicate`/`exists_intro` ascription --
/// and finally a direct, timed `Kernel::def_eq(speedup_n, seq(target, n))`
/// call, which hung regardless of whether `target` was the named `e` or a
/// freshly, independently, or identically re-derived local `mk(...)` value.
fn e_ingredients(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId, ExprId) {
    // `k_dom` is `exp_dominant_cauchy_body_concrete`'s RETURNED witness for
    // `Cauchy (sumRange expDominant)` -- already `K_G + 2` (the `+2` from its
    // own internal `cauchy_body_transport`), not the raw `K_G` for `G` alone.
    let (k_dom, hyp2) = exp_dominant_cauchy_body_concrete(d, p);

    let exp_term_const = d.kernel().const_(p.exp_term, vec![]);
    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let exp_series_partial_const = d.kernel().const_(p.exp_series_partial, vec![]);
    let hyp1 = d.lemma(p.exp_term_abs_le_dominant, &[]);

    let ordered_half = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, hab: ExprId| -> ExprId {
        d.lemma(
            p.sum_range_cauchy_dominated_ordered_normalized,
            &[
                exp_term_const,
                exp_dominant_const,
                k_dom,
                a,
                b,
                hyp1,
                hyp2,
                hab,
            ],
        )
    };

    let mut k_final = k_dom;
    for _ in 0..8 {
        k_final = d.succ(k_final);
    }

    let exp_series_partial_body =
        promote_ordered_half_to_full(d, p, exp_series_partial_const, k_final, &ordered_half);

    let raw = diagonal_seq(d, p, exp_series_partial_const);
    (raw, k_final, exp_series_partial_body)
}

/// `raw`/`k_final`/`exp_series_partial_body` are the CALLER's — see
/// [`declare_e_family`]'s own doc for why these must be the SAME `ExprId`s
/// [`declare_e_converges`] uses, not a second, independently-derived
/// (merely value-equal) copy.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_e(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k_final: ExprId,
    exp_series_partial_body: ExprId,
) -> Result<(), KernelError> {
    let exp_series_partial_const = d.kernel().const_(p.exp_series_partial, vec![]);

    let speedup_term = d.const_app(p.speedup, &[raw, k_final]);
    let regularity_proof = d.lemma(
        p.regular_of_scaled_cauchy,
        &[exp_series_partial_const, k_final, exp_series_partial_body],
    );

    let constructor = d.kernel().const_(p.mk, vec![]);
    let value = d.apply(constructor, &[speedup_term, regularity_proof]);
    let ty = creal_ty(d, p);

    d.kernel().add_declaration(Declaration::Definition {
        name: p.e,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 40),
    })
}

/// `CReal.e_converges : Converges expSeriesPartial e` — `e`'s own defining
/// property, and the missing link every property of `e` needs
/// (`converges_lower_bound`/`converges_lower_bound_shift`/
/// `converges_upper_bound` all consume a `Converges` hypothesis, not a bare
/// `Cauchy` one).
///
/// Built by reproducing [`super::convergence::declare_converges_of_cauchy`]'s
/// own `minor` closure directly against CONCRETE data (`k_final`,
/// `exp_series_partial_body` from [`e_ingredients`]) instead of running it
/// through that theorem's `Exists`-elimination over an abstract `Cauchy`
/// witness: the existential route can only produce `Converges f L` for an
/// OPAQUE `L` bound inside the proof, never for the literal declared `e`, and
/// `Exists.rec` is `Prop`-only so `L` cannot be extracted as data afterward
/// either. `e`'s own `seq` projection ignores which `Regular` proof `CReal.mk`
/// was given (the projector only reads the first field), so the concrete
/// witness built here needs no separate proof that it matches `e`'s own
/// `regularity_proof` — only `raw`/`k_final` need to match, and
/// [`e_ingredients`] guarantees that structurally.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_e_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k_final: ExprId,
    exp_series_partial_body: ExprId,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let exp_series_partial_const = d.kernel().const_(p.exp_series_partial, vec![]);
    let e_const = d.kernel().const_(p.e, vec![]);

    // Build the proof GENERICALLY over a BOUND `(k : Nat) (h :
    // sum_range_cauchy_body (expSeriesPartial, k))`, exactly mirroring
    // `declare_converges_of_cauchy`'s own `minor` closure shape, and apply
    // it at the CONCRETE `(k_final, exp_series_partial_body)` only at the
    // very end.
    //
    // Measured root cause (2026-08-26): building the per-`n` proof directly
    // against the CONCRETE `k_final` makes `speedup(raw, k_final)` a
    // partially-concrete Nat expression (concrete in `k_final`, symbolic in
    // `n`). The kernel's lazy-delta `is_def_eq`, forced to compare
    // `speedup_term(n)` against `seq(l_val, n)` inside `exists_intro`'s
    // argument check, unfolds `speedup` and `seq` in lock-step (their names
    // differ, so neither side's unfold is deferred to let the other catch
    // up) and the two sides never re-synchronize at the point where they
    // ARE equal -- both race forward, and because the Nat.mul/Nat.add
    // building the reindexed sample index has `k_final` concrete enough to
    // fire (unlike a fully symbolic `k`, which cannot fire at all against a
    // free variable), that race partially evaluates `sumRange` at a
    // symbolic index, driving recursion depth into the thousands and
    // overflowing a 1 GiB RELEASE stack (confirmed by isolating and timing
    // `Kernel::def_eq(speedup_n, seq(l_val, n))` directly: it alone hangs,
    // with or without an independently-recomputed `e_ingredients`).
    //
    // With `k` and `h` BOUND (Pi/lambda variables, not yet substituted),
    // every `Nat.mul`/`Nat.add` built from them stays stuck against BOTH
    // fvars simultaneously -- exactly why `declare_converges_of_cauchy`
    // itself (which never concretizes its own `K` before `add_declaration`
    // time) has never hit this. `Kernel::infer` on the finished lambda only
    // needs to type-check its BODY once, generically; substituting the
    // concrete `(k_final, exp_series_partial_body)` afterward is then a
    // plain Pi-application (codomain substitution), never re-entering the
    // per-`n` comparison.
    let generic = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = sum_range_cauchy_body(d, p, exp_series_partial_const, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let kregular_proof = kregular_of_cauchy_proof(d, p, raw, k, hp);
        let speedup_term = d.const_app(p.speedup, &[raw, k]);
        let sc = d.const_app(p.speedup_close, &[raw, k, kregular_proof]);

        let regularity_proof = d.lemma(
            p.regular_of_scaled_cauchy,
            &[exp_series_partial_const, k, hp],
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
        let converges_pred = converges_predicate(d, p, exp_series_partial_const, l_val);
        let converges_proof = exists_intro(d, p, nat, converges_pred, k2, over_n);

        let with_hp = d.lam_fv(hp_fv, hp_ty, converges_proof);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let value = d.apply(generic, &[k_final, exp_series_partial_body]);

    let ty = converges_applied(d, p, exp_series_partial_const, e_const);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.e_converges,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.two_le_e : le two e`.
///
/// **The eventual argument.** `expSeriesPartial 0 = 0 < 2`, so
/// `converges_lower_bound` cannot apply directly — the bound only holds from
/// index `2` on. Two pieces close it:
///
/// - `CReal.sumRange_mono_outer` at `f := expTerm` (nonnegative by
///   [`CRealPrelude::exp_term_nonneg`]) gives `∀ m n, Nat.le m n → le
///   (expSeriesPartial m) (expSeriesPartial n)`, so in particular `∀ n, le
///   (expSeriesPartial 2) (expSeriesPartial (Nat.add n 2))` (`Nat.le 2
///   (Nat.add n 2)` via `Nat.zero_le`/`Nat.add_le_add_right`).
/// - `expSeriesPartial 2` reduces, by the SAME `Kernel::def_eq` ι-chain
///   `creal_tests.rs`'s own `exp_series_partial_computes_its_first_few_values`
///   exercises, to the identical `Rat.mk` normal form as [`two`] — so
///   `CReal.le_refl` at `two`, ascribed at `le two (expSeriesPartial 2)`, type-
///   checks by that same defeq with no explicit rewrite needed.
///
/// Chaining those via `CReal.le_trans` gives `∀ n, le two (expSeriesPartial
/// (Nat.add n 2))`, exactly [`CRealPrelude::converges_lower_bound_shift`]'s
/// hypothesis at shift `s := 2`; applied with [`CRealPrelude::e_converges`]
/// closes `le two e`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_two_le_e(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let exp_term_const = d.kernel().const_(p.exp_term, vec![]);
    let exp_series_partial_const = d.kernel().const_(p.exp_series_partial, vec![]);
    let exp_term_nonneg_const = d.kernel().const_(p.exp_term_nonneg, vec![]);
    let e_const = d.kernel().const_(p.e, vec![]);
    let e_converges_proof = d.kernel().const_(p.e_converges, vec![]);
    let two_creal = two(d, p);
    let two_nat = d.num(2);

    // exp_series_partial_at_2 : expSeriesPartial 2 -- defeq to `two` (same
    // Kernel::def_eq chain `creal_tests.rs`'s concrete test already exercises).
    let exp_series_partial_at_2 = d.const_app(p.exp_series_partial, &[two_nat]);
    let base = d.lemma(p.le_refl, &[two_creal]);

    // h1_shift : ∀ n, le two (expSeriesPartial (Nat.add n 2)).
    let h1_shift = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let shifted_n = NatOps::add(d, n, two_nat);

        let zero_nat = d.num(0);
        let zero_le_n = d.lemma(p.rat.int.nat.zero_le, &[n]);
        let two_le_shifted = d.lemma(
            p.rat.int.nat.add_le_add_right,
            &[two_nat, zero_nat, n, zero_le_n],
        ); // Le (Nat.add 0 2) (Nat.add n 2) -- defeq to Le 2 (Nat.add n 2).

        let mono2 = d.const_app(
            p.sum_range_mono_outer,
            &[
                exp_term_const,
                exp_term_nonneg_const,
                two_nat,
                shifted_n,
                two_le_shifted,
            ],
        );
        // mono2 : le (sumRange expTerm 2) (sumRange expTerm shifted_n)
        //       = le (expSeriesPartial 2) (expSeriesPartial shifted_n), by delta.

        let exp_series_partial_shifted = d.const_app(p.exp_series_partial, &[shifted_n]);
        let step = d.lemma(
            p.le_trans,
            &[
                two_creal,
                exp_series_partial_at_2,
                exp_series_partial_shifted,
                base,
                mono2,
            ],
        );
        d.lam_fv(n_fv, nat, step)
    };

    let value = d.const_app(
        p.converges_lower_bound_shift,
        &[
            two_nat,
            two_creal,
            exp_series_partial_const,
            e_const,
            h1_shift,
            e_converges_proof,
        ],
    );
    let ty = cle(d, p, two_creal, e_const);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.two_le_e,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (neg zero) zero` — reproduced verbatim from `series.rs`'s own
/// private `neg_zero_equiv` (that module's own precedent for reusing a
/// sibling's private helper by reproduction rather than widening its
/// visibility, e.g. [`diagonal_seq`] above).
fn neg_zero_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]); // Equiv padded nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // Equiv nz padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // Equiv padded flipped
    let h3 = d.lemma(p.add_neg, &[zero_c]); // Equiv flipped zero_c
    let t1 = d.lemma(p.equiv_trans, &[nz, padded, flipped, step1, h2]);
    d.lemma(p.equiv_trans, &[nz, flipped, zero_c, t1, h3])
}

/// `CReal.e_le_four : le e four`, `four := mul two two`.
///
/// **Why `4`, not the classically sharper `3`.** The domination this file
/// already built is `expTerm n ≤ expDominant n := mul two (pow half n)` —
/// deliberately UNIFORM in `n`, including `n = 0`/`1` where the true ratio
/// `1/n! : (1/2)ⁿ` is `1:1` and `2:1`, not yet the geometric decay that makes
/// the bound tight. Summing the uniform bound therefore doubles a quantity
/// that is already loose by a factor of `2` at the first two terms: `Σ
/// expDominant = 2·Σ(1/2)ⁱ = 2·(2·(1−(1/2)ⁿ)) ≤ 4`. The classical `e ≤ 3`
/// bound splits off the first two terms (`1 + 1`) exactly and only bounds the
/// TAIL (`n ≥ 2`) by the geometric series, which needs a domination
/// re-indexed to start at `2`, not a direct application of
/// `sumRange_pow_half_closed_form` to the existing `expDominant`. That is
/// more than a corollary of what exists here and is not attempted in this
/// slice; `4` is what the current development actually supports.
///
/// Chain: `expSeriesPartial n = sumRange expTerm n ≤ sumRange expDominant n`
/// (`CReal.sumRange_le` at the pointwise bound `CReal.exp_term_le_dominant`)
/// `~ mul two (sumRange (pow half ·) n)` (`CReal.mul_sumRange`, symm) `~ mul
/// two (mul two (add one (neg (pow half n))))`
/// (`CReal.sumRange_pow_half_closed_form`, congruence) `~ mul four (add one
/// (neg (pow half n)))` (`CReal.mul_assoc`) `≤ mul four one` (`add one (neg
/// (pow half n)) ≤ one`, since `pow half n ≥ 0`, via
/// `CReal.neg_le_neg`/[`neg_zero_equiv_local`]/`CReal.add_le_add`) `~ four`
/// (`CReal.mul_one`). Holds at every `n` including `n = 0` — no shift needed,
/// unlike [`declare_two_le_e`] — then `CReal.converges_upper_bound` closes it
/// against [`CRealPrelude::e_converges`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_e_le_four(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let exp_term_const = d.kernel().const_(p.exp_term, vec![]);
    let exp_dominant_const = d.kernel().const_(p.exp_dominant, vec![]);
    let exp_series_partial_const = d.kernel().const_(p.exp_series_partial, vec![]);
    let exp_term_le_dominant_const = d.kernel().const_(p.exp_term_le_dominant, vec![]);
    let e_const = d.kernel().const_(p.e, vec![]);
    let e_converges_proof = d.kernel().const_(p.e_converges, vec![]);

    let zero_c = czero(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let two_creal = two(d, p);
    let half_val = half(d, p);
    let four = cmul(d, p, two_creal, two_creal);
    let four_nonneg = {
        let two_nonneg = two_nonneg_proof(d, p);
        d.lemma(
            p.mul_nonneg,
            &[two_creal, two_creal, two_nonneg, two_nonneg],
        )
    };

    // per_n : le (sumRange expTerm n) four, for a bound (Nat-level) `n`.
    let per_n = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        // Step A: le (sumRange expTerm n) (sumRange expDominant n).
        let ptwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_fv = d.fresh_fvar();
            let lt_ty = d.lt(i, n);
            let body = d.apply(exp_term_le_dominant_const, &[i]);
            let with_lt = d.lam_fv(lt_fv, lt_ty, body);
            d.lam_fv(i_fv, nat, with_lt)
        };
        let step_a = d.const_app(
            p.sum_range_le,
            &[exp_term_const, exp_dominant_const, n, ptwise],
        );

        // Equiv (sumRange expDominant n) (mul four y_n), y_n := add one (neg (pow half n)).
        let pow_half_fn_ = pow_half_fn(d, p);
        let sum_pow_half_n = d.const_app(p.sum_range, &[pow_half_fn_, n]);
        let sum_expdom_n = d.const_app(p.sum_range, &[exp_dominant_const, n]);
        let mul_two_sum = cmul(d, p, two_creal, sum_pow_half_n);
        let mul_sum_eq = d.lemma(p.mul_sum_range, &[two_creal, pow_half_fn_, n]);
        // mul_sum_eq : Equiv mul_two_sum sum_expdom_n (RHS defeq to `sumRange
        // expDominant n` via `expDominant`'s own delta-unfold).
        let mul_sum_eq_symm = d.lemma(p.equiv_symm, &[mul_two_sum, sum_expdom_n, mul_sum_eq]);

        let n_pow = cpow(d, p, half_val, n);
        let neg_pow = cneg(d, p, n_pow);
        let y_n = cadd(d, p, one_c, neg_pow);
        // mul_two_y := mul two y_n -- `sum_pow_half_closed_form`'s own RHS.
        let mul_two_y = cmul(d, p, two_creal, y_n);
        let closed_form = d.const_app(p.sum_pow_half_closed_form, &[n]);
        // closed_form : Equiv sum_pow_half_n mul_two_y
        let refl_two = d.lemma(p.equiv_refl, &[two_creal]);
        // mul_two_mul_two_y := mul two mul_two_y = mul two (mul two y_n) --
        // ONE MORE `mul two` wrapper than `mul_two_y` itself, since `mul_congr`
        // here scales `closed_form`'s WHOLE equivalence (sum_pow_half_n ~
        // mul_two_y) by the outer `two` already in `mul_two_sum`.
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

        let four_raw = cmul(d, p, four, y_n);
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
        let refl_one = d.lemma(p.le_refl, &[one_c]);
        let grown_y = d.lemma(
            p.add_le_add,
            &[one_c, one_c, neg_pow, zero_c, refl_one, neg_pow_le_zero],
        );
        let padded_one = cadd(d, p, one_c, zero_c);
        let add_zero_eq = d.lemma(p.add_zero, &[one_c]);
        let refl_y = d.lemma(p.equiv_refl, &[y_n]);
        let y_le_one = d.lemma(
            p.le_congr,
            &[y_n, y_n, padded_one, one_c, refl_y, add_zero_eq, grown_y],
        );

        // mul four y_n <= mul four one ~ four.
        let mul_le = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[four, y_n, one_c, four_nonneg, y_le_one],
        );
        let mul_four_one = cmul(d, p, four, one_c);
        let mul_one_eq = d.lemma(p.mul_one, &[four]);
        let refl_four_raw = d.lemma(p.equiv_refl, &[four_raw]);
        let four_raw_le_four = d.lemma(
            p.le_congr,
            &[
                four_raw,
                four_raw,
                mul_four_one,
                four,
                refl_four_raw,
                mul_one_eq,
                mul_le,
            ],
        );

        let eq_sum_four_symm = d.lemma(p.equiv_symm, &[sum_expdom_n, four_raw, eq_sum_four]);
        let refl_four = d.lemma(p.equiv_refl, &[four]);
        let sum_le_four = d.lemma(
            p.le_congr,
            &[
                four_raw,
                sum_expdom_n,
                four,
                four,
                eq_sum_four_symm,
                refl_four,
                four_raw_le_four,
            ],
        );

        let sum_expterm_n = d.const_app(p.sum_range, &[exp_term_const, n]);
        d.lemma(
            p.le_trans,
            &[sum_expterm_n, sum_expdom_n, four, step_a, sum_le_four],
        )
    };

    let ptwise_upper = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = per_n(d, n);
        d.lam_fv(n_fv, nat, body)
    };
    // ptwise_upper : ∀ n, le (expSeriesPartial n) four (by delta).

    let value = d.const_app(
        p.converges_upper_bound,
        &[
            exp_series_partial_const,
            e_const,
            four,
            ptwise_upper,
            e_converges_proof,
        ],
    );
    let ty = cle(d, p, e_const, four);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.e_le_four,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.three := add two one`.
fn three(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let t = two(d, p);
    let o = d.kernel().const_(p.one, vec![]);
    cadd(d, p, t, o)
}

/// `Equiv (mul two half) one`, i.e. `2 · (1/2) = 1` — the `CReal`-level lift
/// of [`rat_two_mul_half_eq_one`], extracted verbatim from `step2` inside
/// [`two_mul_one_sub_half_equiv_one`] so [`two_mul_pow_half_succ_equiv`] can
/// reuse it without re-deriving.
fn two_mul_half_equiv_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let t = two(d, p);
    let h = half(d, p);
    let (two_r, half_r, rat_eq) = rat_two_mul_half_eq_one(d, p);
    let mul_proof = d.lemma(p.of_rat_mul, &[two_r, half_r]);
    let mul_r = rmul(d, two_r, half_r);
    let one_r = rone(d, p.rat);
    let ofrat_eq = ofrat_congr(d, p, mul_r, one_r, rat_eq);
    let mul_two_half = cmul(d, p, t, h);
    let embed_mul_r = embed(d, p, mul_r);
    let one_c = d.kernel().const_(p.one, vec![]);
    echain(
        d,
        p,
        mul_two_half,
        &[(embed_mul_r, mul_proof), (one_c, ofrat_eq)],
    )
}

/// `Equiv (add half half) one`, i.e. `1/2 + 1/2 = 1` — the `CReal`-level lift
/// of [`rat_half_add_half_eq_one`], extracted verbatim from the `g_new` block
/// inside [`one_sub_half_equiv_half`] so the additive form of the index-shift
/// identity (used by [`exp_tail_partial_bound`]'s induction step) can reuse
/// it without re-deriving.
fn half_add_half_equiv_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let h = half(d, p);
    let (half_r, rat_eq) = rat_half_add_half_eq_one(d, p);
    let add_proof = d.lemma(p.of_rat_add, &[half_r, half_r]);
    let add_hh_r = radd(d, half_r, half_r);
    let one_r = rone(d, p.rat);
    let ofrat_eq = ofrat_congr(d, p, add_hh_r, one_r, rat_eq);
    let hh = cadd(d, p, h, h);
    let mid = embed(d, p, add_hh_r);
    let one_c = d.kernel().const_(p.one, vec![]);
    echain(d, p, hh, &[(mid, add_proof), (one_c, ofrat_eq)])
}

/// `Equiv (mul two (pow half (Nat.succ m))) (pow half m)` — the index-shift
/// identity behind the `e ≤ 3` split: `2 · (1/2)^(m+1) = (1/2)^m`. Built from
/// `pow_succ`'s ι-unfold (`pow half (succ m)` is DEFEQ to `mul (pow half m)
/// half`, never invoked as an explicit lemma — see the module's own
/// `two_le_e`/`e_le_four` precedent for relying on this kind of defeq
/// directly), `mul_comm`, `mul_assoc`, and [`two_mul_half_equiv_one`].
///
/// Chain: `mul two (mul (pow half m) half) ~ mul two (mul half (pow half m))`
/// (`mul_comm`) `~ mul (mul two half) (pow half m)` (`mul_assoc`, symm)
/// `~ mul one (pow half m)` (`two_mul_half_equiv_one`) `~ mul (pow half m)
/// one` (`mul_comm`) `~ pow half m` (`mul_one`).
fn two_mul_pow_half_succ_equiv(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let t = two(d, p);
    let h = half(d, p);
    let pow_m = cpow(d, p, h, m);
    let mul_pow_m_half = cmul(d, p, pow_m, h); // defeq to `pow half (succ m)`

    let comm1 = d.lemma(p.mul_comm, &[pow_m, h]); // Equiv (mul pow_m h) (mul h pow_m)
    let refl_two = d.lemma(p.equiv_refl, &[t]);
    let mul_h_pow_m = cmul(d, p, h, pow_m);
    let step1 = d.lemma(
        p.mul_congr,
        &[t, t, mul_pow_m_half, mul_h_pow_m, refl_two, comm1],
    );
    // step1 : Equiv (mul two mul_pow_m_half) (mul two mul_h_pow_m)

    let mul_two_h = cmul(d, p, t, h);
    let assoc = d.lemma(p.mul_assoc, &[t, h, pow_m]);
    // assoc : Equiv (mul (mul two h) pow_m) (mul two mul_h_pow_m)
    let mul_two_h_pow_m = cmul(d, p, t, mul_h_pow_m);
    let assoc_symm_lhs = cmul(d, p, mul_two_h, pow_m);
    let assoc_symm = d.lemma(p.equiv_symm, &[assoc_symm_lhs, mul_two_h_pow_m, assoc]);
    // assoc_symm : Equiv (mul two mul_h_pow_m) assoc_symm_lhs

    let two_half_one = two_mul_half_equiv_one(d, p);
    // two_half_one : Equiv (mul two half) one
    let one_c = d.kernel().const_(p.one, vec![]);
    let refl_pow_m = d.lemma(p.equiv_refl, &[pow_m]);
    let step3 = d.lemma(
        p.mul_congr,
        &[mul_two_h, one_c, pow_m, pow_m, two_half_one, refl_pow_m],
    );
    // step3 : Equiv assoc_symm_lhs (mul one pow_m)

    let mul_one_pow_m = cmul(d, p, one_c, pow_m);
    let comm2 = d.lemma(p.mul_comm, &[one_c, pow_m]);
    // comm2 : Equiv (mul one pow_m) (mul pow_m one)
    let mul_pow_m_one = cmul(d, p, pow_m, one_c);
    let mo = d.lemma(p.mul_one, &[pow_m]);
    // mo : Equiv (mul pow_m one) pow_m

    let start = cmul(d, p, t, mul_pow_m_half);
    echain(
        d,
        p,
        start,
        &[
            (mul_two_h_pow_m, step1),
            (assoc_symm_lhs, assoc_symm),
            (mul_one_pow_m, step3),
            (mul_pow_m_one, comm2),
            (pow_m, mo),
        ],
    )
}

/// `le (expTerm (Nat.add k 2)) (pow half (Nat.add k 1))` — the shifted-by-2
/// domination the classical `e ≤ 3` split needs, for a BOUND `k`. From
/// [`CRealPrelude::exp_term_le_dominant`] at `k+2` (`le (expTerm (k+2))
/// (expDominant (k+2))`, `expDominant (k+2)` defeq `mul two (pow half
/// (k+2))`, `k+2` defeq `succ (k+1)`) rewritten along
/// [`two_mul_pow_half_succ_equiv`] at `m := k+1`.
///
/// No new `Nat`-level fact: unlike [`CRealPrelude::exp_term_le_geom`]'s own
/// `2ⁿ ≤ 2·n!`, this is pure `CReal` algebra reusing an already-proved
/// pointwise bound.
fn exp_term_shift2_le_pow_half(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let k2 = NatOps::add(d, k, two_nat);
    let k1 = NatOps::add(d, k, one_nat);

    let exp_term_le_dominant_const = d.kernel().const_(p.exp_term_le_dominant, vec![]);
    let base = d.apply(exp_term_le_dominant_const, &[k2]);
    // base : le (expTerm k2) (expDominant k2), defeq le (expTerm k2) (mul two (pow half k2))

    let equiv_shift = two_mul_pow_half_succ_equiv(d, p, k1);
    // equiv_shift : Equiv (mul two (pow half (succ k1))) (pow half k1)
    // succ k1 defeq k2 (k1 = add k 1 defeq succ k, k2 = add k 2 defeq succ (succ k))

    let exp_term_const = d.kernel().const_(p.exp_term, vec![]);
    let exp_term_k2 = d.apply(exp_term_const, &[k2]);
    let refl_lhs = d.lemma(p.equiv_refl, &[exp_term_k2]);

    let t = two(d, p);
    let h = half(d, p);
    let pow_k2 = cpow(d, p, h, k2);
    let mul_two_pow_k2 = cmul(d, p, t, pow_k2);
    let pow_k1 = cpow(d, p, h, k1);

    d.lemma(
        p.le_congr,
        &[
            exp_term_k2,
            exp_term_k2,
            mul_two_pow_k2,
            pow_k1,
            refl_lhs,
            equiv_shift,
            base,
        ],
    )
}

/// `∀ k, le (add (sumRange expTerm (Nat.add k 2)) (pow half k)) three` — the
/// telescoping invariant behind `e ≤ 3`: `Σ_{n<k+2} 1/n! + (1/2)^k ≤ 3`,
/// tight at `k = 0` (`2 + 1 = 3`, both sides exact) and closed at every step
/// by [`exp_term_shift2_le_pow_half`] plus the ADDITIVE form of the same
/// index-shift identity `two_mul_pow_half_succ_equiv` proves multiplicatively
/// (`pow half (k+1) + pow half (k+1) ~ pow half k`, via `left_distrib` +
/// [`half_add_half_equiv_one`] + `mul_one`, since `pow half (succ k)` is
/// defeq `mul (pow half k) half`).
///
/// Induction on `k`. Base: `sumRange expTerm 2 + pow half 0` is defeq
/// `add two one = three` (`sumRange expTerm 2` reduces to `two` by the same
/// `Kernel::def_eq` chain [`declare_two_le_e`]'s own concrete test exercises;
/// `pow half 0` reduces to `one` by `pow_zero`'s ι-reduction) — `le_refl`
/// alone closes it.
fn exp_tail_partial_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    three_c: ExprId,
) -> ExprId {
    let exp_term_const = d.kernel().const_(p.exp_term, vec![]);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let two_nat = d.num(2);
        let x2 = NatOps::add(d, x, two_nat);
        let sum_x2 = d.const_app(p.sum_range, &[exp_term_const, x2]);
        let h = half(d, p);
        let pow_x = cpow(d, p, h, x);
        let lhs = cadd(d, p, sum_x2, pow_x);
        cle(d, p, lhs, three_c)
    };

    let base_case = |d: &mut IntDev<'_>| -> ExprId { d.lemma(p.le_refl, &[three_c]) };

    let step_case = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let two_nat = d.num(2);
        let j2 = NatOps::add(d, j, two_nat);
        let sum_j2 = d.const_app(p.sum_range, &[exp_term_const, j2]);
        let h = half(d, p);
        let pow_j = cpow(d, p, h, j);
        let succ_j = d.succ(j);
        let pow_succ_j = cpow(d, p, h, succ_j); // = C, defeq mul pow_j half
        let exp_term_j2 = d.apply(exp_term_const, &[j2]); // = B

        let l1 = exp_term_shift2_le_pow_half(d, p, j);
        // l1 : le (expTerm j2) (pow half (add j 1)), defeq le exp_term_j2 pow_succ_j

        let le_refl_c = d.lemma(p.le_refl, &[pow_succ_j]);
        let step_le1 = d.lemma(
            p.add_le_add,
            &[
                exp_term_j2,
                pow_succ_j,
                pow_succ_j,
                pow_succ_j,
                l1,
                le_refl_c,
            ],
        );
        // step_le1 : le (add exp_term_j2 pow_succ_j) (add pow_succ_j pow_succ_j)

        // (add pow_succ_j pow_succ_j) ~ pow_j, via left_distrib symm + half_add_half_equiv_one + mul_one.
        let mul_pj_half = cmul(d, p, pow_j, h);
        let ld = d.lemma(p.left_distrib, &[pow_j, h, h]);
        // ld : Equiv (mul pow_j (add half half)) (add mul_pj_half mul_pj_half)
        let hh = cadd(d, p, h, h);
        let mul_pj_addhh = cmul(d, p, pow_j, hh);
        let ld_symm_lhs = cadd(d, p, mul_pj_half, mul_pj_half);
        let ld_symm = d.lemma(p.equiv_symm, &[mul_pj_addhh, ld_symm_lhs, ld]);
        // ld_symm : Equiv ld_symm_lhs mul_pj_addhh

        let hh_one = half_add_half_equiv_one(d, p);
        let refl_pj = d.lemma(p.equiv_refl, &[pow_j]);
        let one_c = d.kernel().const_(p.one, vec![]);
        let congr1 = d.lemma(p.mul_congr, &[pow_j, pow_j, hh, one_c, refl_pj, hh_one]);
        // congr1 : Equiv mul_pj_addhh (mul pow_j one)
        let mul_pj_one = cmul(d, p, pow_j, one_c);
        let mo = d.lemma(p.mul_one, &[pow_j]); // Equiv mul_pj_one pow_j

        let cc_equiv_pj = echain(
            d,
            p,
            ld_symm_lhs,
            &[(mul_pj_addhh, ld_symm), (mul_pj_one, congr1), (pow_j, mo)],
        );
        // cc_equiv_pj : Equiv (add pow_succ_j pow_succ_j) pow_j (ld_symm_lhs defeq add pow_succ_j pow_succ_j)

        let add_c_c = cadd(d, p, pow_succ_j, pow_succ_j);
        let bc = cadd(d, p, exp_term_j2, pow_succ_j);
        let refl_bc = d.lemma(p.equiv_refl, &[bc]);
        let step_bc_le = d.lemma(
            p.le_congr,
            &[bc, bc, add_c_c, pow_j, refl_bc, cc_equiv_pj, step_le1],
        );
        // step_bc_le : le (add exp_term_j2 pow_succ_j) pow_j

        let le_refl_sum = d.lemma(p.le_refl, &[sum_j2]);
        let step2 = d.lemma(
            p.add_le_add,
            &[sum_j2, sum_j2, bc, pow_j, le_refl_sum, step_bc_le],
        );
        // step2 : le (add sum_j2 bc) (add sum_j2 pow_j)

        let ih_lhs = cadd(d, p, sum_j2, pow_j);
        let add_sum_j2_bc = cadd(d, p, sum_j2, bc);
        let combined = d.lemma(p.le_trans, &[add_sum_j2_bc, ih_lhs, three_c, step2, ih]);
        // combined : le add_sum_j2_bc three_c

        let assoc = d.lemma(p.add_assoc, &[sum_j2, exp_term_j2, pow_succ_j]);
        // assoc : Equiv goal_lhs add_sum_j2_bc
        let sum_j2_plus_exp_term_j2 = cadd(d, p, sum_j2, exp_term_j2);
        let goal_lhs = cadd(d, p, sum_j2_plus_exp_term_j2, pow_succ_j);
        let assoc_symm = d.lemma(p.equiv_symm, &[goal_lhs, add_sum_j2_bc, assoc]);
        // assoc_symm : Equiv add_sum_j2_bc goal_lhs

        let refl_three = d.lemma(p.equiv_refl, &[three_c]);
        d.lemma(
            p.le_congr,
            &[
                add_sum_j2_bc,
                goal_lhs,
                three_c,
                three_c,
                assoc_symm,
                refl_three,
                combined,
            ],
        )
        // result : le goal_lhs three_c, goal_lhs defeq sumRange expTerm (add (succ j) 2)
    };

    d.induct(&motive, &base_case, &step_case, k)
}

/// `le zero three`.
fn zero_le_three(d: &mut IntDev<'_>, p: CRealPrelude, three_c: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let two_c = two(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let two_nn = two_nonneg_proof(d, p);
    let zlt1 = d.lemma(p.zero_lt_one, &[]);
    let one_nn = d.lemma(p.le_of_lt, &[zero_c, one_c, zlt1]);
    let step = d.lemma(
        p.add_le_add,
        &[zero_c, two_c, zero_c, one_c, two_nn, one_nn],
    );
    // step : le (add zero zero) (add two one) = le (add zero zero) three_c
    let az = d.lemma(p.add_zero, &[zero_c]); // Equiv (add zero zero) zero
    let refl_three = d.lemma(p.equiv_refl, &[three_c]);
    let zero_plus_zero = cadd(d, p, zero_c, zero_c);
    d.lemma(
        p.le_congr,
        &[
            zero_plus_zero,
            zero_c,
            three_c,
            three_c,
            az,
            refl_three,
            step,
        ],
    )
}

/// `le one three`.
fn one_le_three(d: &mut IntDev<'_>, p: CRealPrelude, three_c: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let two_c = two(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let two_nn = two_nonneg_proof(d, p);
    let refl_one = d.lemma(p.le_refl, &[one_c]);
    let step = d.lemma(
        p.add_le_add,
        &[zero_c, two_c, one_c, one_c, two_nn, refl_one],
    );
    // step : le (add zero one) (add two one) = le (add zero one) three_c
    let comm = d.lemma(p.add_comm, &[zero_c, one_c]);
    let az = d.lemma(p.add_zero, &[one_c]);
    let add_zero_one = cadd(d, p, zero_c, one_c);
    let add_one_zero = cadd(d, p, one_c, zero_c);
    let eq_chain = echain(d, p, add_zero_one, &[(add_one_zero, comm), (one_c, az)]);
    let refl_three = d.lemma(p.equiv_refl, &[three_c]);
    d.lemma(
        p.le_congr,
        &[
            add_zero_one,
            one_c,
            three_c,
            three_c,
            eq_chain,
            refl_three,
            step,
        ],
    )
}

/// `∀ n, le (sumRange expTerm n) three` — the top-level bound, over ALL `n`
/// (not just `n ≥ 2`), by a NESTED case split on `{0, 1, k+2}`: unlike
/// [`declare_e_le_four`]'s `per_n` (one uniform algebraic bound at every
/// `n`), the classical `e ≤ 3` argument genuinely kinks at index `2`
/// (`expTerm 0 = expTerm 1 = 1`, not yet geometric), so no single formula
/// dominates `expTerm` from `n = 0` while also being tight enough to sum to
/// `3`. `n = 0`/`n = 1` close directly ([`zero_le_three`]/[`one_le_three`]);
/// `n = k + 2` closes via [`exp_tail_partial_bound`] with the nonnegative
/// `pow half k` term dropped ([`CRealPrelude::pow_nonneg`] + `add_zero`).
fn e_le_three_per_n(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId, three_c: ExprId) -> ExprId {
    let exp_term_const = d.kernel().const_(p.exp_term, vec![]);

    let outer_motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sum_x = d.const_app(p.sum_range, &[exp_term_const, x]);
        cle(d, p, sum_x, three_c)
    };
    let outer_base = |d: &mut IntDev<'_>| -> ExprId { zero_le_three(d, p, three_c) };
    let outer_step = |d: &mut IntDev<'_>, m: ExprId, _ih: ExprId| -> ExprId {
        let inner_motive = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
            let succ_y = d.succ(y);
            let sum_succ_y = d.const_app(p.sum_range, &[exp_term_const, succ_y]);
            cle(d, p, sum_succ_y, three_c)
        };
        let inner_base = |d: &mut IntDev<'_>| -> ExprId { one_le_three(d, p, three_c) };
        let inner_step = |d: &mut IntDev<'_>, k: ExprId, _ih2: ExprId| -> ExprId {
            let tail = exp_tail_partial_bound(d, p, k, three_c);
            // tail : le (add (sumRange expTerm (add k 2)) (pow half k)) three_c
            let two_nat = d.num(2);
            let k2 = NatOps::add(d, k, two_nat);
            let sum_k2 = d.const_app(p.sum_range, &[exp_term_const, k2]);
            let h = half(d, p);
            let pow_k = cpow(d, p, h, k);
            let half_nn = half_nonneg_proof(d, p);
            let pow_nn = d.lemma(p.pow_nonneg, &[h, half_nn, k]);
            // pow_nn : le zero pow_k

            let zero_c = czero(d, p);
            let le_refl_sum = d.lemma(p.le_refl, &[sum_k2]);
            let step_le = d.lemma(
                p.add_le_add,
                &[sum_k2, sum_k2, zero_c, pow_k, le_refl_sum, pow_nn],
            );
            // step_le : le (add sum_k2 zero) (add sum_k2 pow_k)
            let sum_k2_pad = cadd(d, p, sum_k2, zero_c);
            let sum_k2_pow_k = cadd(d, p, sum_k2, pow_k);
            let combined = d.lemma(
                p.le_trans,
                &[sum_k2_pad, sum_k2_pow_k, three_c, step_le, tail],
            );
            // combined : le sum_k2_pad three_c

            let az = d.lemma(p.add_zero, &[sum_k2]); // Equiv sum_k2_pad sum_k2
            let refl_three = d.lemma(p.equiv_refl, &[three_c]);
            d.lemma(
                p.le_congr,
                &[
                    sum_k2_pad, sum_k2, three_c, three_c, az, refl_three, combined,
                ],
            )
            // result : le sum_k2 three_c, sum_k2 defeq sumRange expTerm (succ (succ k))
        };
        d.induct(&inner_motive, &inner_base, &inner_step, m)
    };

    d.induct(&outer_motive, &outer_base, &outer_step, n)
}

/// `CReal.e_le_three : le e three`, `three := add two one` — the sharpened
/// upper bound. See [`CRealPrelude::e_le_three`]'s own doc for the
/// mathematics and why the split is worth its cost over [`declare_e_le_four`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_e_le_three(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let exp_series_partial_const = d.kernel().const_(p.exp_series_partial, vec![]);
    let e_const = d.kernel().const_(p.e, vec![]);
    let e_converges_proof = d.kernel().const_(p.e_converges, vec![]);

    let three_c = three(d, p);

    let ptwise_upper = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = e_le_three_per_n(d, p, n, three_c);
        d.lam_fv(n_fv, nat, body)
    };
    // ptwise_upper : ∀ n, le (expSeriesPartial n) three (by delta).

    let value = d.const_app(
        p.converges_upper_bound,
        &[
            exp_series_partial_const,
            e_const,
            three_c,
            ptwise_upper,
            e_converges_proof,
        ],
    );
    let ty = cle(d, p, e_const, three_c);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.e_le_three,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.e`, `CReal.e_converges`, `CReal.two_le_e`,
/// `CReal.e_le_four` and `CReal.e_le_three`. Run **after**
/// [`declare_exp_convergence`] (shares
/// `exp_dominant_cauchy_body_concrete`'s dependencies:
/// `geomCauchy_ordered_half`, `exp_term_abs_le_dominant`,
/// `sum_range_cauchy_dominated_ordered_normalized`, `regular_of_scaled_cauchy`
/// — all declared well before `exponential`'s own functions run).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_e_family(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    // `e_ingredients` runs EXACTLY ONCE here, and the resulting `(raw,
    // k_final, exp_series_partial_body)` `ExprId`s are threaded into BOTH
    // `declare_e` and `declare_e_converges` -- NOT re-derived by a second,
    // independent call. This alone is NOT what fixes the stack overflow
    // below (an earlier hypothesis, disproven by measurement: sharing these
    // `ExprId`s and even routing the whole proof through a LOCALLY-built
    // `mk(...)` value instead of the named `e` both left the overflow fully
    // reproducible) -- see `declare_e_converges`'s own doc for the actual
    // root cause and fix (build generically over a BOUND `K`, substitute the
    // concrete `k_final` only in the very last step). Sharing is kept
    // because it is still the right hygiene (one derivation, not two) and
    // because `declare_two_le_e`/`declare_e_le_four` need the SAME `e` the
    // shared `k_final` builds, via `CRealPrelude::e_converges`.
    let (raw, k_final, exp_series_partial_body) = e_ingredients(d, p);
    declare_e(d, p, raw, k_final, exp_series_partial_body)?;
    declare_e_converges(d, p, raw, k_final, exp_series_partial_body)?;
    declare_two_le_e(d, p)?;
    declare_e_le_four(d, p)?;
    declare_e_le_three(d, p)
}
