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
//! **A genuinely new fact changes that module's own diagnosis, though.**
//! `geometric.rs` names "no lemma bounding `CReal.pow` above by a
//! `natDivSucc` rational" as one of three pieces missing to close
//! `CReal.geom_cauchy` via `geom_pair_within` (`geom_tail_within_le` +
//! `geom_pair_within` are landed there; the harmonic bound on the deferred
//! `seq Yₘ b` leaf was the blocker). That bound **already exists** —
//! `CRealPrelude::pow_half_le_nat_div_succ : ∀n, le (pow half n) (ofRat
//! (natDivSucc 1 n))`, built in `geometric.rs` itself for the IVT bisection
//! modulus (`ivt.rs`) — for the concrete base `1/2` this file needs. So
//! `geom_pair_within`'s `Nat.le_total` split plus fusing its five leaves
//! (including `seq Yₘ b`, `Yₘ := pow half m * inv (add one (neg half))`) is
//! newly unblocked. It still goes through `CReal.inv`/`PosBound` to build
//! `Yₘ` (`PosBound half 1` is easy — `half`'s own sample is the constant
//! `1/2` — but it is `inv`, which the domination bound above deliberately
//! never touches). Two live options for the next lane, neither attempted
//! here: finish `geom_cauchy` through `inv` at this one concrete base (a
//! bounded, contained use, not a new general reliance on `inv`), or build a
//! from-scratch inv-free Cauchy witness directly off
//! `sumRange_pow_half_closed_form` mirroring `series.rs`'s own
//! index-bookkeeping. Either way, scaling the resulting `Cauchy (sumRange
//! (pow half ·))` up to `Cauchy (sumRange expDominant)` (the `mul two`
//! wrapper) is a further step, not free, because of the same `CReal.mul`
//! index-shift.
//!
//! Separately, once *some* `Cauchy (sumRange expDominant)` witness exists (by
//! either route above): `CReal.sumRange_cauchy_dominated_ordered_normalized`
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

use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, div_succ, embed, equiv};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::RatPrelude;
use crate::rat_prelude::ops::{
    den, den_z, iregroup4, nat_rewrite_prop, normalize, num, radd, rat_eq_rewrite, rchain, rmul,
    rone, rpow,
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

/// `CReal.exp_dominant_nonneg : ∀ n, le zero (expDominant n)` — from
/// [`CRealPrelude::mul_nonneg`], `0 ≤ two` and [`CRealPrelude::pow_nonneg`]
/// at `0 ≤ half` (both via `Rat.zero_le_natDivSucc` + `CReal.of_rat_le`).
fn declare_exp_dominant_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let rp = p.rat;
    let zero_rat = crate::rat_prelude::ops::rzero(d, rp);

    // `0 ≤ half`, via `Rat.zero_le_natDivSucc 1 1` and `CReal.of_rat_le`.
    let one_nat = d.num(1);
    let half_le_zero = d.lemma(rp.zero_le_nat_div_succ, &[one_nat, one_nat]);
    let hr = half_rat(d, p);
    let half_nonneg = d.lemma(p.of_rat_le, &[zero_rat, hr, half_le_zero]);

    // `0 ≤ two`: `two_r := normalize 2 1 h1` (the SAME construction
    // [`two`]/[`exp_dominant_at`] use), by `expterm_nonneg_proof`'s
    // cross-multiplication technique with numerator `2` and denominator `1`.
    let h = half(d, p);
    let (two_r, two_z, h1) = two_normalize(d, p);
    let t = embed(d, p, two_r);
    let two_nonneg = {
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
    };

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
