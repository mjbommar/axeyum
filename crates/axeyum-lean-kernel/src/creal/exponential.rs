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
//! **This file still does not establish `Cauchy (sumRange expTerm)`, and so
//! still does not build `CReal.e`.** That is genuinely the next step, and
//! separately: `CReal.sumRange_cauchy_dominated_ordered_normalized`
//! (`series.rs`) already gives a raw, UNWRAPPED pointwise Cauchy-shaped
//! bound for one ordered pair `a ≤ b` from exactly this kind of domination
//! (`∀x, le (abs (f x)) (g x)`, plus a Cauchy witness for `sumRange g` in the
//! same raw form) — the `abs` needs `expTerm`/the geometric bound each shown
//! nonnegative first (an easy `Rat`-level fact via [`normalize`]'s own
//! `num`/`den`, not yet built here), and the `Cauchy (sumRange g)` witness
//! for THIS `g` (route (b)'s raw-normalize sequence) still needs its own
//! tail-sum argument — `geom_pair_within`/`geom_tail_bounded_div`
//! (`geometric.rs`, route (a)'s machinery) do not apply to it directly since
//! they are built for `CReal.pow`-based sequences, and bridging `g` to a
//! `CReal.pow`-based sequence hits the same `Rat.pow`-vs-`Rat.normalize`
//! representation gap route (a) was blocked on (see below) unless a fresh
//! `Rat`-level equality `Rat.pow (natDivSucc 1 1) n = Rat.normalize 1 (2ⁿ) _`
//! is built first (a clean, bounded induction via `normalize_mul_normalize`,
//! not attempted here). Once *some* Cauchy witness for `sumRange g` exists in
//! the raw pointwise form, doing the `Nat.le_total` split on top of
//! `sum_range_cauchy_dominated_ordered_normalized` (mirroring what
//! `sum_range_cauchy_of_dominated` does internally, but stopping short of its
//! final `Exists.intro`) gives a concrete-`K` pointwise Cauchy bound for
//! `sumRange expTerm`, which is exactly the shape
//! [`CRealPrelude::regular_of_scaled_cauchy`] consumes to build `CReal.e :=
//! CReal.mk (speedup (diagonal expSeriesPartial) K) (...)` directly — see
//! `creal/convergence.rs` for `regular_of_scaled_cauchy`/`speedup`, and
//! `creal/completeness.rs` for the `CReal.mk`-on-an-explicit-sequence pattern
//! this needs (an `Exists`-elimination into `CReal` data is not available in
//! this kernel; `converges_of_cauchy`'s own `∃ L, …` cannot be unwrapped for
//! this purpose).
//!
//! What follows below is this file's original diagnosis, from before the
//! domination bound existed, of what a route (a)/(b) choice would need for
//! domination specifically — kept because the same representation gap it
//! names (`Rat.pow` vs `Rat.normalize`) is exactly what still blocks the
//! Cauchy witness above, on the route (a) side: (a) relate `CReal.pow
//! (ofRat (1/2)) n` to `ofRat ((1/2)^n)` via `of_rat_mul`/`pow_congr`
//! induction (this bridge, `CReal.ofRat_pow`, now EXISTS —
//! `creal/geometric.rs` — so route (a)'s domination half was in fact
//! buildable; what remained missing for it was `Rat.pow (1/2) n`'s
//! relationship to a `Rat.normalize`d denominator, not an order lemma); or
//! (b) skip `CReal.pow` and `Rat.normalize` a genuinely rational geometric
//! bound `g n := ofRat (2 / 2ⁿ)` directly (the route this file's domination
//! bound now takes).

use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, embed};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::RatPrelude;
use crate::rat_prelude::ops::{den, den_z, iregroup4, normalize, num};

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
    declare_exp_term_le_geom(d, p)
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
