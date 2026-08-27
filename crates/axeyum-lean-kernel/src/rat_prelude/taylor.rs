//! The finite Taylor expansion identity for polynomials over `ℚ` — the
//! **algebraic core** of Taylor's theorem (ADR-0603 row 3), which needs no
//! analysis, no limits, and no mean-value argument: for a polynomial `p` and
//! a center `a`,
//!
//! ```text
//! p(x) = Σ_{k=0}^{deg p} (p⁽ᵏ⁾(a) / k!) · (x − a)ᵏ
//! ```
//!
//! is a finite algebraic sum identity. [`crate::axeyum_cas::taylor`] (read:
//! `crates/axeyum-cas/src/taylor.rs`) proves the full **analytic** Taylor
//! theorem with Lagrange remainder — a named witness `ξ` produced via
//! generalized Rolle, CAS-internal because it needs the same real-analysis
//! machinery `crate::mvt`/`crate::extremum` already cannot reach
//! constructively. This file is the kernel half: the part of that same
//! mathematics provable directly, over `Rat.polyEval`
//! (`rat_prelude/polynomial.rs`), by pure ring algebra.
//!
//! # What is proved, and at what generality
//!
//! - [`RatPrelude::pow_one`]: `pow a (succ zero) = a` — the missing `n = 1`
//!   instance of `Rat.pow`'s own equations. General, for every `a`.
//! - [`RatPrelude::add_sub_cancel_left`]: `a + (x − a) = x`. General, for
//!   every `a`, `x` — reusable anywhere a basepoint needs to cancel out of a
//!   residue, independent of Taylor's theorem entirely.
//! - [`RatPrelude::sq_sub_sq`]: `x² − a² = (x − a)·(x + a)` —
//!   difference-of-squares, the reusable algebraic core of the **factor
//!   theorem** at degree 2 (`x² − a²` factors through `x − a`, the same
//!   move that makes `p(x) − p(a)` divisible by `x − a` for any polynomial
//!   `p`). General, for every `x`, `a` — not itself used by
//!   [`RatPrelude::taylor_deg1`] (degree 1 has no square to factor) but kept
//!   here as the building block the degree-2 rung needs next.
//! - [`RatPrelude::poly_eval_deg1`]: the closed form for evaluating a
//!   degree-≤1 polynomial, `polyEval (coeff2 c0 c1) 2 t = c0 + c1·t`, where
//!   `coeff2 c0 c1` is the coefficient function built inline by `Nat.rec`
//!   (`i = 0 ↦ c0`, `i ≥ 1 ↦ c1`) — the same "inline `Nat.rec`, no named
//!   cast" move `bernoulli.rs`'s `L` uses, since nothing else in this
//!   prelude needs to name a two-term coefficient function.
//! - [`RatPrelude::taylor_deg1`]: the Taylor expansion identity itself, at
//!   degree 1 — `p(x) = p(a) + c1·(x − a)` for `p = c0 + c1·X` — exact, for
//!   every `c0`, `c1`, `x`, `a`, no remainder (a degree-≤1 polynomial's own
//!   degree-1 Taylor polynomial is itself).
//!
//! # Why this stops at degree 1, and precisely what blocks degree ≥ 2
//!
//! [`polynomial.rs`]'s own module doc already names the obstacle for
//! `Rat.polyEval_mul` (the Cauchy product): reindexing a double sum over
//! `Rat.sumRange` needs a diagonal/rectangle lemma this prelude has not
//! ported from `nat_prelude::diagonal`/`nat_prelude::rectangle`. The
//! **general-degree** factor theorem — `p(x) − p(a) = (x − a)·q(x)` for a
//! `polyEval`-represented `p` of arbitrary degree bound `n` — needs exactly
//! the same machinery: `q`'s `k`-th coefficient is
//! `Σ_{i=k+1}^{n-1} c(i)·a^{i-1-k}`, a double sum over `Rat.sumRange` that
//! cannot be built, reindexed, or evaluated without it. This is not a
//! failed proof attempt; it is the same documented gap, hit from a second
//! direction. A **fixed, low** degree sidesteps it entirely (degree 1's
//! `q(x) = c1` needs no sum at all; degree 2's needs one application of
//! [`RatPrelude::sq_sub_sq`], not a reindexing lemma) — which is exactly why
//! this file lands the low-degree rungs and stops there rather than forcing
//! an unverified general statement. Porting the diagonal/rectangle
//! machinery to `ℚ` is the prerequisite for degree ≥ 3 and for the
//! general-degree statement; it is future work, not attempted here.
//!
//! A **separate**, independent obstacle would face any general-degree
//! *derivative-coefficient* formulation (`p⁽ᵏ⁾(a)/k!` for symbolic `k`):
//! this prelude has no `Nat → ℚ` cast (`polynomial.rs`'s own module doc
//! notes the absence), so writing `k!` as a `Rat` for a symbolic `k` has no
//! target type to land in without first admitting one. The low-degree
//! rungs avoid this too — `c1` and `(c1, c2)` are already the derivative
//! coefficients directly, with no cast or factorial needed, since `1! = 1`
//! and `2!·(1/2) = 1` are absorbed into the concrete arithmetic
//! (`c1 + c2 + c2` rather than `c1 + 2·c2`, avoiding a numeral literal `2`
//! entirely).

use super::RatPrelude;
use super::ops::{
    radd, rat_ty, rchain, rcongr, req, rmul, rneg, rone, rpoly_eval, rpow, rsymm, rtrans, rzero,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// `Rat.sub a b` — this file's only user of `p.sub` directly (everything
/// else in `rat_prelude` either builds `Rat.sub` itself or never needs it),
/// so no shared helper for it exists in [`super::ops`].
fn rsub(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.sub, &[a, b])
}

/// Declare every theorem in this file.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_taylor(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_pow_one(d, p)?;
    declare_add_sub_cancel_left(d, p)?;
    declare_sq_sub_sq(d, p)?;
    declare_poly_eval_deg1(d, p)?;
    declare_taylor_deg1(d, p)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Small reusable lemmas the expansion needs.
// ---------------------------------------------------------------------------

/// `Rat.pow_one : ∀ a, Eq Rat (pow a (succ zero)) a`.
///
/// `pow a (succ zero) ≡ mul (pow a zero) a ≡ mul one a` by pure `ι`/`β`
/// reduction (`Rat.pow`'s own `Nat.rec`, exactly as `pow_succ`/`pow_zero`
/// unfold) — the remaining `mul one a = a` needs `mul_comm` then `mul_one`,
/// since this prelude has no `one_mul`.
fn declare_pow_one(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);

    let lhs = rpow(d, p, a, one_n);
    let one_r = rone(d, p);

    // pow a (succ zero) ≡ mul (pow a zero) a ≡ mul one a — pure reduction,
    // so `pow_succ` applied here already yields (up to defeq) `mul one a`.
    let h1 = d.lemma(p.pow_succ, &[a, zero_n]);
    let mul_one_a = rmul(d, one_r, a);

    let h2 = d.lemma(p.mul_comm, &[one_r, a]);
    let mul_a_one = rmul(d, a, one_r);

    let h3 = d.lemma(p.mul_one, &[a]);

    let (_e, proof) = rchain(d, lhs, &[(mul_one_a, h1), (mul_a_one, h2), (a, h3)]);

    let stmt = req(d, lhs, a);
    let ty = d.pi_fv(a_fv, carrier, stmt);
    let value = d.lam_fv(a_fv, carrier, proof);
    d.declare_theorem(p.pow_one, ty, value)
}

/// `Rat.add_sub_cancel_left : ∀ a x, Eq Rat (add a (sub x a)) x`.
///
/// `sub x a` unfolds (by definition, `Rat.sub a b := add a (neg b)`) to
/// `add x (neg a)`, so the whole proof is built in terms of `add`/`neg` —
/// `(a + x) + (−a) = (x + a) + (−a) = x + (a + (−a)) = x + 0 = x` — and the
/// declared statement (which mentions `Rat.sub`) is defeq to it for free.
fn declare_add_sub_cancel_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let sub_x_a = rsub(d, p, x, a);
    let neg_a = rneg(d, a);
    let u = radd(d, x, neg_a); // defeq to sub_x_a
    let start = radd(d, a, u); // defeq to the declared `add a (sub x a)`
    let declared_start = radd(d, a, sub_x_a);

    // (a + x) + (−a) = a + (x + (−a)) = a + u.
    let ax = radd(d, a, x);
    let h1 = d.lemma(p.add_assoc, &[a, x, neg_a]);
    let ax_neg_a = radd(d, ax, neg_a);
    let h1s = rsymm(d, ax_neg_a, start, h1); // start = ax_neg_a

    // a + x = x + a, lifted through `+ (−a)`.
    let xa = radd(d, x, a);
    let h2 = d.lemma(p.add_comm, &[a, x]);
    let h2c = rcongr(d, ax, xa, h2, &|d, t| radd(d, t, neg_a));
    let xa_neg_a = radd(d, xa, neg_a);

    // (x + a) + (−a) = x + (a + (−a)).
    let a_neg_a = radd(d, a, neg_a);
    let h3 = d.lemma(p.add_assoc, &[x, a, neg_a]);
    let x_a_neg_a = radd(d, x, a_neg_a);

    // a + (−a) = 0, lifted through `x + _`.
    let h4 = d.lemma(p.add_neg, &[a]);
    let zero_r = rzero(d, p);
    let h4c = rcongr(d, a_neg_a, zero_r, h4, &|d, t| radd(d, x, t));
    let x_zero = radd(d, x, zero_r);

    // x + 0 = x.
    let h5 = d.lemma(p.add_zero, &[x]);

    let (_e, proof) = rchain(
        d,
        start,
        &[
            (ax_neg_a, h1s),
            (xa_neg_a, h2c),
            (x_a_neg_a, h3),
            (x_zero, h4c),
            (x, h5),
        ],
    );

    let stmt = req(d, declared_start, x);
    let ty_inner = d.pi_fv(x_fv, carrier, stmt);
    let ty = d.pi_fv(a_fv, carrier, ty_inner);
    let value_inner = d.lam_fv(x_fv, carrier, proof);
    let value = d.lam_fv(a_fv, carrier, value_inner);
    d.declare_theorem(p.add_sub_cancel_left, ty, value)
}

/// `Rat.sq_sub_sq : ∀ x a, Eq Rat (sub (mul x x) (mul a a)) (mul (sub x a) (add x a))`.
///
/// Difference-of-squares. Route: `Rat.mul_sub_mul` splits `x·x − a·a` into
/// `x·(x−a) + (x−a)·a`; `mul_comm` turns the first summand into
/// `(x−a)·x`; `left_distrib` (symm'd) refolds `(x−a)·x + (x−a)·a` into
/// `(x−a)·(x+a)`.
fn declare_sq_sub_sq(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let sub_x_a = rsub(d, p, x, a);
    let xx = rmul(d, x, x);
    let aa = rmul(d, a, a);
    let start = rsub(d, p, xx, aa);

    // sub (x*x) (a*a) = add (x*(sub x a)) ((sub x a)*a).
    let x_sub = rmul(d, x, sub_x_a);
    let sub_a = rmul(d, sub_x_a, a);
    let h1 = d.lemma(p.mul_sub_mul, &[x, x, a, a]);
    let mid1 = radd(d, x_sub, sub_a);

    // x*(sub x a) = (sub x a)*x, lifted through `+ (sub x a)*a`.
    let sub_x = rmul(d, sub_x_a, x);
    let h2 = d.lemma(p.mul_comm, &[x, sub_x_a]);
    let h2c = rcongr(d, x_sub, sub_x, h2, &|d, t| radd(d, t, sub_a));
    let mid2 = radd(d, sub_x, sub_a);

    // (sub x a)*(x+a) = (sub x a)*x + (sub x a)*a, symm'd.
    let x_plus_a = radd(d, x, a);
    let h3 = d.lemma(p.left_distrib, &[sub_x_a, x, a]);
    let final_rhs = rmul(d, sub_x_a, x_plus_a);
    let h3s = rsymm(d, final_rhs, mid2, h3);

    let (_e, proof) = rchain(d, start, &[(mid1, h1), (mid2, h2c), (final_rhs, h3s)]);

    let stmt = req(d, start, final_rhs);
    let ty_inner = d.pi_fv(a_fv, carrier, stmt);
    let ty = d.pi_fv(x_fv, carrier, ty_inner);
    let value_inner = d.lam_fv(a_fv, carrier, proof);
    let value = d.lam_fv(x_fv, carrier, value_inner);
    d.declare_theorem(p.sq_sub_sq, ty, value)
}

// ---------------------------------------------------------------------------
// The degree-1 Taylor expansion, over `Rat.polyEval`.
// ---------------------------------------------------------------------------

/// `fun i => Nat.rec (motive := fun _ => Rat) c0 (fun _ _ => c1) i` — the
/// coefficient function of a degree-≤1 polynomial (`i = 0 ↦ c0`, `i ≥ 1 ↦
/// c1`), built inline exactly as `bernoulli.rs`'s `L` is: this prelude has
/// no tuple/list type to hold two coefficients, and nothing else here needs
/// to name this function, only to evaluate it at `polyEval`'s two summand
/// indices (`0` and `1`).
fn coeff2(d: &mut IntDev<'_>, c0: ExprId, c1: ExprId) -> ExprId {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = c0;
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let inner = d.lam_fv(ih_fv, carrier, c1);
        d.lam_fv(j_fv, nat, inner)
    };
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, i]);
    d.lam_fv(i_fv, nat, body)
}

/// `Rat.polyEval_deg1 : ∀ c0 c1 t, Eq Rat (polyEval (coeff2 c0 c1) 2 t) (add
/// c0 (mul c1 t))` — the closed form for evaluating a degree-≤1 polynomial.
///
/// Route: two `polyEval_succ` unfoldings and one `polyEval_zero`, each
/// paired with the free (`ι`/`β`-only) simplification of `coeff2 c0 c1`
/// applied to a literal index and of `pow t` at `zero`/`(succ zero)` (the
/// latter via [`RatPrelude::pow_one`]), then `mul_one` and `zero_add` clear
/// the two leftover identity terms.
fn declare_poly_eval_deg1(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let c0_fv = d.fresh_fvar();
    let c0 = d.kernel().fvar(c0_fv);
    let c1_fv = d.fresh_fvar();
    let c1 = d.kernel().fvar(c1_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let c = coeff2(d, c0, c1);
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);

    let start = rpoly_eval(d, p, c, two_n, t);

    // polyEval c 2 t = add (polyEval c 1 t) (mul (c 1) (pow t 1))
    //               ~ add (polyEval c 1 t) (mul c1 (pow t 1))     [c 1 ~ c1, free]
    let pe1t = rpoly_eval(d, p, c, one_n, t);
    let pow_t_1 = rpow(d, p, t, one_n);
    let c1_pow = rmul(d, c1, pow_t_1);
    let h1 = d.lemma(p.poly_eval_succ, &[c, one_n, t]);
    let mid1 = radd(d, pe1t, c1_pow);

    // pow t 1 = t, lifted through `add (polyEval c 1 t) (mul c1 _)`.
    let c1t = rmul(d, c1, t);
    let h_pow1 = d.lemma(p.pow_one, &[t]);
    let h2 = rcongr(d, pow_t_1, t, h_pow1, &|d, tt| {
        let c1_tt = rmul(d, c1, tt);
        radd(d, pe1t, c1_tt)
    });
    let mid2 = radd(d, pe1t, c1t);

    // polyEval c 1 t = c0, by a sub-chain: unfold once more, drop the
    // zero-length sum, clear `mul c0 one`, then `zero_add`.
    let pe0t = rpoly_eval(d, p, c, zero_n, t);
    let one_r = rone(d, p);
    let c0_one = rmul(d, c0, one_r);
    let h3a = d.lemma(p.poly_eval_succ, &[c, zero_n, t]);
    let submid1 = radd(d, pe0t, c0_one);

    let zero_r = rzero(d, p);
    let h3b = d.lemma(p.poly_eval_zero, &[c, t]);
    let h3b_lift = rcongr(d, pe0t, zero_r, h3b, &|d, tt| radd(d, tt, c0_one));
    let submid2 = radd(d, zero_r, c0_one);

    let h3c = d.lemma(p.mul_one, &[c0]);
    let h3c_lift = rcongr(d, c0_one, c0, h3c, &|d, tt| radd(d, zero_r, tt));
    let submid3 = radd(d, zero_r, c0);

    let h3d = d.lemma(p.zero_add, &[c0]);

    let (_e, sub_proof) = rchain(
        d,
        pe1t,
        &[
            (submid1, h3a),
            (submid2, h3b_lift),
            (submid3, h3c_lift),
            (c0, h3d),
        ],
    );

    let h4 = rcongr(d, pe1t, c0, sub_proof, &|d, tt| radd(d, tt, c1t));
    let mid3 = radd(d, c0, c1t);

    let (_e, proof) = rchain(d, start, &[(mid1, h1), (mid2, h2), (mid3, h4)]);

    let final_stmt_rhs = radd(d, c0, c1t);
    let stmt = req(d, start, final_stmt_rhs);
    let ty_t = d.pi_fv(t_fv, carrier, stmt);
    let ty_c1 = d.pi_fv(c1_fv, carrier, ty_t);
    let ty = d.pi_fv(c0_fv, carrier, ty_c1);
    let value_t = d.lam_fv(t_fv, carrier, proof);
    let value_c1 = d.lam_fv(c1_fv, carrier, value_t);
    let value = d.lam_fv(c0_fv, carrier, value_c1);
    d.declare_theorem(p.poly_eval_deg1, ty, value)
}

/// `Rat.taylor_deg1 : ∀ c0 c1 x a, Eq Rat (polyEval (coeff2 c0 c1) 2 x) (add
/// (polyEval (coeff2 c0 c1) 2 a) (mul c1 (sub x a)))`.
///
/// The finite Taylor expansion identity at degree 1: `p(x) = p(a) + c1·(x −
/// a)`. Route: [`RatPrelude::poly_eval_deg1`] at `x` and at `a`, then the
/// pure ring identity `c1·a + c1·(x−a) = c1·x` (via `left_distrib` and
/// [`RatPrelude::add_sub_cancel_left`]) reassembled with `add_assoc`.
fn declare_taylor_deg1(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let c0_fv = d.fresh_fvar();
    let c0 = d.kernel().fvar(c0_fv);
    let c1_fv = d.fresh_fvar();
    let c1 = d.kernel().fvar(c1_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let c = coeff2(d, c0, c1);
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);

    let sub_x_a = rsub(d, p, x, a);
    let start = rpoly_eval(d, p, c, two_n, x);
    let pa = rpoly_eval(d, p, c, two_n, a);

    // Step A: polyEval c 2 x = c0 + c1*x.
    let pf_x = d.lemma(p.poly_eval_deg1, &[c0, c1, x]);
    let c1x = rmul(d, c1, x);
    let target_a = radd(d, c0, c1x);

    // Step B: c0 + c1*x = (c0 + c1*a) + c1*(x-a) — a pure ring identity.
    let mc1a = rmul(d, c1, a);
    let mc1sub = rmul(d, c1, sub_x_a);
    let sum_mc1a_mc1sub = radd(d, mc1a, mc1sub);
    let c0_mc1a = radd(d, c0, mc1a);
    let target_expanded = radd(d, c0_mc1a, mc1sub);

    let h_assoc = d.lemma(p.add_assoc, &[c0, mc1a, mc1sub]);
    let c0_plus_sum = radd(d, c0, sum_mc1a_mc1sub);

    // c1*a + c1*(x-a) = c1*(a + (x-a)) = c1*x.
    let h_distrib = d.lemma(p.left_distrib, &[c1, a, sub_x_a]);
    let a_plus_sub = radd(d, a, sub_x_a);
    let c1_times_sum = rmul(d, c1, a_plus_sub);
    let h_distrib_s = rsymm(d, c1_times_sum, sum_mc1a_mc1sub, h_distrib);

    let h_cancel = d.lemma(p.add_sub_cancel_left, &[a, x]);
    let h_cancel_lift = rcongr(d, a_plus_sub, x, h_cancel, &|d, t| rmul(d, c1, t));
    let mc1x = rmul(d, c1, x);

    let (_e, pf_ring) = rchain(
        d,
        sum_mc1a_mc1sub,
        &[(c1_times_sum, h_distrib_s), (mc1x, h_cancel_lift)],
    );

    let h_ring_lift = rcongr(d, sum_mc1a_mc1sub, mc1x, pf_ring, &|d, t| radd(d, c0, t));

    let pf_expanded_to_a = rtrans(
        d,
        target_expanded,
        c0_plus_sum,
        target_a,
        h_assoc,
        h_ring_lift,
    );
    let fact_b = rsymm(d, target_expanded, target_a, pf_expanded_to_a);

    // Step C: (c0 + c1*a) + c1*(x-a) = polyEval c 2 a + c1*(x-a).
    let pf_a = d.lemma(p.poly_eval_deg1, &[c0, c1, a]);
    let target_a_form = c0_mc1a;
    let step_rhs_expand = rcongr(d, pa, target_a_form, pf_a, &|d, t| radd(d, t, mc1sub));
    let final_rhs = radd(d, pa, mc1sub);
    // step_rhs_expand : Eq(final_rhs, target_expanded); flip it.
    let step_c = rsymm(d, final_rhs, target_expanded, step_rhs_expand);

    let (_e, proof) = rchain(
        d,
        start,
        &[
            (target_a, pf_x),
            (target_expanded, fact_b),
            (final_rhs, step_c),
        ],
    );

    let stmt = req(d, start, final_rhs);
    let ty_a = d.pi_fv(a_fv, carrier, stmt);
    let ty_x = d.pi_fv(x_fv, carrier, ty_a);
    let ty_c1 = d.pi_fv(c1_fv, carrier, ty_x);
    let ty = d.pi_fv(c0_fv, carrier, ty_c1);
    let value_a = d.lam_fv(a_fv, carrier, proof);
    let value_x = d.lam_fv(x_fv, carrier, value_a);
    let value_c1 = d.lam_fv(c1_fv, carrier, value_x);
    let value = d.lam_fv(c0_fv, carrier, value_c1);
    d.declare_theorem(p.taylor_deg1, ty, value)
}
