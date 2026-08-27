//! The **Leibniz (alternating series) criterion**, and the pairing argument
//! `creal/trig.rs::declare_cos_one_le_four`'s own doc comment names as the
//! genuine gap between the loose uniform bound `[-4, 4]` on `cosOne` and a
//! bound tight enough to pin the sign (`cos 1 ≈ 0.5403`).
//!
//! ## Why the triangle inequality throws away the one thing that matters
//!
//! `trig.rs`'s bound composes `CReal.abs_sumRange_le` (the triangle
//! inequality, `|Σf| ≤ Σ|f|`) with a domination bound reused unchanged from
//! `CReal.e`. Triangle-inequality composition is blind to *sign*: it is
//! exactly as happy bounding a series whose terms all agree in sign as one
//! that alternates, so it never notices the cancellation that makes an
//! alternating series converge so much faster than its magnitude-sum. The
//! fix genuinely needs to track sign, which is why it needs new machinery
//! rather than a tighter domination series.
//!
//! ## Route: pairing consecutive terms, generalized over `a`
//!
//! For a Nat-indexed term magnitude `a : Nat → CReal` with `a k ≥ 0` and `a
//! (succ k) ≤ a k` (the Leibniz hypotheses), set `t k := mul (pow (neg one)
//! k) (a k)` (the signed term) and, for any `x : Nat`, the **paired partial
//! sums** `E x := sumRange t (add x x)` (an even number of terms) and `O x
//! := sumRange t (succ (add x x))` (one more, odd).
//!
//! [`declare_neg_one_pow_double`] is the parity fact underneath everything
//! else here: `pow (neg one) (add k k) ~ one` for every `k`, proved by plain
//! induction (no case split — the induction variable `k`, not the sign,
//! carries the recursion). It is what turns `E`/`O`'s *algebraic* difference
//! `t (add x x)` into the concrete, sign-known quantity `a (add x x)`, which
//! is what lets [`declare_alternating_e_le_o`] show `E x ≤ O x` from
//! `hnn` alone, and what lets [`declare_alternating_bracket`]'s pairing step
//! show `E x ≤ E (succ x)` from `hdec` alone (`E (succ x) - E x = a (add x x)
//! - a (succ (add x x)) ≥ 0`, i.e. exactly one instance of `hdec`, not a new
//!   domination argument).
//!
//! [`declare_alternating_bracket`] is the pairing induction itself: `∀ m i,
//! E m ≤ E (add m i) ∧ E m ≤ O (add m i)` — the classical fact that EVERY
//! even partial sum from `m` onward, and every odd one, sits above `E m`.
//! Read at `i` ranging over all of `Nat`, this is the finite-sum content of
//! the Leibniz criterion: pairing two terms at a time (never one), the even
//! partial sums climb monotonically and every odd one stays above every even
//! one they are compared against, which is the bracketing structure a
//! convergent alternating series needs and a plain triangle-inequality bound
//! cannot see.
//!
//! ## What this file does NOT reach, and why that is a sized stop, not an
//! oversight
//!
//! Closing `∀ m, E m ≤ L ≤ O m` for the actual limit `L` (`Converges
//! cosSeriesPartial cosOne`, in `CReal.cosOne`'s case) needs
//! `CReal.converges_lower_bound_shift` applied with the hypothesis `∀ n, le
//! (E m) (S (add n (add m m)))` — genuinely quantified over *every* `n`, not
//! just the paired-index `i` this file's induction produces. Bridging `n` to
//! its even/odd decomposition (`n = add i i` or `n = succ (add i i))`) needs
//! a decidable-parity split of an arbitrary `Nat`, which is exactly the
//! device `nat_prelude/fibonacci.rs`'s own module documentation names and
//! explicitly declines to build for Cassini's identity ("substantial new
//! machinery on top of what is here ... that this slice's budget does not
//! cover"). The same call applies here: [`declare_alternating_bracket`] is a
//! complete, symbolic, general theorem in its own right — the pairing
//! argument the loose bound's own doc comment identifies as the missing
//! piece — and the limit-closure plus the concrete numeric bound on `cosOne`
//! are a well-scoped, separately tractable next step, not attempted in this
//! file.

use super::trig::{
    cadd, cle, cmul, cneg, cpow, echain, erefl, esymm, neg_add_self, neg_unique, one_c,
};
use super::{CRealPrelude, creal_ty};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::{NatOps, NatPrelude};

/// Admit `CReal.negOnePowDouble`, `CReal.alternatingELeO`,
/// `CReal.alternatingBracket`. Run after `trig::declare_trig` (reuses that
/// module's `pub(super)` local builders), though nothing here actually
/// depends on any `CReal.cosOne`-specific declaration -- this file is
/// entirely about an abstract term magnitude `a : Nat -> CReal`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_alternating(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_neg_one_pow_double(d, p)?;
    declare_alternating_e_le_o(d, p)?;
    declare_alternating_bracket(d, p)?;
    declare_alternating_bracket_upper(d, p)?;
    declare_alternating_lower_bound(d, p)?;
    declare_alternating_upper_bound(d, p)
}

// ----------------------------------------------------------------------------
// Local builders, reproduced in shape from `trig.rs`'s own copies (see that
// file's module documentation for why each `creal/*` module keeps its own
// rather than widening a sibling's visibility).
// ----------------------------------------------------------------------------

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn and_ty(d: &mut IntDev<'_>, left: ExprId, right: ExprId) -> ExprId {
    d.and(left, right)
}

fn and_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = p.rat.int.logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// `Eq Nat (add (succ j) (succ j)) (succ (succ (add j j)))`, plus the target
/// index itself. `add (succ j) (succ j)` ι-reduces one step to `succ (add
/// (succ j) j)` (the right argument is a bare `succ`-application, matching
/// regardless of what is inside it) but is then STUCK: `add (succ j) j`'s
/// right argument `j` is an abstract `Nat`, not a literal `succ`/`zero`
/// pattern, so `Nat.add`'s own recursion (on its right argument) cannot fire
/// without `Nat.succ_add` (a genuine theorem, not `ι`). One application of
/// it, wrapped in `Eq.refl` (which the kernel accepts against ANY defeq
/// partner, not just a syntactically identical one) for the free first step,
/// closes it.
fn nat_double_succ_eq(d: &mut IntDev<'_>, np: NatPrelude, j: ExprId) -> (ExprId, ExprId) {
    let sj = d.succ(j);
    let lhs = d.add(sj, sj);
    let a = d.add(sj, j);
    let jj = d.add(j, j);
    let b = d.succ(jj);
    let succ_add_jj = d.lemma(np.succ_add, &[j, j]); // Eq Nat a b
    let mid = d.succ(a);
    let refl1 = d.refl(lhs); // Eq Nat lhs lhs, accepted at Eq Nat lhs mid via defeq
    let cong = d.congr(a, b, succ_add_jj, &|d, x| d.succ(x)); // Eq Nat mid (succ b)
    let final_ = d.succ(b);
    let proof = d.trans(lhs, mid, final_, refl1, cong);
    (final_, proof)
}

/// `Equiv (mul (neg one) y) (neg y)`, for any `y`. Derived from
/// `left_distrib`/`add_neg`/`mul_zero`/`mul_one`/`mul_comm`/`neg_unique`
/// rather than assumed: `mul y (add one (neg one)) ~ mul y zero ~ zero`
/// (`left_distrib` then `add_neg`/`mul_zero`) and `mul y (add one (neg one))
/// ~ add (mul y one) (mul y (neg one)) ~ add y (mul y (neg one))`
/// (`left_distrib` then `mul_one`), so `add y (mul y (neg one)) ~ zero`,
/// giving `mul y (neg one) ~ neg y` by [`neg_unique`]; `mul_comm` moves the
/// `neg one` factor to the left.
fn mul_neg_one_eq_neg(d: &mut IntDev<'_>, p: CRealPrelude, y: ExprId) -> ExprId {
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let zero_c = czero(d, p);

    let sum_one_negone = cadd(d, p, one_cc, neg_one);
    let mul_y_sum = cmul(d, p, y, sum_one_negone);
    let mul_y_one = cmul(d, p, y, one_cc);
    let mul_y_negone = cmul(d, p, y, neg_one);
    let add_muls = cadd(d, p, mul_y_one, mul_y_negone);
    let ld = d.lemma(p.left_distrib, &[y, one_cc, neg_one]); // Equiv mul_y_sum add_muls

    let an = d.lemma(p.add_neg, &[one_cc]); // Equiv sum_one_negone zero
    let refl_y = erefl(d, p, y);
    let mul_y_zero = cmul(d, p, y, zero_c);
    let congr1 = d.lemma(p.mul_congr, &[y, y, sum_one_negone, zero_c, refl_y, an]);
    // congr1 : Equiv mul_y_sum mul_y_zero
    let mz = d.lemma(p.mul_zero, &[y]); // Equiv mul_y_zero zero
    let zero_via = echain(d, p, mul_y_sum, &[(mul_y_zero, congr1), (zero_c, mz)]);
    // zero_via : Equiv mul_y_sum zero

    let ld_rev = esymm(d, p, mul_y_sum, add_muls, ld); // Equiv add_muls mul_y_sum
    let add_muls_zero = echain(d, p, add_muls, &[(mul_y_sum, ld_rev), (zero_c, zero_via)]);
    // add_muls_zero : Equiv add_muls zero

    let mo = d.lemma(p.mul_one, &[y]); // Equiv mul_y_one y
    let add_y_negmul = cadd(d, p, y, mul_y_negone);
    let refl_negmul = erefl(d, p, mul_y_negone);
    let cong2 = d.lemma(
        p.add_congr,
        &[mul_y_one, y, mul_y_negone, mul_y_negone, mo, refl_negmul],
    );
    // cong2 : Equiv add_muls add_y_negmul
    let cong2_symm = esymm(d, p, add_muls, add_y_negmul, cong2);
    let final_zero = echain(
        d,
        p,
        add_y_negmul,
        &[(add_muls, cong2_symm), (zero_c, add_muls_zero)],
    );
    // final_zero : Equiv (add y mul_y_negone) zero

    let mul_y_negone_eq_neg_y = neg_unique(d, p, y, mul_y_negone, final_zero);
    // Equiv mul_y_negone (neg y)

    let comm = d.lemma(p.mul_comm, &[neg_one, y]); // Equiv (mul neg_one y) mul_y_negone
    let neg_y = cneg(d, p, y);
    let mul_negone_y = cmul(d, p, neg_one, y);
    echain(
        d,
        p,
        mul_negone_y,
        &[(mul_y_negone, comm), (neg_y, mul_y_negone_eq_neg_y)],
    )
}

/// `le zero (add a2 (neg a1))`, from `h : le a1 a2` -- the "subtract a
/// smaller quantity, get something nonnegative" step [`declare_alternating_bracket`]'s
/// pairing step needs, built from `add_le_add`/`add_neg`/`le_congr` rather
/// than assumed (no `sub_nonneg_of_le`-shaped lemma exists in
/// `CRealPrelude`).
fn nonneg_of_le(d: &mut IntDev<'_>, p: CRealPrelude, a1: ExprId, a2: ExprId, h: ExprId) -> ExprId {
    let neg_a1 = cneg(d, p, a1);
    let refl_neg = d.lemma(p.le_refl, &[neg_a1]);
    let grown = d.lemma(p.add_le_add, &[a1, a2, neg_a1, neg_a1, h, refl_neg]);
    // grown : le (add a1 neg_a1) (add a2 neg_a1)
    let zero_c = czero(d, p);
    let add_a1_neg = cadd(d, p, a1, neg_a1);
    let an = d.lemma(p.add_neg, &[a1]); // Equiv add_a1_neg zero
    let target = cadd(d, p, a2, neg_a1);
    let refl_target = erefl(d, p, target);
    d.lemma(
        p.le_congr,
        &[add_a1_neg, zero_c, target, target, an, refl_target, grown],
    )
}

/// `le (add (neg a2) a1) zero`, from `h : le a1 a2` -- the mirror of
/// [`nonneg_of_le`], needed by [`o_step_le`]'s decreasing-pair argument:
/// `add_le_add` grows `h` by `neg a2` on the right, `add_comm` puts the
/// `neg a2` summand first, then `add_neg` collapses `add a2 (neg a2)` to
/// `zero`.
fn nonpos_of_le(d: &mut IntDev<'_>, p: CRealPrelude, a1: ExprId, a2: ExprId, h: ExprId) -> ExprId {
    let neg_a2 = cneg(d, p, a2);
    let refl_neg = d.lemma(p.le_refl, &[neg_a2]);
    let grown = d.lemma(p.add_le_add, &[a1, a2, neg_a2, neg_a2, h, refl_neg]);
    // grown : le (add a1 neg_a2) (add a2 neg_a2)
    let zero_c = czero(d, p);
    let source = cadd(d, p, a1, neg_a2);
    let target = cadd(d, p, neg_a2, a1);
    let comm = d.lemma(p.add_comm, &[a1, neg_a2]); // Equiv source target
    let add_a2_neg = cadd(d, p, a2, neg_a2);
    let refl_add_a2_neg = erefl(d, p, add_a2_neg);
    let step1 = d.lemma(
        p.le_congr,
        &[
            source,
            target,
            add_a2_neg,
            add_a2_neg,
            comm,
            refl_add_a2_neg,
            grown,
        ],
    );
    // step1 : le target add_a2_neg
    let an = d.lemma(p.add_neg, &[a2]); // Equiv add_a2_neg zero
    let refl_target = erefl(d, p, target);
    d.lemma(
        p.le_congr,
        &[target, target, add_a2_neg, zero_c, refl_target, an, step1],
    )
}

/// `Equiv (neg (neg x)) x` -- [`neg_add_self`] gives `Equiv (add (neg x) x)
/// zero`, [`neg_unique`] at `(a, b) := (neg x, x)` turns that into `Equiv x
/// (neg (neg x))`, and [`esymm`] flips it.
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let h = neg_add_self(d, p, x); // Equiv (add nx x) zero
    let x_eq_nnx = neg_unique(d, p, nx, x, h); // Equiv x (neg nx)
    let nnx = cneg(d, p, nx);
    esymm(d, p, x, nnx, x_eq_nnx)
}

// ----------------------------------------------------------------------------
// `CReal.negOnePowDouble`.
// ----------------------------------------------------------------------------

/// `CReal.negOnePowDouble : ∀ k, Equiv (pow (neg one) (add k k)) one` --
/// `(-1)^(2k) = 1`, for every `k`, by plain induction on `k` (no parity case
/// split: the RECURSION variable is `k` itself, and each step unfolds `pow
/// (neg one)` twice via its own `ι`-reduction, `pow x (succ m) ≡ mul (pow x
/// m) x`).
///
/// Base (`k = 0`): `add 0 0 ≡ 0` and `pow (neg one) 0 ≡ one`, both pure `ι`
/// (the right argument is the literal `Nat.zero`, the recursor's base
/// clause, regardless of what the left argument is) -- `Equiv.refl` closes
/// it outright.
///
/// Step (`k = succ j`, `ih : Equiv (pow (neg one) (add j j)) one`): unfold
/// `pow (neg one) (succ (succ (add j j)))` twice (`ι`), fold the two extra
/// `mul _ (neg one)` factors against `ih` (`mul_congr`) and
/// `CReal.neg_mul_neg` at `one` (`mul (neg one) (neg one) ~ mul one one ~
/// one`), and transport the result across [`nat_double_succ_eq`]'s Nat-level
/// identity to land on the actual index `add (succ j) (succ j)` the goal
/// names.
fn declare_neg_one_pow_double(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let np = p.rat.int.nat;
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let dbl = d.add(x, x);
        let pw = cpow(d, p, neg_one, dbl);
        d.const_app(p.equiv, &[pw, one_cc])
    };
    let base = |d: &mut IntDev<'_>| -> ExprId { erefl(d, p, one_cc) };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let jj = d.add(j, j);
        let pw_jj = cpow(d, p, neg_one, jj);
        let refl_negone = erefl(d, p, neg_one);

        // Level 1: mul pw_jj neg_one ~ neg_one   ( ~ pow neg_one (succ jj) )
        let step1 = d.lemma(
            p.mul_congr,
            &[pw_jj, one_cc, neg_one, neg_one, ih, refl_negone],
        );
        let mul_one_negone = cmul(d, p, one_cc, neg_one);
        let comm1 = d.lemma(p.mul_comm, &[one_cc, neg_one]);
        let mul_negone_one = cmul(d, p, neg_one, one_cc);
        let mo1 = d.lemma(p.mul_one, &[neg_one]);
        let mul_pwjj_negone = cmul(d, p, pw_jj, neg_one);
        let h_succ_jj = echain(
            d,
            p,
            mul_pwjj_negone,
            &[
                (mul_one_negone, step1),
                (mul_negone_one, comm1),
                (neg_one, mo1),
            ],
        );
        // h_succ_jj : Equiv mul_pwjj_negone neg_one  ( ~ pow neg_one (succ jj) )

        // Level 2: mul (pow neg_one (succ jj)) neg_one ~ one
        let pw_succ_jj = mul_pwjj_negone; // defeq to pow neg_one (succ jj)
        let step2 = d.lemma(
            p.mul_congr,
            &[
                pw_succ_jj,
                neg_one,
                neg_one,
                neg_one,
                h_succ_jj,
                refl_negone,
            ],
        );
        let mul_negone_negone = cmul(d, p, neg_one, neg_one);
        let nmn = d.lemma(p.neg_mul_neg, &[one_cc]); // Equiv mul_negone_negone (mul one one)
        let mul_one_one = cmul(d, p, one_cc, one_cc);
        let mo2 = d.lemma(p.mul_one, &[one_cc]); // Equiv mul_one_one one
        let mul_pwsuccjj_negone = cmul(d, p, pw_succ_jj, neg_one);
        let chain2 = echain(
            d,
            p,
            mul_pwsuccjj_negone,
            &[
                (mul_negone_negone, step2),
                (mul_one_one, nmn),
                (one_cc, mo2),
            ],
        );
        // chain2 : Equiv mul_pwsuccjj_negone one  ( ~ pow neg_one (succ (succ jj)) )

        let (final_idx, nat_eq) = nat_double_succ_eq(d, np, j);
        let sj = d.succ(j);
        let lhs_idx = d.add(sj, sj);
        let nat_eq_symm = d.symm(lhs_idx, final_idx, nat_eq);
        let motive2 = d.eq_motive(final_idx, &|d, x| {
            let pw = cpow(d, p, neg_one, x);
            d.const_app(p.equiv, &[pw, one_cc])
        });
        d.transport(final_idx, motive2, chain2, lhs_idx, nat_eq_symm)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let value = d.induct(&motive, &base, &step, k);
    let stmt = motive(d, k);
    let ty = d.pi_fv(k_fv, nat, stmt);
    let value = d.lam_fv(k_fv, nat, value);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.neg_one_pow_double,
        uparams: vec![],
        ty,
        value,
    })
}

// ----------------------------------------------------------------------------
// Shared builders parametrized by an abstract term magnitude `a`.
// ----------------------------------------------------------------------------

/// `λ k, mul (pow (neg one) k) (a k)` -- the signed term.
fn build_t_lam(d: &mut IntDev<'_>, p: CRealPrelude, a_fn: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_k = cpow(d, p, neg_one, k);
    let a_k = d.apply(a_fn, &[k]);
    let body = cmul(d, p, sign_k, a_k);
    d.lam_fv(k_fv, nat, body)
}

/// `E x := sumRange t (add x x)`.
fn e_of(d: &mut IntDev<'_>, p: CRealPrelude, t_lam: ExprId, x: ExprId) -> ExprId {
    let dbl = d.add(x, x);
    d.const_app(p.sum_range, &[t_lam, dbl])
}

/// `O x := sumRange t (succ (add x x))`.
fn o_of(d: &mut IntDev<'_>, p: CRealPrelude, t_lam: ExprId, x: ExprId) -> ExprId {
    let dbl = d.add(x, x);
    let s = d.succ(dbl);
    d.const_app(p.sum_range, &[t_lam, s])
}

/// `Equiv (t (add k k)) (a (add k k))` -- the even-index term IS its
/// magnitude, via [`declare_neg_one_pow_double`] plus `mul_congr`/
/// `mul_comm`/`mul_one`.
fn t_double_eq_a(d: &mut IntDev<'_>, p: CRealPrelude, a_fn: ExprId, k: ExprId) -> ExprId {
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let dbl = d.add(k, k);
    let a_dbl = d.apply(a_fn, &[dbl]);
    let pw = cpow(d, p, neg_one, dbl);
    let parity = d.lemma(p.neg_one_pow_double, &[k]); // Equiv pw one_cc
    let refl_a = erefl(d, p, a_dbl);
    let step1 = d.lemma(p.mul_congr, &[pw, one_cc, a_dbl, a_dbl, parity, refl_a]);
    let mul_one_a = cmul(d, p, one_cc, a_dbl);
    let comm = d.lemma(p.mul_comm, &[one_cc, a_dbl]);
    let mul_a_one = cmul(d, p, a_dbl, one_cc);
    let mo = d.lemma(p.mul_one, &[a_dbl]);
    let mul_pw_a = cmul(d, p, pw, a_dbl);
    echain(
        d,
        p,
        mul_pw_a,
        &[(mul_one_a, step1), (mul_a_one, comm), (a_dbl, mo)],
    )
}

/// `Equiv (t (succ (add k k))) (mul (neg one) (a (succ (add k k))))` -- the
/// odd-index term's sign flips, via [`declare_neg_one_pow_double`] (at `k`)
/// composed one more `pow_succ` step, `mul_congr`, `mul_comm`, `mul_one`.
fn t_double_succ_eq_neg_mul(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_fn: ExprId,
    k: ExprId,
) -> ExprId {
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let dbl = d.add(k, k);
    let sdbl = d.succ(dbl);
    let a_sdbl = d.apply(a_fn, &[sdbl]);
    let pw_dbl = cpow(d, p, neg_one, dbl);
    let parity = d.lemma(p.neg_one_pow_double, &[k]); // Equiv pw_dbl one_cc
    let refl_negone = erefl(d, p, neg_one);
    let step1 = d.lemma(
        p.mul_congr,
        &[pw_dbl, one_cc, neg_one, neg_one, parity, refl_negone],
    );
    // step1 : Equiv (mul pw_dbl neg_one) (mul one_cc neg_one)
    let mul_pwdbl_negone = cmul(d, p, pw_dbl, neg_one); // defeq: pow neg_one (succ dbl)
    let mul_one_negone = cmul(d, p, one_cc, neg_one);
    let comm = d.lemma(p.mul_comm, &[one_cc, neg_one]);
    let mul_negone_one = cmul(d, p, neg_one, one_cc);
    let mo = d.lemma(p.mul_one, &[neg_one]);
    let parity_succ = echain(
        d,
        p,
        mul_pwdbl_negone,
        &[
            (mul_one_negone, step1),
            (mul_negone_one, comm),
            (neg_one, mo),
        ],
    );
    // parity_succ : Equiv (pow neg_one (succ dbl)) neg_one

    let refl_a_sdbl = erefl(d, p, a_sdbl);
    d.lemma(
        p.mul_congr,
        &[
            mul_pwdbl_negone,
            neg_one,
            a_sdbl,
            a_sdbl,
            parity_succ,
            refl_a_sdbl,
        ],
    )
    // Equiv (mul (pow neg_one (succ dbl)) a_sdbl) (mul neg_one a_sdbl)
    //   ~ Equiv (t (succ dbl)) (mul neg_one a_sdbl)   [defeq on the LHS]
}

// ----------------------------------------------------------------------------
// `CReal.alternatingELeO`.
// ----------------------------------------------------------------------------

/// `le (E k) (O k)`, given `hnn : ∀ k, le zero (a k)` -- `O k = add (E k) (t
/// (add k k))` (defeq, `sumRange`'s own `ι`-reduction), and `t (add k k) ~ a
/// (add k k) ≥ 0` ([`t_double_eq_a`] plus `hnn`), so `E k ≤ E k + t (add k
/// k) = O k` by the same `x ≤ x + w` (`w ≥ 0`) shift
/// `series.rs::declare_sum_range_mono_outer`'s own "adjacent" closure uses.
fn e_le_o_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_fn: ExprId,
    hnn: ExprId,
    t_lam: ExprId,
    k: ExprId,
) -> ExprId {
    let e_k = e_of(d, p, t_lam, k);
    let dbl = d.add(k, k);
    let a_dbl = d.apply(a_fn, &[dbl]);
    let hnn_dbl = d.apply(hnn, &[dbl]); // le zero a_dbl
    let t_eq = t_double_eq_a(d, p, a_fn, k); // Equiv t_dbl a_dbl
    let t_dbl = d.apply(t_lam, &[dbl]);
    let zero_c = czero(d, p);

    let t_eq_symm = esymm(d, p, t_dbl, a_dbl, t_eq); // Equiv a_dbl t_dbl
    let refl_zero = erefl(d, p, zero_c);
    let t_nonneg = d.lemma(
        p.le_congr,
        &[zero_c, zero_c, a_dbl, t_dbl, refl_zero, t_eq_symm, hnn_dbl],
    );

    let refl_e = d.lemma(p.le_refl, &[e_k]);
    let grown = d.lemma(p.add_le_add, &[e_k, e_k, zero_c, t_dbl, refl_e, t_nonneg]);
    let padded = cadd(d, p, e_k, zero_c);
    let target = cadd(d, p, e_k, t_dbl); // defeq to o_of k
    let trim = d.lemma(p.add_zero, &[e_k]); // Equiv padded e_k
    let refl_target = erefl(d, p, target);
    d.lemma(
        p.le_congr,
        &[padded, e_k, target, target, trim, refl_target, grown],
    )
}

/// `CReal.alternatingELeO : ∀ a, (∀ k, le zero (a k)) → ∀ k, le (E k) (O
/// k)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_alternating_e_le_o(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a_fn = d.kernel().fvar(a_fv);
    let hnn_fv = d.fresh_fvar();
    let hnn = d.kernel().fvar(hnn_fv);
    let hnn_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_c = czero(d, p);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, zero_c, a_k);
        d.pi_fv(k_fv, nat, body)
    };

    let t_lam = build_t_lam(d, p, a_fn);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = e_le_o_body(d, p, a_fn, hnn, t_lam, k);
    let e_k = e_of(d, p, t_lam, k);
    let o_k = o_of(d, p, t_lam, k);
    let stmt = cle(d, p, e_k, o_k);

    let value = {
        let inner = d.lam_fv(k_fv, nat, body);
        let inner = d.lam_fv(hnn_fv, hnn_ty, inner);
        d.lam_fv(a_fv, fn_ty, inner)
    };
    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt);
        let inner = d.arrow(hnn_ty, inner);
        d.pi_fv(a_fv, fn_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.alternating_e_le_o,
        uparams: vec![],
        ty,
        value,
    })
}

// ----------------------------------------------------------------------------
// `CReal.alternatingBracket`.
// ----------------------------------------------------------------------------

/// `le (E k) (E (succ k))`, given `hdec : ∀ k, le (a (succ k)) (a k)` --
/// `E (succ k) = add (add (E k) (t (add k k))) (t (succ (add k k)))` (defeq,
/// via [`nat_double_succ_eq`] plus two `sumRange` `ι`-steps), and the two new
/// terms sum to `a (add k k) - a (succ (add k k)) ≥ 0`
/// ([`t_double_eq_a`]/[`t_double_succ_eq_neg_mul`]/[`mul_neg_one_eq_neg`]
/// turn the second into `neg (a (succ (add k k)))`, [`nonneg_of_le`] turns
/// `hdec` at `add k k` into that nonnegativity), so `E k ≤ E k + (that pair)
/// = E (succ k)` by the same `x ≤ x + w` shift [`e_le_o_body`] already uses.
fn e_step_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_fn: ExprId,
    hdec: ExprId,
    t_lam: ExprId,
    k: ExprId,
) -> ExprId {
    let np = p.rat.int.nat;
    let e_k = e_of(d, p, t_lam, k);
    let dbl = d.add(k, k);
    let sdbl = d.succ(dbl);
    let t_dbl = d.apply(t_lam, &[dbl]);
    let t_sdbl = d.apply(t_lam, &[sdbl]);
    let pair = cadd(d, p, t_dbl, t_sdbl);

    // pair ~ a(dbl) + neg(a(sdbl))
    let a_dbl = d.apply(a_fn, &[dbl]);
    let a_sdbl = d.apply(a_fn, &[sdbl]);
    let t_dbl_eq = t_double_eq_a(d, p, a_fn, k); // Equiv t_dbl a_dbl
    let t_sdbl_eq_mul = t_double_succ_eq_neg_mul(d, p, a_fn, k); // Equiv t_sdbl (mul neg_one a_sdbl)
    let neg_mul_eq_neg = mul_neg_one_eq_neg(d, p, a_sdbl); // Equiv (mul neg_one a_sdbl) (neg a_sdbl)
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let mul_negone_asdbl = cmul(d, p, neg_one, a_sdbl);
    let neg_a_sdbl = cneg(d, p, a_sdbl);
    let t_sdbl_eq_neg = echain(
        d,
        p,
        t_sdbl,
        &[
            (mul_negone_asdbl, t_sdbl_eq_mul),
            (neg_a_sdbl, neg_mul_eq_neg),
        ],
    );
    // t_sdbl_eq_neg : Equiv t_sdbl neg_a_sdbl
    let pair_eq = d.lemma(
        p.add_congr,
        &[t_dbl, a_dbl, t_sdbl, neg_a_sdbl, t_dbl_eq, t_sdbl_eq_neg],
    );
    // pair_eq : Equiv pair (add a_dbl neg_a_sdbl)

    // pair nonneg: hdec at dbl gives le a_sdbl a_dbl, so nonneg_of_le gives
    // le zero (add a_dbl (neg a_sdbl)).
    let hdec_dbl = d.apply(hdec, &[dbl]); // le a_sdbl a_dbl
    let nn = nonneg_of_le(d, p, a_sdbl, a_dbl, hdec_dbl); // le zero (add a_dbl neg_a_sdbl)
    let zero_c = czero(d, p);
    let add_a_dbl_neg = cadd(d, p, a_dbl, neg_a_sdbl);
    let pair_eq_symm = esymm(d, p, pair, add_a_dbl_neg, pair_eq);
    let refl_zero = erefl(d, p, zero_c);
    let pair_nonneg = d.lemma(
        p.le_congr,
        &[
            zero_c,
            zero_c,
            add_a_dbl_neg,
            pair,
            refl_zero,
            pair_eq_symm,
            nn,
        ],
    );
    // pair_nonneg : le zero pair

    // E k <= E k + pair.
    let refl_e = d.lemma(p.le_refl, &[e_k]);
    let grown = d.lemma(p.add_le_add, &[e_k, e_k, zero_c, pair, refl_e, pair_nonneg]);
    let padded = cadd(d, p, e_k, zero_c);
    let target = cadd(d, p, e_k, pair);
    let trim = d.lemma(p.add_zero, &[e_k]);
    let refl_target = erefl(d, p, target);
    let e_k_le_target = d.lemma(
        p.le_congr,
        &[padded, e_k, target, target, trim, refl_target, grown],
    );
    // e_k_le_target : le e_k target, target = add e_k pair
    //   = add e_k (add t_dbl t_sdbl)

    // Bridge: E(succ k) = add(add(E k, t_dbl), t_sdbl) [defeq via
    // nat_double_succ_eq], reassociate to add(e_k, add(t_dbl,t_sdbl)) via
    // add_assoc, matching `target`.
    let assoc = d.lemma(p.add_assoc, &[e_k, t_dbl, t_sdbl]);
    // assoc : Equiv (add (add e_k t_dbl) t_sdbl) (add e_k (add t_dbl t_sdbl)) = target
    let e_k_plus_t_dbl = cadd(d, p, e_k, t_dbl);
    let e_k_succ_shape = cadd(d, p, e_k_plus_t_dbl, t_sdbl);
    let assoc_symm = esymm(d, p, e_k_succ_shape, target, assoc);
    let refl_e_k = erefl(d, p, e_k);
    let e_k_le_shape = d.lemma(
        p.le_congr,
        &[
            e_k,
            e_k,
            target,
            e_k_succ_shape,
            refl_e_k,
            assoc_symm,
            e_k_le_target,
        ],
    );
    // e_k_le_shape : le e_k e_k_succ_shape

    // `e_k_le_shape` is typed at `final_idx = succ (succ (add k k))`, where
    // `sumRange t_lam final_idx` DEFEQ-reduces (two `ι` steps) to
    // `e_k_succ_shape`. The goal names the index as `add (succ k) (succ k)`
    // (`lhs_idx`), which is only PROPOSITIONALLY (via `nat_double_succ_eq`,
    // not `ι`) equal to `final_idx` -- so the transport must run FROM
    // `final_idx` (where the defeq already holds) TO `lhs_idx` (what the
    // caller's goal names), not the other way around.
    let (final_idx, nat_eq) = nat_double_succ_eq(d, np, k);
    let sk = d.succ(k);
    let lhs_idx = d.add(sk, sk);
    let motive2 = d.eq_motive(final_idx, &|d, x| {
        let ek = e_of(d, p, t_lam, k);
        let sx = d.const_app(p.sum_range, &[t_lam, x]);
        cle(d, p, ek, sx)
    });
    let nat_eq_symm = d.symm(lhs_idx, final_idx, nat_eq); // Eq Nat final_idx lhs_idx
    d.transport(final_idx, motive2, e_k_le_shape, lhs_idx, nat_eq_symm)
    // : le e_k (sumRange t_lam lhs_idx) = le e_k (e_of (succ k))
    //   [since lhs_idx = add sk sk]
}

/// `CReal.alternatingBracket : ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a (succ
/// k)) (a k)) → ∀ m i, And (le (E m) (E (add m i))) (le (E m) (O (add m
/// i)))`.
///
/// Induction on `i`. Base (`i = 0`): `add m 0 ≡ m` (pure `ι`, `Nat.add`'s
/// base clause on its right argument), so both conjuncts reduce to `le (E m)
/// (E m)` (`le_refl`) and `le (E m) (O m)` ([`declare_alternating_e_le_o`]
/// itself, applied at `m`). Step (`i = succ j`, `ih : And (le (E m) (E (add m
/// j))) (le (E m) (O (add m j)))`): `add m (succ j) ≡ succ (add m j)` (pure
/// `ι` again -- `Nat.add`'s right argument here IS the literal `succ j`), so
/// `E (add m (succ j)) = E (succ (add m j))`, one [`e_step_le`] step past
/// `ih`'s left half (`le_trans`); `O (add m (succ j)) = O (succ (add m j))`,
/// reached from the just-derived `le (E m) (E (succ (add m j)))` via
/// [`declare_alternating_e_le_o`] at `succ (add m j)` (`le_trans` again),
/// entirely bypassing any need to track `O`'s own step relation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_alternating_bracket(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a_fn = d.kernel().fvar(a_fv);
    let hnn_fv = d.fresh_fvar();
    let hnn = d.kernel().fvar(hnn_fv);
    let hnn_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_c = czero(d, p);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, zero_c, a_k);
        d.pi_fv(k_fv, nat, body)
    };
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);
    let hdec_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let a_sk = d.apply(a_fn, &[sk]);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, a_sk, a_k);
        d.pi_fv(k_fv, nat, body)
    };

    let t_lam = build_t_lam(d, p, a_fn);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // Motive over `i`: And (le (E m) (E (add m i))) (le (E m) (O (add m i))).
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let e_m = e_of(d, p, t_lam, m);
        let mx = d.add(m, x);
        let e_mx = e_of(d, p, t_lam, mx);
        let o_mx = o_of(d, p, t_lam, mx);
        let left = cle(d, p, e_m, e_mx);
        let right = cle(d, p, e_m, o_mx);
        and_ty(d, left, right)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        // add m 0 ≡ m, pure ι.
        let e_m = e_of(d, p, t_lam, m);
        let left = d.lemma(p.le_refl, &[e_m]);
        let right = e_le_o_body(d, p, a_fn, hnn, t_lam, m);
        let left_ty = cle(d, p, e_m, e_m);
        let o_m = o_of(d, p, t_lam, m);
        let right_ty = cle(d, p, e_m, o_m);
        and_intro(d, p, left_ty, right_ty, left, right)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let e_m = e_of(d, p, t_lam, m);
        let mj = d.add(m, j);
        let e_mj = e_of(d, p, t_lam, mj);
        let o_mj = o_of(d, p, t_lam, mj);
        let left_ty = cle(d, p, e_m, e_mj);
        let right_ty = cle(d, p, e_m, o_mj);
        let ih_left = d.and_left(left_ty, right_ty, ih); // le e_m e_mj
        let ih_right = d.and_right(left_ty, right_ty, ih); // le e_m o_mj (unused directly)
        let _ = ih_right;

        // e_mj -> e(succ mj), one pairing step.
        let step_le = e_step_le(d, p, a_fn, hdec, t_lam, mj); // le e_mj e_of(succ mj)
        let s_mj = d.succ(mj);
        let e_smj = e_of(d, p, t_lam, s_mj);
        let new_left = d.lemma(p.le_trans, &[e_m, e_mj, e_smj, ih_left, step_le]);
        // new_left : le e_m e_smj

        let cross = e_le_o_body(d, p, a_fn, hnn, t_lam, s_mj); // le e_smj o_of(s_mj)
        let o_smj = o_of(d, p, t_lam, s_mj);
        let new_right = d.lemma(p.le_trans, &[e_m, e_smj, o_smj, new_left, cross]);
        // new_right : le e_m o_smj

        // Bridge index: add m (succ j) ≡ succ (add m j) = s_mj, pure ι.
        let sj = d.succ(j);
        let m_sj = d.add(m, sj);
        let e_m_sj = e_of(d, p, t_lam, m_sj); // defeq to e_smj
        let o_m_sj = o_of(d, p, t_lam, m_sj); // defeq to o_smj
        let left_final_ty = cle(d, p, e_m, e_m_sj);
        let right_final_ty = cle(d, p, e_m, o_m_sj);
        and_intro(d, p, left_final_ty, right_final_ty, new_left, new_right)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let value_at_i = d.induct(&motive, &base, &step, i);
    let stmt_at_i = motive(d, i);

    let value = {
        let with_i = d.lam_fv(i_fv, nat, value_at_i);
        let with_m = d.lam_fv(m_fv, nat, with_i);
        let with_hdec = d.lam_fv(hdec_fv, hdec_ty, with_m);
        let with_hnn = d.lam_fv(hnn_fv, hnn_ty, with_hdec);
        d.lam_fv(a_fv, fn_ty, with_hnn)
    };
    let ty = {
        let with_i = d.pi_fv(i_fv, nat, stmt_at_i);
        let with_m = d.pi_fv(m_fv, nat, with_i);
        let with_hdec = d.arrow(hdec_ty, with_m);
        let with_hnn = d.arrow(hnn_ty, with_hdec);
        d.pi_fv(a_fv, fn_ty, with_hnn)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.alternating_bracket,
        uparams: vec![],
        ty,
        value,
    })
}

// ----------------------------------------------------------------------------
// `CReal.alternatingBracketUpper`.
// ----------------------------------------------------------------------------

/// `le (O (succ k)) (O k)`, given `hdec : ∀ k, le (a (succ k)) (a k)` --
/// mirrors [`e_step_le`]: `O (succ k) = O k + (t (succ dbl) + t (succ (succ
/// dbl)))` (defeq, via [`nat_double_succ_eq`] plus THREE `sumRange` `ι`-steps
/// this time -- `O`'s own extra `succ` costs one more unfolding than `E`'s),
/// and the two new terms sum to `a (succ (succ dbl)) - a (succ dbl) ≤ 0`
/// ([`t_double_eq_a`] at `succ k`, transported across
/// [`nat_double_succ_eq`], for the even one; [`t_double_succ_eq_neg_mul`] for
/// the odd one; [`nonpos_of_le`] turns `hdec` at `succ dbl` into that
/// non-positivity), so `O (succ k) = O k + (that pair) ≤ O k`.
fn o_step_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_fn: ExprId,
    hdec: ExprId,
    t_lam: ExprId,
    k: ExprId,
) -> ExprId {
    let np = p.rat.int.nat;
    let e_k = e_of(d, p, t_lam, k);
    let dbl = d.add(k, k);
    let sdbl = d.succ(dbl);
    let t_dbl = d.apply(t_lam, &[dbl]);
    let t_sdbl = d.apply(t_lam, &[sdbl]);
    let o_k_shape = cadd(d, p, e_k, t_dbl); // defeq O(k)

    // t_sdbl ~ neg a_sdbl (odd index sdbl).
    let a_sdbl = d.apply(a_fn, &[sdbl]);
    let t_sdbl_eq_mul = t_double_succ_eq_neg_mul(d, p, a_fn, k);
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let mul_negone_asdbl = cmul(d, p, neg_one, a_sdbl);
    let neg_a_sdbl = cneg(d, p, a_sdbl);
    let nmn = mul_neg_one_eq_neg(d, p, a_sdbl); // Equiv mul_negone_asdbl neg_a_sdbl
    let t_sdbl_eq_neg = echain(
        d,
        p,
        t_sdbl,
        &[(mul_negone_asdbl, t_sdbl_eq_mul), (neg_a_sdbl, nmn)],
    );

    // ssdbl := succ sdbl = succ(succ dbl). t_ssdbl ~ a_ssdbl (even), via
    // t_double_eq_a at `succ k` (relative to `lhs_idx`), transported across
    // nat_double_succ_eq(k).
    let (ssdbl, nat_eq) = nat_double_succ_eq(d, np, k); // Eq lhs_idx ssdbl
    let sk = d.succ(k);
    let lhs_idx = d.add(sk, sk);
    let t_ssdbl = d.apply(t_lam, &[ssdbl]);
    let a_ssdbl = d.apply(a_fn, &[ssdbl]);
    let t_lhs_eq_a_lhs = t_double_eq_a(d, p, a_fn, sk); // Equiv (t lhs_idx)(a lhs_idx)
    let t_ssdbl_eq_a_ssdbl = {
        let motive = d.eq_motive(lhs_idx, &|d, x| {
            let tx = d.apply(t_lam, &[x]);
            let ax = d.apply(a_fn, &[x]);
            d.const_app(p.equiv, &[tx, ax])
        });
        d.transport(lhs_idx, motive, t_lhs_eq_a_lhs, ssdbl, nat_eq)
    };
    // t_ssdbl_eq_a_ssdbl : Equiv t_ssdbl a_ssdbl

    // pair2 := t_sdbl + t_ssdbl ~ neg a_sdbl + a_ssdbl.
    let pair2 = cadd(d, p, t_sdbl, t_ssdbl);
    let add_neg_ssdbl = cadd(d, p, neg_a_sdbl, a_ssdbl);
    let pair2_eq = d.lemma(
        p.add_congr,
        &[
            t_sdbl,
            neg_a_sdbl,
            t_ssdbl,
            a_ssdbl,
            t_sdbl_eq_neg,
            t_ssdbl_eq_a_ssdbl,
        ],
    ); // Equiv pair2 add_neg_ssdbl

    // pair2 nonpos: hdec at sdbl gives le a_ssdbl a_sdbl (ssdbl = succ sdbl),
    // so nonpos_of_le gives le add_neg_ssdbl zero.
    let hdec_sdbl = d.apply(hdec, &[sdbl]); // le a_ssdbl a_sdbl
    let np_le = nonpos_of_le(d, p, a_ssdbl, a_sdbl, hdec_sdbl); // le add_neg_ssdbl zero
    let zero_c = czero(d, p);
    let pair2_eq_symm = esymm(d, p, pair2, add_neg_ssdbl, pair2_eq); // Equiv add_neg_ssdbl pair2
    let refl_zero = erefl(d, p, zero_c);
    let pair2_nonpos = d.lemma(
        p.le_congr,
        &[
            add_neg_ssdbl,
            pair2,
            zero_c,
            zero_c,
            pair2_eq_symm,
            refl_zero,
            np_le,
        ],
    ); // le pair2 zero

    // O(k) + pair2 <= O(k) + 0 ~ O(k).
    let refl_ok = d.lemma(p.le_refl, &[o_k_shape]);
    let grown = d.lemma(
        p.add_le_add,
        &[o_k_shape, o_k_shape, pair2, zero_c, refl_ok, pair2_nonpos],
    ); // le (add o_k_shape pair2) (add o_k_shape zero)
    let shape2 = cadd(d, p, o_k_shape, pair2);
    let padded = cadd(d, p, o_k_shape, zero_c);
    let trim = d.lemma(p.add_zero, &[o_k_shape]); // Equiv padded o_k_shape
    let refl_shape2 = erefl(d, p, shape2);
    let shape2_le_ok = d.lemma(
        p.le_congr,
        &[shape2, shape2, padded, o_k_shape, refl_shape2, trim, grown],
    ); // le shape2 o_k_shape

    // RAW = add(add(o_k_shape, t_sdbl), t_ssdbl) ~[assoc]~ shape2.
    let ok_tsdbl = cadd(d, p, o_k_shape, t_sdbl);
    let raw = cadd(d, p, ok_tsdbl, t_ssdbl);
    let assoc = d.lemma(p.add_assoc, &[o_k_shape, t_sdbl, t_ssdbl]); // Equiv raw shape2
    let assoc_symm = esymm(d, p, raw, shape2, assoc); // Equiv shape2 raw
    let refl_ok2 = erefl(d, p, o_k_shape);
    let raw_le_ok = d.lemma(
        p.le_congr,
        &[
            shape2,
            raw,
            o_k_shape,
            o_k_shape,
            assoc_symm,
            refl_ok2,
            shape2_le_ok,
        ],
    ); // le raw o_k_shape

    // Bridge: O(succ k)'s raw index is `succ lhs_idx`; RAW is defeq to
    // `sumRange t (succ ssdbl)` (three ι steps). Transport across
    // `Eq (succ ssdbl) (succ lhs_idx)`.
    let succ_lhs_idx = d.succ(lhs_idx);
    let sssdbl = d.succ(ssdbl);
    let congr_succ = d.congr(lhs_idx, ssdbl, nat_eq, &|d, x| d.succ(x)); // Eq succ_lhs_idx sssdbl
    let bridge = d.symm(succ_lhs_idx, sssdbl, congr_succ); // Eq sssdbl succ_lhs_idx
    let motive_final = d.eq_motive(sssdbl, &|d, x| {
        let sx = d.const_app(p.sum_range, &[t_lam, x]);
        cle(d, p, sx, o_k_shape)
    });
    d.transport(sssdbl, motive_final, raw_le_ok, succ_lhs_idx, bridge)
    // : le (O (succ k)) (O k)
}

/// `CReal.alternatingBracketUpper : ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a
/// (succ k)) (a k)) → ∀ m i, And (le (E (add m i)) (O m)) (le (O (add m i))
/// (O m))` -- the DUAL of [`declare_alternating_bracket`], same induction
/// shape on `i`: base is [`e_le_o_body`] at `m` plus `le_refl`; step chains
/// [`o_step_le`] against the induction hypothesis's `O` half (`le_trans`)
/// for the new `O` conjunct, then [`e_le_o_body`] at the new index against
/// that just-derived `O` bound for the new `E` conjunct.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_alternating_bracket_upper(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a_fn = d.kernel().fvar(a_fv);
    let hnn_fv = d.fresh_fvar();
    let hnn = d.kernel().fvar(hnn_fv);
    let hnn_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_c = czero(d, p);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, zero_c, a_k);
        d.pi_fv(k_fv, nat, body)
    };
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);
    let hdec_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let a_sk = d.apply(a_fn, &[sk]);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, a_sk, a_k);
        d.pi_fv(k_fv, nat, body)
    };

    let t_lam = build_t_lam(d, p, a_fn);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let o_m = o_of(d, p, t_lam, m);

    // Motive over `i`: And (le (E (add m i)) (O m)) (le (O (add m i)) (O m)).
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let o_m = o_of(d, p, t_lam, m);
        let mx = d.add(m, x);
        let e_mx = e_of(d, p, t_lam, mx);
        let o_mx = o_of(d, p, t_lam, mx);
        let left = cle(d, p, e_mx, o_m);
        let right = cle(d, p, o_mx, o_m);
        and_ty(d, left, right)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        // add m 0 ≡ m, pure ι.
        let left = e_le_o_body(d, p, a_fn, hnn, t_lam, m);
        let right = d.lemma(p.le_refl, &[o_m]);
        let e_m = e_of(d, p, t_lam, m);
        let left_ty = cle(d, p, e_m, o_m);
        let right_ty = cle(d, p, o_m, o_m);
        and_intro(d, p, left_ty, right_ty, left, right)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let mj = d.add(m, j);
        let e_mj = e_of(d, p, t_lam, mj);
        let o_mj = o_of(d, p, t_lam, mj);
        let left_ty = cle(d, p, e_mj, o_m);
        let right_ty = cle(d, p, o_mj, o_m);
        let ih_right = d.and_right(left_ty, right_ty, ih); // le o_mj o_m

        // O(succ mj) -> O(mj), one antitone step, then chain through ih.
        let step_le = o_step_le(d, p, a_fn, hdec, t_lam, mj); // le O(succ mj) o_mj
        let s_mj = d.succ(mj);
        let o_smj = o_of(d, p, t_lam, s_mj);
        let new_right = d.lemma(p.le_trans, &[o_smj, o_mj, o_m, step_le, ih_right]);
        // new_right : le o_smj o_m

        let cross = e_le_o_body(d, p, a_fn, hnn, t_lam, s_mj); // le e_smj o_smj
        let e_smj = e_of(d, p, t_lam, s_mj);
        let new_left = d.lemma(p.le_trans, &[e_smj, o_smj, o_m, cross, new_right]);
        // new_left : le e_smj o_m

        // Bridge index: add m (succ j) ≡ succ (add m j) = s_mj, pure ι.
        let sj = d.succ(j);
        let m_sj = d.add(m, sj);
        let e_m_sj = e_of(d, p, t_lam, m_sj); // defeq to e_smj
        let o_m_sj = o_of(d, p, t_lam, m_sj); // defeq to o_smj
        let left_final_ty = cle(d, p, e_m_sj, o_m);
        let right_final_ty = cle(d, p, o_m_sj, o_m);
        and_intro(d, p, left_final_ty, right_final_ty, new_left, new_right)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let value_at_i = d.induct(&motive, &base, &step, i);
    let stmt_at_i = motive(d, i);

    let value = {
        let with_i = d.lam_fv(i_fv, nat, value_at_i);
        let with_m = d.lam_fv(m_fv, nat, with_i);
        let with_hdec = d.lam_fv(hdec_fv, hdec_ty, with_m);
        let with_hnn = d.lam_fv(hnn_fv, hnn_ty, with_hdec);
        d.lam_fv(a_fv, fn_ty, with_hnn)
    };
    let ty = {
        let with_i = d.pi_fv(i_fv, nat, stmt_at_i);
        let with_m = d.pi_fv(m_fv, nat, with_i);
        let with_hdec = d.arrow(hdec_ty, with_m);
        let with_hnn = d.arrow(hnn_ty, with_hdec);
        d.pi_fv(a_fv, fn_ty, with_hnn)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.alternating_bracket_upper,
        uparams: vec![],
        ty,
        value,
    })
}

// ----------------------------------------------------------------------------
// Closing the bracket against an actual limit.
// ----------------------------------------------------------------------------

/// `Eq Nat (add (add a b) (add c e)) (add (add a c) (add b e))` -- reproduced
/// verbatim in shape from `nat_prelude/fibonacci.rs`'s own private
/// `add_regroup_four` (this module does not touch that file), retyped over
/// `&mut IntDev`.
fn add_regroup_four(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> ExprId {
    let ab = d.add(a, b);
    let ce = d.add(c, e);
    let start = d.add(ab, ce);

    let abc = d.add(ab, c);
    let step1 = d.add(abc, e);
    let h1 = {
        let fwd = d.lemma(np.add_assoc, &[ab, c, e]); // (ab+c)+e = ab+(c+e)
        d.symm(step1, start, fwd)
    };

    let ac = d.add(a, c);
    let acb = d.add(ac, b);
    let step2 = d.add(acb, e);
    let h2 = {
        let h_comm = d.lemma(np.add_right_comm, &[a, b, c]); // (a+b)+c = (a+c)+b
        d.congr(abc, acb, h_comm, &|d, x| d.add(x, e))
    };

    let be = d.add(b, e);
    let target = d.add(ac, be);
    let h3 = d.lemma(np.add_assoc, &[ac, b, e]); // (ac+b)+e = ac+(b+e)

    let (_end, proof) = d.chain(start, &[(step1, h1), (step2, h2), (target, h3)]);
    proof
}

/// `Eq Nat (add (add k k) (add m m)) (add (add m k) (add m k))` --
/// [`add_regroup_four`] at `(k, k, m, m)` gives `(k+m)+(k+m)`; one `add_comm`
/// swap under `fun x => add x x` finishes.
fn kk_mm_regroup(d: &mut IntDev<'_>, np: NatPrelude, k: ExprId, m: ExprId) -> ExprId {
    let step = add_regroup_four(d, np, k, k, m, m); // Eq (kk+mm) ((k+m)+(k+m))
    let km = d.add(k, m);
    let mk = d.add(m, k);
    let comm = d.lemma(np.add_comm, &[k, m]); // Eq km mk
    let swap = d.congr(km, mk, comm, &|d, x| d.add(x, x)); // Eq ((k+m)+(k+m)) ((m+k)+(m+k))
    let kk = d.add(k, k);
    let mm = d.add(m, m);
    let start = d.add(kk, mm);
    let mid = d.add(km, km);
    let end = d.add(mk, mk);
    let (_, proof) = d.chain(start, &[(mid, step), (end, swap)]);
    proof
}

/// `CReal.alternatingLowerBound`. See
/// [`CRealPrelude::alternating_lower_bound`].
///
/// Builds `shift_hyp : ∀ n, le (E m) (sumRange t (add n (add m m)))` by
/// case-splitting `n` via `Nat.even_or_odd` (the COMPUTED parity split,
/// `k := div n 2`): at `n = add k k`, [`kk_mm_regroup`] plus one `Nat`-level
/// substitution transports [`declare_alternating_bracket`]'s `le (E m) (E
/// (add m k))` across the (propositional, not `ι`) index identity onto `le
/// (E m) (sumRange t (add n (add m m)))`; at `n = succ (add k k)`, one more
/// `succ_add` step does the same for the `O (add m k)` half. Then
/// [`CRealPrelude::converges_lower_bound_shift`] at shift `s := add m m`
/// closes `le (E m) L`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_alternating_lower_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let np = p.rat.int.nat;

    let a_fv = d.fresh_fvar();
    let a_fn = d.kernel().fvar(a_fv);
    let hnn_fv = d.fresh_fvar();
    let hnn = d.kernel().fvar(hnn_fv);
    let hnn_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_c = czero(d, p);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, zero_c, a_k);
        d.pi_fv(k_fv, nat, body)
    };
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);
    let hdec_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let a_sk = d.apply(a_fn, &[sk]);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, a_sk, a_k);
        d.pi_fv(k_fv, nat, body)
    };

    let t_lam = build_t_lam(d, p, a_fn);
    let f_expr = d.const_app(p.sum_range, &[t_lam]);

    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let converges_hyp_fv = d.fresh_fvar();
    let converges_hyp = d.kernel().fvar(converges_hyp_fv);
    let converges_ty = d.const_app(p.converges, &[f_expr, l]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let e_m = e_of(d, p, t_lam, m);
    let m_m = d.add(m, m);

    // shift_hyp : ∀ n, le (E m) (S (add n (add m m))).
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let two_nat = d.num(2);
    let k = d.div(n, two_nat);
    let kk = d.add(k, k);
    let skk = d.succ(kk);
    let left_ty = d.eq(n, kk);
    let right_ty = d.eq(n, skk);
    let even_or_odd_n = d.lemma(np.even_or_odd, &[n]);
    let n_mm = d.add(n, m_m);
    let s_n_mm = d.const_app(p.sum_range, &[t_lam, n_mm]);
    let target = cle(d, p, e_m, s_n_mm);

    let mk = d.add(m, k);
    let e_mk = e_of(d, p, t_lam, mk);
    let o_mk = o_of(d, p, t_lam, mk);
    let bracket_left_ty = cle(d, p, e_m, e_mk);
    let bracket_right_ty = cle(d, p, e_m, o_mk);
    let bracket_at_mk = d.const_app(p.alternating_bracket, &[a_fn, hnn, hdec, m, k]);
    let bracket_left = d.and_left(bracket_left_ty, bracket_right_ty, bracket_at_mk);
    let bracket_right = d.and_right(bracket_left_ty, bracket_right_ty, bracket_at_mk);

    let rhs0 = d.add(mk, mk); // matches e_mk's raw Nat argument
    let rhs1 = d.succ(rhs0); // matches o_mk's raw Nat argument
    let core_eq = kk_mm_regroup(d, np, k, m); // Eq (add kk m_m) rhs0
    let lhs0 = d.add(kk, m_m);

    let on_left = |d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
        // heq : Eq n kk
        let symm_heq = d.symm(n, kk, heq); // Eq kk n
        let congr_step = d.congr(kk, n, symm_heq, &|d, x| d.add(x, m_m)); // Eq lhs0 n_mm
        let symm_core = d.symm(lhs0, rhs0, core_eq); // Eq rhs0 lhs0
        let h_final = d.trans(rhs0, lhs0, n_mm, symm_core, congr_step); // Eq rhs0 n_mm
        let motive = d.eq_motive(rhs0, &|d, x| {
            let sx = d.const_app(p.sum_range, &[t_lam, x]);
            cle(d, p, e_m, sx)
        });
        d.transport(rhs0, motive, bracket_left, n_mm, h_final)
    };

    let on_right = |d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
        // heq : Eq n skk
        let succ_add_eq = d.lemma(np.succ_add, &[kk, m_m]); // Eq (add skk m_m) (succ (add kk m_m))
        let mid = d.succ(lhs0);
        let succ_congr = d.congr(lhs0, rhs0, core_eq, &|d, x| d.succ(x)); // Eq mid rhs1
        let lhs1 = d.add(skk, m_m);
        let (_, chain_proof) = d.chain(lhs1, &[(mid, succ_add_eq), (rhs1, succ_congr)]);
        // chain_proof : Eq lhs1 rhs1
        let symm_heq = d.symm(n, skk, heq); // Eq skk n
        let congr_step = d.congr(skk, n, symm_heq, &|d, x| d.add(x, m_m)); // Eq lhs1 n_mm
        let symm_chain = d.symm(lhs1, rhs1, chain_proof); // Eq rhs1 lhs1
        let h_final = d.trans(rhs1, lhs1, n_mm, symm_chain, congr_step); // Eq rhs1 n_mm
        let motive = d.eq_motive(rhs1, &|d, x| {
            let sx = d.const_app(p.sum_range, &[t_lam, x]);
            cle(d, p, e_m, sx)
        });
        d.transport(rhs1, motive, bracket_right, n_mm, h_final)
    };

    let or_body = d.or_elim(
        left_ty,
        right_ty,
        target,
        even_or_odd_n,
        &on_left,
        &on_right,
    );
    let shift_hyp = d.lam_fv(n_fv, nat, or_body);

    let result = d.const_app(
        p.converges_lower_bound_shift,
        &[m_m, e_m, f_expr, l, shift_hyp, converges_hyp],
    );

    let value = {
        let with_m = d.lam_fv(m_fv, nat, result);
        let with_converges = d.lam_fv(converges_hyp_fv, converges_ty, with_m);
        let with_l = d.lam_fv(l_fv, carrier, with_converges);
        let with_hdec = d.lam_fv(hdec_fv, hdec_ty, with_l);
        let with_hnn = d.lam_fv(hnn_fv, hnn_ty, with_hdec);
        d.lam_fv(a_fv, fn_ty, with_hnn)
    };
    let stmt_at_m = cle(d, p, e_m, l);
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt_at_m);
        let with_converges = d.arrow(converges_ty, with_m);
        let with_l = d.pi_fv(l_fv, carrier, with_converges);
        let with_hdec = d.arrow(hdec_ty, with_l);
        let with_hnn = d.arrow(hnn_ty, with_hdec);
        d.pi_fv(a_fv, fn_ty, with_hnn)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.alternating_lower_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.alternatingUpperBound`. See
/// [`CRealPrelude::alternating_upper_bound`].
///
/// Same per-`n` case split as [`declare_alternating_lower_bound`], but off
/// [`declare_alternating_bracket_upper`] instead, landing directly on
/// `direct_hyp : ∀ n, le (sumRange t (add n (add m m))) (O m)`. This
/// development has no `converges_upper_bound_shift`, so closing `le L (O m)`
/// routes through [`CRealPrelude::converges_neg`]/[`CRealPrelude::neg_le_neg`]:
/// `neg_le_neg` turns `direct_hyp` into the shift hypothesis
/// [`CRealPrelude::converges_lower_bound_shift`] needs for the NEGATED
/// sequence (`a := neg (O m)`, `f := fun n => neg (S n)`,
/// `L' := neg L`, via `converges_neg`), giving `le (neg (O m)) (neg L)`; one
/// more `neg_le_neg` plus [`double_neg`] (twice, via `le_congr`) flips that
/// back to `le L (O m)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_alternating_upper_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let np = p.rat.int.nat;

    let a_fv = d.fresh_fvar();
    let a_fn = d.kernel().fvar(a_fv);
    let hnn_fv = d.fresh_fvar();
    let hnn = d.kernel().fvar(hnn_fv);
    let hnn_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_c = czero(d, p);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, zero_c, a_k);
        d.pi_fv(k_fv, nat, body)
    };
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);
    let hdec_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let a_sk = d.apply(a_fn, &[sk]);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, a_sk, a_k);
        d.pi_fv(k_fv, nat, body)
    };

    let t_lam = build_t_lam(d, p, a_fn);
    let f_expr = d.const_app(p.sum_range, &[t_lam]);

    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let converges_hyp_fv = d.fresh_fvar();
    let converges_hyp = d.kernel().fvar(converges_hyp_fv);
    let converges_ty = d.const_app(p.converges, &[f_expr, l]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let o_m = o_of(d, p, t_lam, m);
    let m_m = d.add(m, m);

    // direct_hyp : ∀ n, le (S (add n (add m m))) (O m).
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let two_nat = d.num(2);
    let k = d.div(n, two_nat);
    let kk = d.add(k, k);
    let skk = d.succ(kk);
    let left_ty = d.eq(n, kk);
    let right_ty = d.eq(n, skk);
    let even_or_odd_n = d.lemma(np.even_or_odd, &[n]);
    let n_mm = d.add(n, m_m);
    let s_n_mm = d.const_app(p.sum_range, &[t_lam, n_mm]);
    let direct_target = cle(d, p, s_n_mm, o_m);

    let mk = d.add(m, k);
    let e_mk = e_of(d, p, t_lam, mk);
    let o_mk = o_of(d, p, t_lam, mk);
    let upper_left_ty = cle(d, p, e_mk, o_m);
    let upper_right_ty = cle(d, p, o_mk, o_m);
    let upper_at_mk = d.const_app(p.alternating_bracket_upper, &[a_fn, hnn, hdec, m, k]);
    let upper_left = d.and_left(upper_left_ty, upper_right_ty, upper_at_mk); // le e_mk o_m
    let upper_right = d.and_right(upper_left_ty, upper_right_ty, upper_at_mk); // le o_mk o_m

    let rhs0 = d.add(mk, mk); // matches e_mk's raw Nat argument
    let rhs1 = d.succ(rhs0); // matches o_mk's raw Nat argument
    let core_eq = kk_mm_regroup(d, np, k, m); // Eq (add kk m_m) rhs0
    let lhs0 = d.add(kk, m_m);

    let on_left = |d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
        let symm_heq = d.symm(n, kk, heq);
        let congr_step = d.congr(kk, n, symm_heq, &|d, x| d.add(x, m_m)); // Eq lhs0 n_mm
        let symm_core = d.symm(lhs0, rhs0, core_eq); // Eq rhs0 lhs0
        let h_final = d.trans(rhs0, lhs0, n_mm, symm_core, congr_step); // Eq rhs0 n_mm
        let motive = d.eq_motive(rhs0, &|d, x| {
            let sx = d.const_app(p.sum_range, &[t_lam, x]);
            cle(d, p, sx, o_m)
        });
        d.transport(rhs0, motive, upper_left, n_mm, h_final)
    };

    let on_right = |d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
        let succ_add_eq = d.lemma(np.succ_add, &[kk, m_m]);
        let mid = d.succ(lhs0);
        let succ_congr = d.congr(lhs0, rhs0, core_eq, &|d, x| d.succ(x));
        let lhs1 = d.add(skk, m_m);
        let (_, chain_proof) = d.chain(lhs1, &[(mid, succ_add_eq), (rhs1, succ_congr)]);
        let symm_heq = d.symm(n, skk, heq);
        let congr_step = d.congr(skk, n, symm_heq, &|d, x| d.add(x, m_m));
        let symm_chain = d.symm(lhs1, rhs1, chain_proof);
        let h_final = d.trans(rhs1, lhs1, n_mm, symm_chain, congr_step);
        let motive = d.eq_motive(rhs1, &|d, x| {
            let sx = d.const_app(p.sum_range, &[t_lam, x]);
            cle(d, p, sx, o_m)
        });
        d.transport(rhs1, motive, upper_right, n_mm, h_final)
    };

    let direct_body = d.or_elim(
        left_ty,
        right_ty,
        direct_target,
        even_or_odd_n,
        &on_left,
        &on_right,
    );

    // shift_hyp : ∀ n, le (neg (O m)) (neg (S (add n (add m m)))), via
    // neg_le_neg on direct_body.
    let neg_o_m = cneg(d, p, o_m);
    let flipped = d.lemma(p.neg_le_neg, &[s_n_mm, o_m, direct_body]);
    let shift_hyp = d.lam_fv(n_fv, nat, flipped);

    let neg_f_lam = {
        let fresh_n_fv = d.fresh_fvar();
        let fresh_n = d.kernel().fvar(fresh_n_fv);
        let f_n = d.apply(f_expr, &[fresh_n]);
        let neg_f_n = cneg(d, p, f_n);
        d.lam_fv(fresh_n_fv, nat, neg_f_n)
    };
    let neg_l = cneg(d, p, l);
    let converges_neg_hyp = d.const_app(p.converges_neg, &[f_expr, l, converges_hyp]);

    let lower_result = d.const_app(
        p.converges_lower_bound_shift,
        &[m_m, neg_o_m, neg_f_lam, neg_l, shift_hyp, converges_neg_hyp],
    );
    // lower_result : le neg_o_m neg_l = le (neg (O m)) (neg L)

    // Flip back: neg_le_neg gives le (neg neg_l) (neg neg_o_m); double_neg
    // (twice) plus le_congr land on le L (O m).
    let flipped_back = d.lemma(p.neg_le_neg, &[neg_o_m, neg_l, lower_result]);
    // flipped_back : le (neg neg_l) (neg neg_o_m)
    let nn_l = cneg(d, p, neg_l);
    let nn_o_m = cneg(d, p, neg_o_m);
    let dn_l = double_neg(d, p, l); // Equiv nn_l l
    let dn_o_m = double_neg(d, p, o_m); // Equiv nn_o_m o_m
    let stmt_at_m = cle(d, p, l, o_m);
    let final_result = d.lemma(
        p.le_congr,
        &[nn_l, l, nn_o_m, o_m, dn_l, dn_o_m, flipped_back],
    );
    // final_result : le l o_m

    let value = {
        let with_m = d.lam_fv(m_fv, nat, final_result);
        let with_converges = d.lam_fv(converges_hyp_fv, converges_ty, with_m);
        let with_l = d.lam_fv(l_fv, carrier, with_converges);
        let with_hdec = d.lam_fv(hdec_fv, hdec_ty, with_l);
        let with_hnn = d.lam_fv(hnn_fv, hnn_ty, with_hdec);
        d.lam_fv(a_fv, fn_ty, with_hnn)
    };
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt_at_m);
        let with_converges = d.arrow(converges_ty, with_m);
        let with_l = d.pi_fv(l_fv, carrier, with_converges);
        let with_hdec = d.arrow(hdec_ty, with_l);
        let with_hnn = d.arrow(hnn_ty, with_hdec);
        d.pi_fv(a_fv, fn_ty, with_hnn)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.alternating_upper_bound,
        uparams: vec![],
        ty,
        value,
    })
}
