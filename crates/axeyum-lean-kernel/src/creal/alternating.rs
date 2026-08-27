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
//! domination argument).
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

use super::trig::{cadd, cle, cmul, cneg, cpow, echain, erefl, esymm, neg_unique, one_c};
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
    declare_alternating_bracket(d, p)
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
