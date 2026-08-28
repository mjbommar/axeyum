//! `Nat.descFactorial n k = n * (n-1) * … * (n-k+1)` (`k` factors), by
//! structural recursion on `k` with truncated `Nat.sub`:
//!
//! ```text
//! descFactorial n zero     ≡ 1
//! descFactorial n (succ k) ≡ (n - k) * descFactorial n k
//! ```
//!
//! Mirrors Mathlib's `Nat.descFactorial`
//! (`Mathlib.Data.Nat.Factorial.Basic`):
//! `descFactorial (n : ℕ) : ℕ → ℕ | 0 => 1 | k + 1 => (n - k) * descFactorial n k`.
//! Structural in `k`, exactly like [`NatPrelude::factorial`] is structural in
//! its argument — no fuel device is needed. Built with the same
//! [`NatOps::define_binary`] combinator `Nat.sub`/`Nat.mul`/`Nat.sumRange`
//! already use for a two-argument, second-argument recursion.
//!
//! `Nat.sub` truncates (`3 - 5 ≡ 0` rather than going negative), so once `k`
//! exceeds `n` every further step multiplies by a zero factor and the whole
//! product collapses to `0`. [`declare_desc_factorial_of_lt`] proves exactly
//! that boundary (`n < k → n.descFactorial k = 0`) rather than merely
//! asserting it — this is the definition's highest-risk seam, since a wrong
//! sign or a swapped `sub` argument order would still type-check and would
//! only show up as a wrong *value*, never a kernel rejection.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.descFactorial n k`.
fn desc_factorial(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.desc_factorial, &[n, k])
}

/// `False.rec (fun _ => target) false_proof : target` — ex falso into an
/// arbitrary target from a proof of `False`. Local copy of the pattern
/// duplicated per-file throughout this crate (`order_more.rs`, `choose.rs`,
/// `binomial.rs`, …).
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `Nat.descFactorial : Nat → Nat → Nat`, structural recursion on the
/// **second** argument via [`NatOps::define_binary`] — the same combinator
/// `Nat.sub`/`Nat.mul` use — so `descFactorial_zero`/`descFactorial_succ`
/// below hold by `Eq.refl` (β/δ/ι) and exist only so callers can rewrite by
/// name, exactly as `factorial_zero`/`factorial_succ` do for
/// [`NatPrelude::factorial`].
pub(super) fn declare_desc_factorial(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    // descFactorial n zero ≡ 1 ; descFactorial n (succ k) ≡ (n - k) * descFactorial n k
    d.define_binary(p.desc_factorial, 3, &|d, _n| d.num(1), &|d, n, k, ih| {
        let sub_nk = d.sub(n, k);
        d.mul(sub_nk, ih)
    })?;

    // descFactorial_zero : ∀ n, n.descFactorial 0 = 1
    d.theorem(p.desc_factorial_zero, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let lhs = desc_factorial(d, &p, n, zero);
        let one = d.num(1);
        (d.eq(lhs, one), d.refl(one))
    })?;

    // descFactorial_succ : ∀ n k, n.descFactorial (succ k) = (n - k) * n.descFactorial k
    d.theorem(p.desc_factorial_succ, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let sk = d.succ(k);
        let lhs = desc_factorial(d, &p, n, sk);
        let prior = desc_factorial(d, &p, n, k);
        let sub_nk = d.sub(n, k);
        let rhs = d.mul(sub_nk, prior);
        (d.eq(lhs, rhs), d.refl(rhs))
    })?;

    Ok(())
}

/// `descFactorial_one : ∀ n, n.descFactorial 1 = n`.
///
/// `n.descFactorial 1` reduces (`descFactorial_succ` at `k := 0`,
/// definitionally) to `(n - 0) * n.descFactorial 0`, and `n - 0 ≡ n` is
/// itself definitional (`Nat.sub`'s own base case). So the stated goal is
/// defeq to `n * 1 = n`, and `mul_one`'s own proof term closes it directly —
/// no explicit rewrite needed.
pub(super) fn declare_desc_factorial_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.desc_factorial_one, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let lhs = desc_factorial(d, &p, n, one);
        let proof = d.lemma(p.mul_one, &[n]);
        (d.eq(lhs, n), proof)
    })?;
    Ok(())
}

/// `descFactorial_of_lt : ∀ n k, n < k → n.descFactorial k = 0` — the
/// truncated-subtraction boundary: once `k` exceeds `n`, some factor
/// `n - j` in the unrolled product is `0` (`Nat.sub` truncates rather than
/// going negative), so the whole product collapses.
///
/// Induction on `k`, with `n` held fixed throughout (bound once, outside the
/// induction, by [`NatOps::theorem`]'s own arity-2 binder — no need to
/// generalize over `n` inside the motive):
/// - `k = 0`: `n < 0` is impossible ([`NatPrelude::not_lt_zero`]).
/// - `k = succ j`: `n < succ j` gives `n ≤ j`
///   ([`NatPrelude::le_of_lt_succ`]), split into `n < j` or `n = j`
///   ([`NatPrelude::lt_or_eq_of_le`]):
///   - `n < j`: the induction hypothesis gives `n.descFactorial j = 0`, and
///     `n.descFactorial (succ j) ≡ (n - j) * n.descFactorial j` (defeq)
///     collapses via [`NatPrelude::mul_zero`].
///   - `n = j`: substitute `j := n` (`Eq.rec`, [`NatOps::transport`]) into a
///     goal computed once at `x := n`, where
///     `n.descFactorial (succ n) ≡ (n - n) * n.descFactorial n` (defeq)
///     collapses via [`NatPrelude::sub_self`] then [`NatPrelude::zero_mul`].
pub(super) fn declare_desc_factorial_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.desc_factorial_of_lt, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let zero = d.zero();
        let stmt = {
            let hyp = d.lt(n, k);
            let df = desc_factorial(d, &p, n, k);
            let concl = d.eq(df, zero);
            d.arrow(hyp, concl)
        };

        let proof = d.induct(
            &|d, x| {
                let hyp = d.lt(n, x);
                let df = desc_factorial(d, &p, n, x);
                let concl = d.eq(df, zero);
                d.arrow(hyp, concl)
            },
            &|d| {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let hyp_ty = d.lt(n, zero);
                let false_proof = d.lemma(p.not_lt_zero, &[n, h]);
                let df = desc_factorial(d, &p, n, zero);
                let target = d.eq(df, zero);
                let body = ex_falso(d, &p, target, false_proof);
                d.lam_fv(h_fv, hyp_ty, body)
            },
            &|d, j, ih| {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let sj = d.succ(j);
                let hyp_ty = d.lt(n, sj);

                let le_nj = d.lemma(p.le_of_lt_succ, &[n, j, h]);
                let split = d.lemma(p.lt_or_eq_of_le, &[n, j, le_nj]);

                let lt_nj = d.lt(n, j);
                let eq_nj = d.eq(n, j);
                let df_succ_j = desc_factorial(d, &p, n, sj);
                let target = d.eq(df_succ_j, zero);

                // n < j : the IH gives descFactorial n j = 0, so
                // descFactorial n (succ j) ≡ (n-j) * descFactorial n j
                // collapses to (n-j) * 0 = 0.
                let left_minor = {
                    let h1_fv = d.fresh_fvar();
                    let h1 = d.kernel().fvar(h1_fv);
                    let ih_j = d.apply(ih, &[h1]);
                    let df_j = desc_factorial(d, &p, n, j);
                    let sub_nj = d.sub(n, j);
                    let start = d.mul(sub_nj, df_j);
                    let step1 = d.congr(df_j, zero, ih_j, &|d, x| {
                        let sub_nj = d.sub(n, j);
                        d.mul(sub_nj, x)
                    });
                    let sub_nj_zero = d.mul(sub_nj, zero);
                    let step2 = d.lemma(p.mul_zero, &[sub_nj]);
                    let (_last, chained) = d.chain(start, &[(sub_nj_zero, step1), (zero, step2)]);
                    d.lam_fv(h1_fv, lt_nj, chained)
                };

                // n = j : substitute j := n into a goal computed once at
                // x := n, where descFactorial n (succ n) ≡
                // (n-n) * descFactorial n n collapses to 0 * _ = 0.
                let right_minor = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);
                    let df_nn = desc_factorial(d, &p, n, n);
                    let sub_nn = d.sub(n, n);
                    let start = d.mul(sub_nn, df_nn);
                    let sub_self_proof = d.lemma(p.sub_self, &[n]);
                    let step1 = d.congr(sub_nn, zero, sub_self_proof, &|d, x| {
                        let df_nn = desc_factorial(d, &p, n, n);
                        d.mul(x, df_nn)
                    });
                    let zero_mul_dfnn = d.mul(zero, df_nn);
                    let step2 = d.lemma(p.zero_mul, &[df_nn]);
                    let (_last, refl_case) =
                        d.chain(start, &[(zero_mul_dfnn, step1), (zero, step2)]);
                    let motive = d.eq_motive(n, &|d, x| {
                        let sx = d.succ(x);
                        let df = desc_factorial(d, &p, n, sx);
                        d.eq(df, zero)
                    });
                    let transported = d.transport(n, motive, refl_case, j, h2);
                    d.lam_fv(h2_fv, eq_nj, transported)
                };

                let anon = d.anon_name();
                let or_ty = d.const_app(p.logic.or, &[lt_nj, eq_nj]);
                let motive_or = d.kernel().lam(anon, or_ty, target, BinderInfo::Default);
                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let case_proof = d.apply(
                    or_rec,
                    &[lt_nj, eq_nj, motive_or, left_minor, right_minor, split],
                );

                d.lam_fv(h_fv, hyp_ty, case_proof)
            },
            k,
        );

        (stmt, proof)
    })?;
    Ok(())
}

/// Declare [`declare_desc_factorial`], then [`declare_desc_factorial_one`]
/// and [`declare_desc_factorial_of_lt`], which depend only on `Nat.sub` /
/// `Nat.mul` order/algebra theorems declared far earlier in the prelude
/// build.
pub(super) fn declare_desc_factorial_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_desc_factorial(d, p)?;
    declare_desc_factorial_one(d, p)?;
    declare_desc_factorial_of_lt(d, p)?;
    Ok(())
}
