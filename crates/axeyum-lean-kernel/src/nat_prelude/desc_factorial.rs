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
use super::binomial::mul_left_comm;
use super::helpers::transport_dvd_right;
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

/// `descFactorial_succ_eq_succ_mul : ∀ n k, (succ n).descFactorial (succ k) =
/// succ n * n.descFactorial k` — the "front-peel" identity. `descFactorial`'s
/// own recursion ([`declare_desc_factorial`]'s `desc_factorial_succ`) peels
/// the SMALLEST factor off the BACK of the product (`n.descFactorial (succ
/// k) = (n-k) * n.descFactorial k`); this peels the LARGEST factor (`succ
/// n` itself) off the FRONT, leaving exactly `n.descFactorial k` — the same
/// `k` factors, one row down. [`declare_desc_factorial_eq_factorial_mul_choose`]'s
/// outer induction needs this precisely because its induction hypothesis is
/// only ever about `n`, never `succ n`; `desc_factorial_succ` alone cannot
/// bridge that gap.
///
/// Proved by induction on `k`, `n` held fixed throughout (it never changes
/// across this recursion). `k = 0` reduces both sides to `succ n` via
/// [`declare_desc_factorial_one`]/[`declare_desc_factorial`]/`mul_one`.
/// `k = succ j` chains `desc_factorial_succ` at `(succ n, succ j)`, the IH at
/// `j`, `succ_sub_succ` (`succ n - succ j = n - j`, collapsing the truncated
/// subtraction back to the untouched-`n` form), and `desc_factorial_succ` at
/// `(n, j)` reversed.
pub(super) fn declare_desc_factorial_succ_eq_succ_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.desc_factorial_succ_eq_succ_mul, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let sn = d.succ(n);

        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sx = d.succ(x);
            let lhs = desc_factorial(d, &p, sn, sx);
            let df_n_x = desc_factorial(d, &p, n, x);
            let rhs = d.mul(sn, df_n_x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, k);

        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let one = d.num(1);
                let lhs = desc_factorial(d, &p, sn, one);
                let lhs_eq = d.lemma(p.desc_factorial_one, &[sn]); // Eq(lhs, sn)

                let df_n_0 = desc_factorial(d, &p, n, zero);
                let rhs = d.mul(sn, df_n_0);
                let df0_eq = d.lemma(p.desc_factorial_zero, &[n]); // Eq(df_n_0, one)
                let mid = d.mul(sn, one);
                let step1 = d.congr(df_n_0, one, df0_eq, &|d, x| d.mul(sn, x));
                let mul_one_eq = d.lemma(p.mul_one, &[sn]); // Eq(mid, sn)
                let (_e, rhs_chain) = d.chain(rhs, &[(mid, step1), (sn, mul_one_eq)]);
                let rhs_rev = d.symm(rhs, sn, rhs_chain);
                d.trans(lhs, sn, rhs, lhs_eq, rhs_rev)
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let ssj = d.succ(sj);

                let start = desc_factorial(d, &p, sn, ssj);
                // Step 1: desc_factorial_succ(sn, sj) — start = (sn - sj) * descFactorial(sn, sj).
                let step1 = d.lemma(p.desc_factorial_succ, &[sn, sj]);
                let sub_sn_sj = d.sub(sn, sj);
                let df_sn_sj = desc_factorial(d, &p, sn, sj);
                let target1 = d.mul(sub_sn_sj, df_sn_sj);

                // Step 2: rewrite descFactorial(sn, sj) via ih.
                let df_n_j = desc_factorial(d, &p, n, j);
                let mul_sn_dfnj = d.mul(sn, df_n_j);
                let step2 = d.congr(df_sn_sj, mul_sn_dfnj, ih, &|d, x| {
                    let sub_sn_sj = d.sub(sn, sj);
                    d.mul(sub_sn_sj, x)
                });
                let target2 = d.mul(sub_sn_sj, mul_sn_dfnj);

                // Step 3: succ_sub_succ(n, j) — sub(sn, sj) = sub(n, j).
                let sub_eq = d.lemma(p.succ_sub_succ, &[n, j]);
                let sub_n_j = d.sub(n, j);
                let step3 = d.congr(sub_sn_sj, sub_n_j, sub_eq, &|d, x| {
                    let mul_sn_dfnj = d.mul(sn, df_n_j);
                    d.mul(x, mul_sn_dfnj)
                });
                let target3 = d.mul(sub_n_j, mul_sn_dfnj);

                // Step 4: mul_left_comm — (n-j)*(sn*df_n_j) = sn*((n-j)*df_n_j).
                let step4 = mul_left_comm(d, &p, sub_n_j, sn, df_n_j);
                let sub_df = d.mul(sub_n_j, df_n_j);
                let target4 = d.mul(sn, sub_df);

                // Step 5: desc_factorial_succ(n, j) reversed — sub_df = descFactorial(n, sj).
                let df_succ_eq = d.lemma(p.desc_factorial_succ, &[n, j]); // Eq(df_n_sj, sub_df)
                let df_n_sj = desc_factorial(d, &p, n, sj);
                let df_succ_rev = d.symm(df_n_sj, sub_df, df_succ_eq); // Eq(sub_df, df_n_sj)
                let step5 = d.congr(sub_df, df_n_sj, df_succ_rev, &|d, x| d.mul(sn, x));
                let target5 = d.mul(sn, df_n_sj);

                let (_e, proof) = d.chain(
                    start,
                    &[
                        (target1, step1),
                        (target2, step2),
                        (target3, step3),
                        (target4, step4),
                        (target5, step5),
                    ],
                );
                proof
            },
            k,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// The `n = 0` base case of
/// [`declare_desc_factorial_eq_factorial_mul_choose`]'s outer induction on
/// `n`: `∀ k, descFactorial 0 k = k! * choose 0 k`, by an inner case-split on
/// `k` (no induction hypothesis exists at `n = 0`).
fn desc_choose_base_all_k(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();

    let case_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let df = desc_factorial(d, &p, zero, x);
        let fact_x = d.factorial(x);
        let choose_0x = d.choose(zero, x);
        let rhs = d.mul(fact_x, choose_0x);
        d.eq(df, rhs)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = d.induct(
        &case_motive,
        &|d| {
            // k = 0 : descFactorial 0 0 = factorial 0 * choose 0 0, both 1.
            let zero = d.zero();
            let one = d.num(1);
            let lhs = desc_factorial(d, &p, zero, zero);
            let lhs_eq = d.lemma(p.desc_factorial_zero, &[zero]); // Eq(lhs, one)

            let fact0 = d.factorial(zero);
            let fact0_eq = d.lemma(p.factorial_zero, &[]); // Eq(fact0, one)
            let choose00 = d.choose(zero, zero);
            let choose00_eq = d.lemma(p.choose_zero_right, &[zero]); // Eq(choose00, one)
            let rhs = d.mul(fact0, choose00);
            let step1 = d.congr(fact0, one, fact0_eq, &|d, x| {
                let choose00 = d.choose(zero, zero);
                d.mul(x, choose00)
            });
            let mid1 = d.mul(one, choose00);
            let step2 = d.congr(choose00, one, choose00_eq, &|d, x| d.mul(one, x));
            let mid2 = d.mul(one, one);
            let one_mul_eq = d.lemma(p.one_mul, &[one]); // Eq(mid2, one)
            let (_e, rhs_chain) = d.chain(rhs, &[(mid1, step1), (mid2, step2), (one, one_mul_eq)]);
            let rhs_rev = d.symm(rhs, one, rhs_chain);
            d.trans(lhs, one, rhs, lhs_eq, rhs_rev)
        },
        &|d, j, _ih| {
            // k = succ j : descFactorial 0 (succ j) = 0 = the choose contribution.
            let sj = d.succ(j);
            let zero = d.zero();
            let lhs = desc_factorial(d, &p, zero, sj);
            let lt_proof = d.zero_lt_succ(j);
            let lhs_eq = d.lemma(p.desc_factorial_of_lt, &[zero, sj, lt_proof]); // Eq(lhs, zero)

            let fact_sj = d.factorial(sj);
            let choose_0sj = d.choose(zero, sj);
            let choose_eq = d.lemma(p.zero_choose_succ, &[j]); // Eq(choose_0sj, zero)
            let rhs = d.mul(fact_sj, choose_0sj);
            let rhs_step = d.congr(choose_0sj, zero, choose_eq, &|d, x| {
                let fact_sj = d.factorial(sj);
                d.mul(fact_sj, x)
            });
            let mid = d.mul(fact_sj, zero);
            let mul_zero_eq = d.lemma(p.mul_zero, &[fact_sj]); // Eq(mid, zero)
            let (_e, rhs_chain) = d.chain(rhs, &[(mid, rhs_step), (zero, mul_zero_eq)]);
            let rhs_rev = d.symm(rhs, zero, rhs_chain);
            d.trans(lhs, zero, rhs, lhs_eq, rhs_rev)
        },
        k,
    );
    d.lam_fv(k_fv, nat, body)
}

/// The successor step of
/// [`declare_desc_factorial_eq_factorial_mul_choose`]'s outer induction:
/// given `ih : ∀ k, descFactorial np k = k! * choose np k`, produce `∀ k,
/// descFactorial (succ np) k = k! * choose (succ np) k`, by an inner
/// case-split on `k`. `k = 0` is trivial; `k = succ j` chains six
/// identities — [`declare_desc_factorial_succ_eq_succ_mul`], `ih` at `j`,
/// [`mul_left_comm`], [`NatPrelude::succ_mul_choose_eq`], `mul_assoc`
/// (reversed), and `factorial_succ` (reversed) — see the module doc comment
/// on [`declare_desc_factorial_eq_factorial_mul_choose`].
fn desc_choose_succ_all_k(d: &mut NatDev<'_>, p: &NatPrelude, np: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let snp = d.succ(np);

    let case_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let df = desc_factorial(d, &p, snp, x);
        let fact_x = d.factorial(x);
        let choose_x = d.choose(snp, x);
        let rhs = d.mul(fact_x, choose_x);
        d.eq(df, rhs)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = d.induct(
        &case_motive,
        &|d| {
            // k = 0 : descFactorial(succ np) 0 = factorial 0 * choose(succ np) 0, both 1.
            let zero = d.zero();
            let one = d.num(1);
            let lhs = desc_factorial(d, &p, snp, zero);
            let lhs_eq = d.lemma(p.desc_factorial_zero, &[snp]); // Eq(lhs, one)

            let fact0 = d.factorial(zero);
            let fact0_eq = d.lemma(p.factorial_zero, &[]); // Eq(fact0, one)
            let choose_snp0 = d.choose(snp, zero);
            let choose_eq = d.lemma(p.choose_zero_right, &[snp]); // Eq(choose_snp0, one)
            let rhs = d.mul(fact0, choose_snp0);
            let step1 = d.congr(fact0, one, fact0_eq, &|d, x| {
                let choose_snp0 = d.choose(snp, zero);
                d.mul(x, choose_snp0)
            });
            let mid1 = d.mul(one, choose_snp0);
            let step2 = d.congr(choose_snp0, one, choose_eq, &|d, x| d.mul(one, x));
            let mid2 = d.mul(one, one);
            let one_mul_eq = d.lemma(p.one_mul, &[one]);
            let (_e, rhs_chain) = d.chain(rhs, &[(mid1, step1), (mid2, step2), (one, one_mul_eq)]);
            let rhs_rev = d.symm(rhs, one, rhs_chain);
            d.trans(lhs, one, rhs, lhs_eq, rhs_rev)
        },
        &|d, j, _k_ih| {
            // k = succ j : the genuine step, chaining six identities.
            let sj = d.succ(j);

            let start = desc_factorial(d, &p, snp, sj);
            // Step 1: desc_factorial_succ_eq_succ_mul(np, j) — the front-peel identity.
            let step1 = d.lemma(p.desc_factorial_succ_eq_succ_mul, &[np, j]);
            let df_np_j = desc_factorial(d, &p, np, j);
            let target1 = d.mul(snp, df_np_j);

            // Step 2: rewrite descFactorial(np, j) via the OUTER ih at j.
            let ih_j = d.apply(ih, &[j]);
            let fact_j = d.factorial(j);
            let choose_np_j = d.choose(np, j);
            let fact_choose = d.mul(fact_j, choose_np_j);
            let step2 = d.congr(df_np_j, fact_choose, ih_j, &|d, x| d.mul(snp, x));
            let target2 = d.mul(snp, fact_choose);

            // Step 3: mul_left_comm — snp*(fact_j*choose_np_j) = fact_j*(snp*choose_np_j).
            let step3 = mul_left_comm(d, &p, snp, fact_j, choose_np_j);
            let snp_choose = d.mul(snp, choose_np_j);
            let target3 = d.mul(fact_j, snp_choose);

            // Step 4: succ_mul_choose_eq(np, j), reversed, congr'd under mul(fact_j, ·).
            let choose_snp_sj = d.choose(snp, sj);
            let sj_choose = d.mul(sj, choose_snp_sj);
            let choose_step = d.lemma(p.succ_mul_choose_eq, &[np, j]); // Eq(sj_choose, snp_choose)
            let choose_step_rev = d.symm(sj_choose, snp_choose, choose_step); // Eq(snp_choose, sj_choose)
            let step4 = d.congr(snp_choose, sj_choose, choose_step_rev, &|d, x| {
                d.mul(fact_j, x)
            });
            let target4 = d.mul(fact_j, sj_choose);

            // Step 5: mul_assoc(fact_j, sj, choose_snp_sj), reversed.
            let fact_j_sj = d.mul(fact_j, sj);
            let target5 = d.mul(fact_j_sj, choose_snp_sj);
            let assoc_eq = d.lemma(p.mul_assoc, &[fact_j, sj, choose_snp_sj]); // Eq(target5, target4)
            let step5 = d.symm(target5, target4, assoc_eq); // Eq(target4, target5)

            // Step 6: factorial_succ(j), reversed, congr'd under mul(·, choose_snp_sj).
            let fact_sj = d.factorial(sj);
            let fact_succ_eq = d.lemma(p.factorial_succ, &[j]); // Eq(fact_sj, fact_j_sj)
            let fact_succ_rev = d.symm(fact_sj, fact_j_sj, fact_succ_eq); // Eq(fact_j_sj, fact_sj)
            let step6 = d.congr(fact_j_sj, fact_sj, fact_succ_rev, &|d, x| {
                d.mul(x, choose_snp_sj)
            });
            let target6 = d.mul(fact_sj, choose_snp_sj);

            let (_e, proof) = d.chain(
                start,
                &[
                    (target1, step1),
                    (target2, step2),
                    (target3, step3),
                    (target4, step4),
                    (target5, step5),
                    (target6, step6),
                ],
            );
            proof
        },
        k,
    );
    d.lam_fv(k_fv, nat, body)
}

/// `Nat.descFactorial n k = k! * n.choose k` — the falling-factorial /
/// binomial-coefficient bridge. Confirmed absent (no `descFactorial_eq_…` or
/// `…_eq_choose_mul` name, and no cross-reference to `choose` anywhere in
/// `desc_factorial.rs`/`binomial.rs`/`choose.rs`) before this landed — the
/// "genuine divisibility induction" `F:ml430-nat-factorial-dvd-descfactorial-bbf6124f`
/// was deferred pending.
///
/// Induction on `n`, `k` generalized inside the motive (mirroring
/// [`NatPrelude::succ_mul_choose_eq`]'s own outer induction — see
/// [`desc_choose_succ_all_k`] for the successor step's six-identity chain).
pub(super) fn declare_desc_factorial_eq_factorial_mul_choose(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, n_val: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let df = desc_factorial(d, &p, n_val, k);
        let fact_k = d.factorial(k);
        let choose_nk = d.choose(n_val, k);
        let rhs = d.mul(fact_k, choose_nk);
        let eqn = d.eq(df, rhs);
        d.pi_fv(k_fv, nat, eqn)
    };

    d.theorem(p.desc_factorial_eq_factorial_mul_choose, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let df = desc_factorial(d, &p, n, k);
        let fact_k = d.factorial(k);
        let choose_nk = d.choose(n, k);
        let rhs = d.mul(fact_k, choose_nk);
        let stmt = d.eq(df, rhs);

        let all_k = d.induct(
            &motive,
            &|d| desc_choose_base_all_k(d, &p),
            &|d, np, ih| desc_choose_succ_all_k(d, &p, np, ih),
            n,
        );
        let proof = d.apply(all_k, &[k]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `factorial_dvd_descFactorial : ∀ n k, k! ∣ n.descFactorial k`. Closes
/// `F:ml430-nat-factorial-dvd-descfactorial-bbf6124f`. Immediate from
/// [`declare_desc_factorial_eq_factorial_mul_choose`] plus `Nat.dvd_mul`
/// (`a ∣ a*q`), transported along the bridge equation.
pub(super) fn declare_factorial_dvd_desc_factorial(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.factorial_dvd_desc_factorial, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let fact_k = d.factorial(k);
        let df = desc_factorial(d, &p, n, k);
        let stmt = d.dvd(fact_k, df);

        let choose_nk = d.choose(n, k);
        let from = d.mul(fact_k, choose_nk);
        let dvd_proof = d.lemma(p.dvd_mul, &[fact_k, choose_nk]); // dvd(fact_k, from)
        let bridge_eq = d.lemma(p.desc_factorial_eq_factorial_mul_choose, &[n, k]); // Eq(df, from)
        let bridge_eq_rev = d.symm(df, from, bridge_eq); // Eq(from, df)
        let proof = transport_dvd_right(d, fact_k, from, df, bridge_eq_rev, dvd_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `descFactorial_self : ∀ n, n.descFactorial n = n.factorial`. Closes
/// `F:ml430-nat-descfactorial-self-899fc0e0`. Immediate from
/// [`declare_desc_factorial_eq_factorial_mul_choose`] at `k := n`
/// (`descFactorial n n = n! * choose n n`), then `choose_self` (`choose n n
/// = 1`) and `mul_one` collapse the right-hand side to `n!`.
pub(super) fn declare_desc_factorial_self(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.desc_factorial_self, 1, &|d, v| {
        let n = v[0];
        let df = desc_factorial(d, &p, n, n);
        let fact_n = d.factorial(n);
        let stmt = d.eq(df, fact_n);

        // bridge : Eq(df, mul(fact_n, choose(n, n)))
        let bridge = d.lemma(p.desc_factorial_eq_factorial_mul_choose, &[n, n]);
        let choose_nn = d.choose(n, n);
        let mul_fact_choose = d.mul(fact_n, choose_nn);
        let choose_self_eq = d.lemma(p.choose_self, &[n]); // Eq(choose_nn, 1)
        let one = d.num(1);
        let step1 = d.congr(choose_nn, one, choose_self_eq, &|d, x| d.mul(fact_n, x));
        let mid = d.mul(fact_n, one);
        let mul_one_eq = d.lemma(p.mul_one, &[fact_n]); // Eq(mid, fact_n)
        let (_e, rhs_chain) = d.chain(mul_fact_choose, &[(mid, step1), (fact_n, mul_one_eq)]);
        let proof = d.trans(df, mul_fact_choose, fact_n, bridge, rhs_chain);
        (stmt, proof)
    })?;
    Ok(())
}

/// `descFactorial_le : ∀ n {k m}, k ≤ m → k.descFactorial n ≤
/// m.descFactorial n` — monotone in the base for fixed exponent `n`. Closes
/// `F:ml430-nat-descfactorial-le-2b8cc09a`.
///
/// Route: rewrite `Le (choose k n) (choose m n)`
/// ([`NatPrelude::choose_le_choose`], directly from the hypothesis) up to
/// `Le (mul (factorial n) (choose k n)) (mul (factorial n) (choose m n))`
/// ([`NatPrelude::mul_le_mul_left`]), then transport twice along
/// [`declare_desc_factorial_eq_factorial_mul_choose`]'s bridge equations (at
/// `(k, n)` and `(m, n)`, both reversed) to land on
/// `Le (descFactorial k n) (descFactorial m n)`.
pub(super) fn declare_desc_factorial_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.desc_factorial_le, 3, &|d, v| {
        let (n, k, m) = (v[0], v[1], v[2]);
        let le_ty = d.le(k, m);
        let df_k = desc_factorial(d, &p, k, n);
        let df_m = desc_factorial(d, &p, m, n);
        let concl = d.le(df_k, df_m);
        let stmt = d.arrow(le_ty, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let choose_kn = d.choose(k, n);
        let choose_mn = d.choose(m, n);
        // Le(choose_kn, choose_mn)
        let choose_step = d.lemma(p.choose_le_choose, &[k, m, n, h]);
        let fact_n = d.factorial(n);
        // Le(mul(fact_n, choose_kn), mul(fact_n, choose_mn))
        let mul_step = d.lemma(
            p.mul_le_mul_left,
            &[fact_n, choose_kn, choose_mn, choose_step],
        );
        let mul_k = d.mul(fact_n, choose_kn);
        let mul_m = d.mul(fact_n, choose_mn);

        let bridge_k = d.lemma(p.desc_factorial_eq_factorial_mul_choose, &[k, n]); // Eq(df_k, mul_k)
        let bridge_k_rev = d.symm(df_k, mul_k, bridge_k); // Eq(mul_k, df_k)
        let bridge_m = d.lemma(p.desc_factorial_eq_factorial_mul_choose, &[m, n]); // Eq(df_m, mul_m)
        let bridge_m_rev = d.symm(df_m, mul_m, bridge_m); // Eq(mul_m, df_m)

        // transport Le(mul_k, mul_m) along Eq(mul_k, df_k) -> Le(df_k, mul_m)
        let motive1 = d.eq_motive(mul_k, &|d, x| d.le(x, mul_m));
        let step_a = d.transport(mul_k, motive1, mul_step, df_k, bridge_k_rev);

        // transport Le(df_k, mul_m) along Eq(mul_m, df_m) -> Le(df_k, df_m)
        let motive2 = d.eq_motive(mul_m, &|d, x| d.le(df_k, x));
        let step_b = d.transport(mul_m, motive2, step_a, df_m, bridge_m_rev);

        let body = d.lam_fv(h_fv, le_ty, step_b);
        (stmt, body)
    })?;
    Ok(())
}

/// `self_le_factorial : ∀ n, n ≤ n.factorial`. Closes
/// `F:ml430-nat-self-le-factorial-cfdffc69`. Independent of the
/// `descFactorial`/`choose` bridge above — a direct induction on `n` using
/// [`NatPrelude::one_le_factorial`] (`1 ≤ n!`), not this file's induction
/// hypothesis, to bound the step.
///
/// - `n = 0`: `Le 0 (factorial 0)` is [`NatPrelude::zero_le`] directly.
/// - `n = succ j`: `factorial (succ j) ≡ factorial j * succ j`
///   ([`NatPrelude::factorial_succ`], defeq); scale
///   [`NatPrelude::one_le_factorial`] at `j` (`Le 1 (factorial j)`, NOT the
///   induction hypothesis, which only bounds `j` itself and is too weak) by
///   `succ j` via [`NatPrelude::mul_le_mul_left`] to get
///   `Le (succ j * 1) (succ j * factorial j)`, rewrite `succ j * 1 = succ j`
///   ([`NatPrelude::mul_one`]) and commute the right side
///   ([`NatPrelude::mul_comm`]) to land on `Le (succ j) (factorial j * succ
///   j)`, then transport along `factorial_succ` (reversed) to the goal.
pub(super) fn declare_self_le_factorial(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let fact_x = d.factorial(x);
        d.le(x, fact_x)
    };

    d.theorem(p.self_le_factorial, 1, &|d, v| {
        let n = v[0];
        let stmt = motive(d, n);

        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let fact0 = d.factorial(zero);
                d.lemma(p.zero_le, &[fact0])
            },
            &|d, j, _ih| {
                let sj = d.succ(j);
                let one = d.num(1);
                let fact_j = d.factorial(j);

                let one_le_j = d.lemma(p.one_le_factorial, &[j]); // Le(1, fact_j)
                // Le(mul(sj, 1), mul(sj, fact_j))
                let mul_step = d.lemma(p.mul_le_mul_left, &[sj, one, fact_j, one_le_j]);

                let sj_mul_one = d.mul(sj, one);
                let mul_one_eq = d.lemma(p.mul_one, &[sj]); // Eq(sj_mul_one, sj)
                let sj_fact_j = d.mul(sj, fact_j);
                let motive_a = d.eq_motive(sj_mul_one, &|d, x| d.le(x, sj_fact_j));
                // Le(sj, mul(sj, fact_j))
                let step_a = d.transport(sj_mul_one, motive_a, mul_step, sj, mul_one_eq);

                let mul_comm_eq = d.lemma(p.mul_comm, &[sj, fact_j]); // Eq(sj_fact_j, fact_j_sj)
                let fact_j_sj = d.mul(fact_j, sj);
                let motive_b = d.eq_motive(sj_fact_j, &|d, x| d.le(sj, x));
                // Le(sj, mul(fact_j, sj))
                let step_b = d.transport(sj_fact_j, motive_b, step_a, fact_j_sj, mul_comm_eq);

                let fact_sj = d.factorial(sj);
                let fact_succ_eq = d.lemma(p.factorial_succ, &[j]); // Eq(fact_sj, fact_j_sj)
                let fact_succ_rev = d.symm(fact_sj, fact_j_sj, fact_succ_eq); // Eq(fact_j_sj, fact_sj)
                let motive_c = d.eq_motive(fact_j_sj, &|d, x| d.le(sj, x));
                // Le(sj, fact_sj)
                d.transport(fact_j_sj, motive_c, step_b, fact_sj, fact_succ_rev)
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare [`declare_desc_factorial`], then [`declare_desc_factorial_one`],
/// [`declare_desc_factorial_of_lt`], and the falling-factorial / `choose`
/// bridge ([`declare_desc_factorial_succ_eq_succ_mul`],
/// [`declare_desc_factorial_eq_factorial_mul_choose`],
/// [`declare_factorial_dvd_desc_factorial`],
/// [`declare_desc_factorial_self`], [`declare_desc_factorial_le`]), which
/// need `Nat.choose` / `Nat.factorial` / `Nat.succ_mul_choose_eq` /
/// `Nat.dvd_mul` / `Nat.choose_self` / `Nat.choose_le_choose` /
/// `Nat.mul_le_mul_left`, all declared far earlier in the prelude build.
pub(super) fn declare_desc_factorial_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_desc_factorial(d, p)?;
    declare_desc_factorial_one(d, p)?;
    declare_desc_factorial_of_lt(d, p)?;
    declare_desc_factorial_succ_eq_succ_mul(d, p)?;
    declare_desc_factorial_eq_factorial_mul_choose(d, p)?;
    declare_factorial_dvd_desc_factorial(d, p)?;
    declare_desc_factorial_self(d, p)?;
    declare_desc_factorial_le(d, p)?;
    declare_self_le_factorial(d, p)?;
    Ok(())
}
