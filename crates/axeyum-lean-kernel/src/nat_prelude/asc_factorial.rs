//! `Nat.ascFactorial n k = n * (n+1) * … * (n+k-1)` (`k` factors), by
//! structural recursion on `k` — mirroring [`super::desc_factorial`] exactly,
//! but climbing with `Nat.add` instead of descending with truncated
//! `Nat.sub`:
//!
//! ```text
//! ascFactorial n zero     ≡ 1
//! ascFactorial n (succ k) ≡ (n + k) * ascFactorial n k
//! ```
//!
//! Mirrors Mathlib's `Nat.ascFactorial` (`Mathlib.Data.Nat.Factorial.Basic`):
//! `ascFactorial (n : ℕ) : ℕ → ℕ | 0 => 1 | k + 1 => (n + k) * ascFactorial n k`.
//! Structural in `k`, built with the same [`NatOps::define_binary`]
//! combinator `Nat.sub`/`Nat.mul`/`Nat.descFactorial` already use for a
//! two-argument, second-argument recursion — so
//! [`declare_asc_factorial`]'s two equation theorems hold by `Eq.refl`
//! (β/δ/ι), no fuel device needed.
//!
//! Unlike `descFactorial`, `Nat.add` never truncates, so there is no
//! analogue of `descFactorial_of_lt`'s zero boundary here — `ascFactorial`
//! is `0` only when `n = 0` and `k ≥ 1` (Mathlib's `Nat.zero_ascFactorial`),
//! which this module does not prove. [`declare_asc_factorial_one`] is the
//! boundary lemma this slice lands, mirroring
//! [`super::desc_factorial::declare_desc_factorial_one`] exactly: `n *
//! ascFactorial n 1` reduces to `n * 1` by pure β/δ/ι, and `Nat.mul_one`
//! closes it directly.
//!
//! Evaluation test (`nat_prelude_tests::asc_factorial_evaluates_correctly`):
//! `ascFactorial 3 2 = 3 * 4 = 12`, `ascFactorial 5 0 = 1`, with a negative
//! control that a *descending* product (`5 * 4 = 20`, i.e. `descFactorial`'s
//! answer) is a DIFFERENT value — catching a copy-paste that reused `sub`
//! instead of `add` in the step function, which would still type-check
//! (`Nat → Nat → Nat` either way) but compute the wrong value.

use super::NatPrelude;
use super::binomial::mul_left_comm;
use super::helpers::{transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.ascFactorial n k`.
fn asc_factorial(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.asc_factorial, &[n, k])
}

/// `Nat.ascFactorial : Nat → Nat → Nat`, structural recursion on the
/// **second** argument via [`NatOps::define_binary`] — the same combinator
/// [`super::desc_factorial::declare_desc_factorial`] uses — so
/// `ascFactorial_zero`/`ascFactorial_succ` below hold by `Eq.refl` (β/δ/ι)
/// and exist only so callers can rewrite by name.
pub(super) fn declare_asc_factorial(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    // ascFactorial n zero ≡ 1 ; ascFactorial n (succ k) ≡ (n + k) * ascFactorial n k
    d.define_binary(p.asc_factorial, 3, &|d, _n| d.num(1), &|d, n, k, ih| {
        let n_plus_k = d.add(n, k);
        d.mul(n_plus_k, ih)
    })?;

    // ascFactorial_zero : ∀ n, n.ascFactorial 0 = 1
    d.theorem(p.asc_factorial_zero, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let lhs = asc_factorial(d, &p, n, zero);
        let one = d.num(1);
        (d.eq(lhs, one), d.refl(one))
    })?;

    // ascFactorial_succ : ∀ n k, n.ascFactorial (succ k) = (n + k) * n.ascFactorial k
    d.theorem(p.asc_factorial_succ, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let sk = d.succ(k);
        let lhs = asc_factorial(d, &p, n, sk);
        let prior = asc_factorial(d, &p, n, k);
        let n_plus_k = d.add(n, k);
        let rhs = d.mul(n_plus_k, prior);
        (d.eq(lhs, rhs), d.refl(rhs))
    })?;

    Ok(())
}

/// `ascFactorial_one : ∀ n, n.ascFactorial 1 = n`.
///
/// `n.ascFactorial 1` reduces (`ascFactorial_succ` at `k := 0`,
/// definitionally) to `(n + 0) * n.ascFactorial 0`, and `n + 0 ≡ n` is
/// itself definitional (`Nat.add`'s own base case, right-recursive, holds
/// for any `n`). So the stated goal is defeq to `n * 1 = n`, and
/// `mul_one`'s own proof term closes it directly — no explicit rewrite
/// needed, exactly mirroring
/// [`super::desc_factorial::declare_desc_factorial_one`].
pub(super) fn declare_asc_factorial_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.asc_factorial_one, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let lhs = asc_factorial(d, &p, n, one);
        let proof = d.lemma(p.mul_one, &[n]);
        (d.eq(lhs, n), proof)
    })?;
    Ok(())
}

/// `zero_ascFactorial_succ : ∀ k, (0:Nat).ascFactorial (succ k) = 0` — the
/// ascending analogue of `descFactorial_of_lt`'s truncation boundary: the
/// LEADING factor of `ascFactorial 0 (succ k)` is `0` itself once there is
/// at least one factor, so the whole product collapses regardless of `k`.
///
/// Proved by induction on `k`: `k = 0` is exactly `ascFactorial_one` at
/// `n := 0` (`ascFactorial 0 1 = 0`); `k = succ j` multiplies by the IH
/// (`ascFactorial 0 (succ j) = 0`) via `asc_factorial_succ` + `mul_zero`, so
/// the leading factor `0 + succ j` never even needs computing.
pub(super) fn declare_zero_asc_factorial_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.zero_asc_factorial_succ, 1, &|d, v| {
        let k = v[0];
        let zero = d.zero();

        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sx = d.succ(x);
            let af = asc_factorial(d, &p, zero, sx);
            let target_zero = d.zero();
            d.eq(af, target_zero)
        };
        let stmt = motive(d, k);

        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.lemma(p.asc_factorial_one, &[zero])
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let ssj = d.succ(sj);
                let zero = d.zero();
                let af_sj = asc_factorial(d, &p, zero, sj);
                let start = asc_factorial(d, &p, zero, ssj);
                let step1 = d.lemma(p.asc_factorial_succ, &[zero, sj]);
                let sum = d.add(zero, sj);
                let mid = d.mul(sum, af_sj);
                let step2 = d.congr(af_sj, zero, ih, &|d, x| {
                    let sum = d.add(zero, sj);
                    d.mul(sum, x)
                });
                let mid2 = d.mul(sum, zero);
                let mul_zero_eq = d.lemma(p.mul_zero, &[sum]);
                let (_e, proof) =
                    d.chain(start, &[(mid, step1), (mid2, step2), (zero, mul_zero_eq)]);
                proof
            },
            k,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `ascFactorial_succ_eq_factorial_mul_choose : ∀ m k, (succ m).ascFactorial k
/// = k! * (m + k).choose k` — the subtraction-free rising-factorial /
/// binomial-coefficient bridge. Reindexed by `n := succ m` (so `n - 1`
/// never needs `Nat.sub`, hence no `n ≥ 1` truncation guard is ever needed)
/// and `(m+k).choose k` (so the addition is between two already-bound
/// variables, never a subtraction).
///
/// Proved by induction on `k`, `m` held fixed (it never changes across the
/// recursion, unlike [`declare_desc_factorial_eq_factorial_mul_choose`]'s
/// outer induction on `n` — here there is no `n = 0` boundary to handle
/// separately, because `n := succ m` is never `0`). The `k = succ j` step
/// chains eight identities: `asc_factorial_succ`, the IH at `j`,
/// [`mul_left_comm`], `succ_add` (aligning `succ m + j` with
/// `succ_mul_choose_eq`'s `succ n'` shape), [`NatPrelude::succ_mul_choose_eq`],
/// `add_succ` (aligning `succ (m+j)` back to `m + succ j`), `mul_assoc`
/// (reversed), and `factorial_succ` (reversed) — the same six-step chain
/// [`super::desc_factorial::declare_desc_factorial_eq_factorial_mul_choose`]
/// uses, plus the two extra addition-alignment rewrites this reindexing
/// needs.
pub(super) fn declare_asc_factorial_succ_eq_factorial_mul_choose(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.asc_factorial_succ_eq_factorial_mul_choose, 2, &|d, v| {
        let (m, k) = (v[0], v[1]);
        let sm = d.succ(m);

        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let af = asc_factorial(d, &p, sm, x);
            let fact_x = d.factorial(x);
            let m_plus_x = d.add(m, x);
            let choose_mx = d.choose(m_plus_x, x);
            let rhs = d.mul(fact_x, choose_mx);
            d.eq(af, rhs)
        };
        let stmt = motive(d, k);

        let proof = d.induct(
            &motive,
            &|d| {
                // k = 0 : ascFactorial(succ m) 0 = 1 = factorial 0 * choose(m+0) 0.
                let zero = d.zero();
                let one = d.num(1);
                let af = asc_factorial(d, &p, sm, zero);
                let af_eq = d.lemma(p.asc_factorial_zero, &[sm]); // Eq(af, one)

                let fact0 = d.factorial(zero);
                let fact0_eq = d.lemma(p.factorial_zero, &[]); // Eq(fact0, one)
                let m_plus_0 = d.add(m, zero);
                let choose_m0 = d.choose(m_plus_0, zero);
                let choose_eq = d.lemma(p.choose_zero_right, &[m_plus_0]); // Eq(choose_m0, one)
                let rhs = d.mul(fact0, choose_m0);
                let step1 = d.congr(fact0, one, fact0_eq, &|d, x| {
                    let m_plus_0 = d.add(m, zero);
                    let choose_m0 = d.choose(m_plus_0, zero);
                    d.mul(x, choose_m0)
                });
                let mid1 = d.mul(one, choose_m0);
                let step2 = d.congr(choose_m0, one, choose_eq, &|d, x| d.mul(one, x));
                let mid2 = d.mul(one, one);
                let one_mul_eq = d.lemma(p.one_mul, &[one]);
                let (_e, rhs_chain) =
                    d.chain(rhs, &[(mid1, step1), (mid2, step2), (one, one_mul_eq)]);
                let rhs_rev = d.symm(rhs, one, rhs_chain);
                d.trans(af, one, rhs, af_eq, rhs_rev)
            },
            &|d, j, ih| {
                // k = succ j : the genuine step, chaining eight identities.
                let sj = d.succ(j);

                let start = asc_factorial(d, &p, sm, sj);
                // Step 1: asc_factorial_succ(sm, j) — start = (sm+j) * ascFactorial(sm, j).
                let step1 = d.lemma(p.asc_factorial_succ, &[sm, j]);
                let sm_plus_j = d.add(sm, j);
                let af_sm_j = asc_factorial(d, &p, sm, j);
                let target1 = d.mul(sm_plus_j, af_sm_j);

                // Step 2: rewrite ascFactorial(sm, j) via ih.
                let fact_j = d.factorial(j);
                let m_plus_j = d.add(m, j);
                let choose_mj = d.choose(m_plus_j, j);
                let fact_choose = d.mul(fact_j, choose_mj);
                let step2 = d.congr(af_sm_j, fact_choose, ih, &|d, x| {
                    let sm_plus_j = d.add(sm, j);
                    d.mul(sm_plus_j, x)
                });
                let target2 = d.mul(sm_plus_j, fact_choose);

                // Step 3: mul_left_comm — (sm+j)*(fact_j*choose_mj) = fact_j*((sm+j)*choose_mj).
                let step3 = mul_left_comm(d, &p, sm_plus_j, fact_j, choose_mj);
                let smj_choose = d.mul(sm_plus_j, choose_mj);
                let target3 = d.mul(fact_j, smj_choose);

                // Step 4: succ_add(m, j) — sm_plus_j = succ(m_plus_j) — rewrite inside
                // fact_j*(sm_plus_j*choose_mj), the FULL target3, not just its inner factor.
                let succ_add_eq = d.lemma(p.succ_add, &[m, j]); // Eq(sm_plus_j, succ(m_plus_j))
                let succ_mj = d.succ(m_plus_j);
                let step4 = d.congr(sm_plus_j, succ_mj, succ_add_eq, &|d, x| {
                    let choose_mj = d.choose(m_plus_j, j);
                    let inner = d.mul(x, choose_mj);
                    d.mul(fact_j, inner)
                });
                let succ_mj_choose = d.mul(succ_mj, choose_mj);
                let target4 = d.mul(fact_j, succ_mj_choose);

                // Step 5: succ_mul_choose_eq(m_plus_j, j), reversed.
                let choose_succ_mj_sj = d.choose(succ_mj, sj);
                let sj_choose2 = d.mul(sj, choose_succ_mj_sj);
                let choose_step = d.lemma(p.succ_mul_choose_eq, &[m_plus_j, j]); // Eq(sj_choose2, succ_mj_choose)
                let choose_step_rev = d.symm(sj_choose2, succ_mj_choose, choose_step); // Eq(succ_mj_choose, sj_choose2)
                let step5 = d.congr(succ_mj_choose, sj_choose2, choose_step_rev, &|d, x| {
                    d.mul(fact_j, x)
                });
                let target5 = d.mul(fact_j, sj_choose2);

                // Step 6: add_succ(m, j) reversed — succ_mj = m + sj — rewrite choose's first arg.
                let add_succ_eq = d.lemma(p.add_succ, &[m, j]); // Eq(m_plus_sj, succ_mj)
                let m_plus_sj = d.add(m, sj);
                let add_succ_rev = d.symm(m_plus_sj, succ_mj, add_succ_eq); // Eq(succ_mj, m_plus_sj)
                let step6 = d.congr(succ_mj, m_plus_sj, add_succ_rev, &|d, x| {
                    let sj = d.succ(j);
                    let c = d.choose(x, sj);
                    let inner = d.mul(sj, c);
                    d.mul(fact_j, inner)
                });
                let choose_m_plus_sj_sj = d.choose(m_plus_sj, sj);
                let sj_choose3 = d.mul(sj, choose_m_plus_sj_sj);
                let target6 = d.mul(fact_j, sj_choose3);

                // Step 7: mul_assoc(fact_j, sj, choose_m_plus_sj_sj), reversed.
                let fact_j_sj = d.mul(fact_j, sj);
                let target7 = d.mul(fact_j_sj, choose_m_plus_sj_sj);
                let assoc_eq = d.lemma(p.mul_assoc, &[fact_j, sj, choose_m_plus_sj_sj]); // Eq(target7, target6)
                let step7 = d.symm(target7, target6, assoc_eq); // Eq(target6, target7)

                // Step 8: factorial_succ(j), reversed.
                let fact_sj = d.factorial(sj);
                let fact_succ_eq = d.lemma(p.factorial_succ, &[j]); // Eq(fact_sj, fact_j_sj)
                let fact_succ_rev = d.symm(fact_sj, fact_j_sj, fact_succ_eq); // Eq(fact_j_sj, fact_sj)
                let step8 = d.congr(fact_j_sj, fact_sj, fact_succ_rev, &|d, x| {
                    d.mul(x, choose_m_plus_sj_sj)
                });
                let target8 = d.mul(fact_sj, choose_m_plus_sj_sj);

                let (_e, proof) = d.chain(
                    start,
                    &[
                        (target1, step1),
                        (target2, step2),
                        (target3, step3),
                        (target4, step4),
                        (target5, step5),
                        (target6, step6),
                        (target7, step7),
                        (target8, step8),
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

/// `factorial_dvd_ascFactorial : ∀ n k, k! ∣ n.ascFactorial k`. Closes
/// `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641`.
///
/// Case-splits `n` (induction on `n` with `k` generalized inside the
/// motive, but the base/step never reference an induction hypothesis — this
/// is a case-split, not a recursion): `n = 0` splits `k` again (`k = 0` via
/// `dvd_refl`; `k = succ j` via [`declare_zero_asc_factorial_succ`] +
/// `dvd_zero`); `n = succ m` via
/// [`declare_asc_factorial_succ_eq_factorial_mul_choose`] + `dvd_mul`,
/// transported along the bridge equation — the same shape
/// [`super::desc_factorial::declare_factorial_dvd_desc_factorial`] uses.
pub(super) fn declare_factorial_dvd_asc_factorial(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, n_val: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fact_k = d.factorial(k);
        let af = asc_factorial(d, &p, n_val, k);
        let eqn = d.dvd(fact_k, af);
        d.pi_fv(k_fv, nat, eqn)
    };

    d.theorem(p.factorial_dvd_asc_factorial, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let fact_k = d.factorial(k);
        let af = asc_factorial(d, &p, n, k);
        let stmt = d.dvd(fact_k, af);

        let all_k = d.induct(
            &motive,
            &|d| {
                // n = 0 : case-split on k.
                let case_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                    let zero = d.zero();
                    let fact_x = d.factorial(x);
                    let af = asc_factorial(d, &p, zero, x);
                    d.dvd(fact_x, af)
                };
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = d.induct(
                    &case_motive,
                    &|d| {
                        // k = 0 : dvd(1, ascFactorial 0 0) — both are 1, dvd_refl.
                        let zero = d.zero();
                        let one = d.num(1);
                        let fact0 = d.factorial(zero);
                        let fact0_eq = d.lemma(p.factorial_zero, &[]); // Eq(fact0, one)
                        let fact0_eq_rev = d.symm(fact0, one, fact0_eq); // Eq(one, fact0)
                        let af00 = asc_factorial(d, &p, zero, zero);
                        let af00_eq = d.lemma(p.asc_factorial_zero, &[zero]); // Eq(af00, one)
                        let af00_eq_rev = d.symm(af00, one, af00_eq); // Eq(one, af00)
                        let dvd_one_one = d.lemma(p.dvd_refl, &[one]); // dvd(one, one)
                        // dvd(one, one) --[divisor one -> fact0]--> dvd(fact0, one)
                        let dvd_fact0_one =
                            transport_dvd_left(d, one, fact0, fact0_eq_rev, one, dvd_one_one);
                        // dvd(fact0, one) --[dividend one -> af00]--> dvd(fact0, af00)
                        transport_dvd_right(d, fact0, one, af00, af00_eq_rev, dvd_fact0_one)
                    },
                    &|d, j, _ih| {
                        // k = succ j : ascFactorial 0 (succ j) = 0, so dvd_zero closes it.
                        let sj = d.succ(j);
                        let zero = d.zero();
                        let fact_sj = d.factorial(sj);
                        let af = asc_factorial(d, &p, zero, sj);
                        let af_eq = d.lemma(p.zero_asc_factorial_succ, &[j]); // Eq(af, zero)
                        let af_eq_rev = d.symm(af, zero, af_eq); // Eq(zero, af)
                        let dvd_zero_proof = d.lemma(p.dvd_zero, &[fact_sj]); // dvd(fact_sj, zero)
                        transport_dvd_right(d, fact_sj, zero, af, af_eq_rev, dvd_zero_proof)
                    },
                    k,
                );
                d.lam_fv(k_fv, nat, body)
            },
            &|d, m, _ih| {
                // n = succ m : use the ascending bridge + dvd_mul, for every k.
                let sm = d.succ(m);
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = {
                    let fact_k = d.factorial(k);
                    let af = asc_factorial(d, &p, sm, k);

                    let m_plus_k = d.add(m, k);
                    let choose_mk = d.choose(m_plus_k, k);
                    let from = d.mul(fact_k, choose_mk);
                    let dvd_proof = d.lemma(p.dvd_mul, &[fact_k, choose_mk]); // dvd(fact_k, from)
                    let bridge_eq = d.lemma(p.asc_factorial_succ_eq_factorial_mul_choose, &[m, k]); // Eq(af, from)
                    let bridge_eq_rev = d.symm(af, from, bridge_eq); // Eq(from, af)
                    transport_dvd_right(d, fact_k, from, af, bridge_eq_rev, dvd_proof)
                };
                d.lam_fv(k_fv, nat, body)
            },
            n,
        );
        let proof = d.apply(all_k, &[k]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare [`declare_asc_factorial`], then [`declare_asc_factorial_one`],
/// which depends only on `Nat.mul_one`, declared far earlier in the prelude
/// build, and the rising-factorial / `choose` bridge
/// ([`declare_zero_asc_factorial_succ`],
/// [`declare_asc_factorial_succ_eq_factorial_mul_choose`],
/// [`declare_factorial_dvd_asc_factorial`]), which need `Nat.choose` /
/// `Nat.factorial` / `Nat.succ_mul_choose_eq` / `Nat.dvd_mul`, all declared
/// far earlier too.
pub(super) fn declare_asc_factorial_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_asc_factorial(d, p)?;
    declare_asc_factorial_one(d, p)?;
    declare_zero_asc_factorial_succ(d, p)?;
    declare_asc_factorial_succ_eq_factorial_mul_choose(d, p)?;
    declare_factorial_dvd_asc_factorial(d, p)?;
    Ok(())
}
