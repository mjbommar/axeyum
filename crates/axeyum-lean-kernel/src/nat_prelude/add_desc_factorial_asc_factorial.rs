//! `Nat.add_descFactorial_eq_ascFactorial : ∀ n k, (n+k).descFactorial k =
//! (n+1).ascFactorial k` -- an `ml430` mirror
//! (`F:ml430-nat-add-descfactorial-eq-ascfactorial-5faac784`).
//!
//! Both sides already have a closed form through the same intermediate,
//! `k! * choose (n+k) k`:
//!
//! - [`NatPrelude::desc_factorial_eq_factorial_mul_choose`]
//!   (`desc_factorial.rs`) instantiated at `(n+k, k)`:
//!   `descFactorial (n+k) k = k! * choose (n+k) k`.
//! - [`NatPrelude::asc_factorial_succ_eq_factorial_mul_choose`]
//!   (`asc_factorial.rs`) instantiated at `(n, k)`:
//!   `ascFactorial (succ n) k = k! * choose (n+k) k` (its own `m+k` is the
//!   SAME `ExprId` as this file's `n+k` when built from the same `n`, `k`).
//!
//! So the whole proof is two lemma applications chained through the shared
//! RHS -- no induction needed here, since both bridges already did the
//! inductive work. Must run after `declare_desc_factorial_all` and
//! `declare_asc_factorial_all`, both far above.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;

/// `Nat.add_descFactorial_eq_ascFactorial`: `∀ n k, (n+k).descFactorial k =
/// (n+1).ascFactorial k`. See the module doc for the route.
pub(super) fn declare_add_desc_factorial_eq_asc_factorial(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_desc_factorial_eq_asc_factorial, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let n_plus_k = d.add(n, k);
        let sn = d.succ(n);

        let df = d.const_app(p.desc_factorial, &[n_plus_k, k]);
        let af = d.const_app(p.asc_factorial, &[sn, k]);
        let fact_k = d.factorial(k);
        let choose_nk = d.choose(n_plus_k, k);
        let rhs = d.mul(fact_k, choose_nk);

        // lemma1 : Eq(df, rhs)
        let lemma1 = d.lemma(p.desc_factorial_eq_factorial_mul_choose, &[n_plus_k, k]);
        // lemma2 : Eq(af, rhs)  -- same rhs `ExprId`, since `asc_factorial_succ_eq_factorial_mul_choose`
        // builds `choose (m+k) k` from the same `m := n`, `k := k`.
        let lemma2 = d.lemma(p.asc_factorial_succ_eq_factorial_mul_choose, &[n, k]);
        let lemma2_rev = d.symm(af, rhs, lemma2); // Eq(rhs, af)

        let proof = d.trans(df, rhs, af, lemma1, lemma2_rev);
        let stmt = d.eq(df, af);
        (stmt, proof)
    })?;
    Ok(())
}
