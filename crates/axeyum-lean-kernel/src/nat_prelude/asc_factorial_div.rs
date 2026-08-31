//! `Nat.ascFactorial_eq_div : ∀ n k, (n+1).ascFactorial k = (n+k)! / n!` --
//! an `ml430` mirror (`F:ml430-nat-ascfactorial-eq-div-87d768e8`).
//!
//! Two already-proved pieces chain straight to it:
//!
//! - [`choose_factorial_add::desc_factorial_add_eq_factorial_at`] (`(*)` in
//!   `choose_factorial_add.rs`'s module doc), instantiated at `(n, k)`:
//!   `descFactorial (n+k) k * n! = (n+k)!`. Converted to the exact-division
//!   form `(n+k)! / n! = descFactorial (n+k) k` by the same "exact factor
//!   divided back out" route [`super::add_choose_div`] and
//!   [`super::coprime_lemmas`]/[`super::lcm_gcd_lemmas`] already use
//!   (`div_eq_of_mul_eq`, copied here per this crate's per-file
//!   local-helper convention), after a `mul_comm` to put the divisor `n!`
//!   on the correct side. `Le 1 n!` comes from
//!   [`NatPrelude::one_le_factorial`].
//! - [`NatPrelude::add_desc_factorial_eq_asc_factorial`]
//!   (`add_desc_factorial_asc_factorial.rs`, `F:ml430-nat-add-descfactorial-
//!   eq-ascfactorial-5faac784`), instantiated at `(n, k)`:
//!   `descFactorial (n+k) k = (n+1).ascFactorial k`.
//!
//! Chaining `(n+k)!/n! = descFactorial(n+k,k) = (n+1).ascFactorial k` and
//! reversing gives the target. No new induction. Must run after
//! `declare_euclidean_division` (`Nat.div`/`div_mul_cancel_of_dvd`/
//! `dvd_mul`), `declare_add_choose_mul_factorial_mul_factorial`
//! (`desc_factorial_add_eq_factorial_at`'s home module), and
//! `declare_add_desc_factorial_eq_asc_factorial`, all above.

use super::NatPrelude;
use super::choose_factorial_add::desc_factorial_add_eq_factorial_at;
use super::helpers::transport_dvd_right;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// Given `mul_eq : Eq (mul k a) b` and `k_pos : Le 1 k`, build a proof of
/// `Eq (div b k) a`. Copied from `add_choose_div.rs`/`coprime_lemmas.rs`/
/// `lcm_gcd_lemmas.rs`'s private helper of the same name and signature.
fn div_eq_of_mul_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    k_pos: ExprId,
    mul_eq: ExprId,
) -> ExprId {
    let p = *p;
    let ka = d.mul(k, a);
    let dvd_k_ka = d.lemma(p.dvd_mul, &[k, a]);
    let dvd_k_b = transport_dvd_right(d, k, ka, b, mul_eq, dvd_k_ka);
    let cancel = d.lemma(p.div_mul_cancel_of_dvd, &[k, b, k_pos, dvd_k_b]);
    let mul_eq_rev = d.symm(ka, b, mul_eq);
    let div_b_k = d.div(b, k);
    let mul_k_divbk = d.mul(k, div_b_k);
    let (_, chained) = d.chain(mul_k_divbk, &[(b, cancel), (ka, mul_eq_rev)]);
    d.lemma(p.mul_left_cancel_of_pos, &[k, div_b_k, a, k_pos, chained])
}

/// `Nat.ascFactorial_eq_div`: `∀ n k, (n+1).ascFactorial k = (n+k)! / n!`.
/// See the module doc for the route.
pub(super) fn declare_asc_factorial_eq_div(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.asc_factorial_eq_div, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let n_plus_k = d.add(n, k);
        let sn = d.succ(n);
        let fact_n = d.factorial(n);
        let fact_nk = d.factorial(n_plus_k);
        let df = d.const_app(p.desc_factorial, &[n_plus_k, k]);
        let af = d.const_app(p.asc_factorial, &[sn, k]);

        // star : Eq(mul(df, fact_n), fact_nk)   -- (*) at (i:=n, j:=k)
        let star = desc_factorial_add_eq_factorial_at(d, &p, n, k);
        let df_mul_n = d.mul(df, fact_n);

        // comm : Eq(mul(fact_n, df), df_mul_n)
        let n_mul_df = d.mul(fact_n, df);
        let comm = d.lemma(p.mul_comm, &[fact_n, df]);

        // mul_eq : Eq(n_mul_df, fact_nk)
        let (_e, mul_eq) = d.chain(n_mul_df, &[(df_mul_n, comm), (fact_nk, star)]);

        // n_pos : Le 1 fact_n
        let n_pos = d.lemma(p.one_le_factorial, &[n]);

        // cancel : Eq(div(fact_nk, fact_n), df)
        let cancel = div_eq_of_mul_eq(d, &p, fact_n, df, fact_nk, n_pos, mul_eq);
        let div_term = d.div(fact_nk, fact_n);

        // bridge : Eq(df, af)  -- add_desc_factorial_eq_asc_factorial(n, k)
        let bridge = d.lemma(p.add_desc_factorial_eq_asc_factorial, &[n, k]);

        // proof : Eq(div_term, af), then flip to Eq(af, div_term).
        let (_e2, div_to_af) = d.chain(div_term, &[(df, cancel), (af, bridge)]);
        let proof = d.symm(div_term, af, div_to_af);

        let stmt = d.eq(af, div_term);
        (stmt, proof)
    })?;
    Ok(())
}
