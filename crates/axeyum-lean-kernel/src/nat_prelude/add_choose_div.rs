//! `Nat.add_choose : ∀ i j, (i+j).choose j = (i+j)! / (i! * j!)` -- an
//! `ml430` mirror (`F:ml430-nat-add-choose-eb49fa11`), the division-normal
//! form of [`NatPrelude::add_choose_mul_factorial_mul_factorial`]
//! (`choose_factorial_add.rs`): `(i+j).choose j * i! * j! = (i+j)!`.
//!
//! Converting a product identity `k * a = b` (with `k` positive) into the
//! exact-division identity `a = b / k` is the "exact factor divided back
//! out" route `coprime_lemmas.rs`'s and `lcm_gcd_lemmas.rs`'s private
//! `div_eq_of_mul_eq` already use for other targets; copied here as a
//! third instance per this crate's per-file local-helper convention (see
//! those two files' module docs for the reasoning behind copying rather
//! than sharing).
//!
//! `Le 1 (i! * j!)`, the positivity hypothesis `div_eq_of_mul_eq` needs,
//! comes from [`NatPrelude::one_le_factorial`] on each factor plus
//! [`NatPrelude::one_le_mul`]. Must run after `declare_euclidean_division`
//! (for `Nat.div`/`div_mul_cancel_of_dvd`/`dvd_mul`) and after
//! `declare_add_choose_mul_factorial_mul_factorial`, both far above.

use super::NatPrelude;
use super::helpers::transport_dvd_right;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// Given `mul_eq : Eq (mul k a) b` and `k_pos : Le 1 k`, build a proof of
/// `Eq (div b k) a` -- the exact factor `k*a` divided back out recovers
/// `a`. Copied from `coprime_lemmas.rs`/`lcm_gcd_lemmas.rs`'s private
/// helper of the same name and signature, per this file's own
/// local-helper convention.
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
    let dvd_k_ka = d.lemma(p.dvd_mul, &[k, a]); // dvd k ka
    let dvd_k_b = transport_dvd_right(d, k, ka, b, mul_eq, dvd_k_ka); // dvd k b
    let cancel = d.lemma(p.div_mul_cancel_of_dvd, &[k, b, k_pos, dvd_k_b]); // Eq (mul k (div b k)) b
    let mul_eq_rev = d.symm(ka, b, mul_eq); // Eq b ka
    let div_b_k = d.div(b, k);
    let mul_k_divbk = d.mul(k, div_b_k);
    let (_, chained) = d.chain(mul_k_divbk, &[(b, cancel), (ka, mul_eq_rev)]);
    // chained : Eq mul_k_divbk ka
    d.lemma(p.mul_left_cancel_of_pos, &[k, div_b_k, a, k_pos, chained]) // Eq div_b_k a
}

/// `Nat.add_choose`: `∀ i j, (i+j).choose j = (i+j)! / (i! * j!)`. See
/// the module doc for the route.
pub(super) fn declare_add_choose(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_choose, 2, &|d, v| {
        let (i, j) = (v[0], v[1]);
        let n_ij = d.add(i, j);
        let choose_ij = d.choose(n_ij, j);
        let fact_i = d.factorial(i);
        let fact_j = d.factorial(j);
        let fact_ij = d.factorial(n_ij);
        let k = d.mul(fact_i, fact_j);

        // h : Eq((choose_ij*i!)*j!, (i+j)!)
        let h = d.lemma(p.add_choose_mul_factorial_mul_factorial, &[i, j]);
        let choose_mul_i = d.mul(choose_ij, fact_i);
        let lhs = d.mul(choose_mul_i, fact_j);

        // assoc : Eq(lhs, mul(choose_ij, k))
        let choose_mul_k = d.mul(choose_ij, k);
        let assoc = d.lemma(p.mul_assoc, &[choose_ij, fact_i, fact_j]);

        // comm : Eq(choose_mul_k, mul(k, choose_ij))
        let k_mul_choose = d.mul(k, choose_ij);
        let comm = d.lemma(p.mul_comm, &[choose_ij, k]);

        // Build mul_eq : Eq(k_mul_choose, fact_ij), i.e. Eq(mul(k, choose_ij), (i+j)!),
        // by chaining k_mul_choose -> choose_mul_k -> lhs -> fact_ij.
        let step1 = d.symm(choose_mul_k, k_mul_choose, comm);
        let step2 = d.symm(lhs, choose_mul_k, assoc);
        let (_e, mul_eq) = d.chain(k_mul_choose, &[(choose_mul_k, step1), (lhs, step2), (fact_ij, h)]);

        // k_pos : Le 1 k
        let one_le_fact_i = d.lemma(p.one_le_factorial, &[i]);
        let one_le_fact_j = d.lemma(p.one_le_factorial, &[j]);
        let k_pos = d.lemma(p.one_le_mul, &[fact_i, fact_j, one_le_fact_i, one_le_fact_j]);

        // cancel : Eq(div(fact_ij, k), choose_ij)
        let cancel = div_eq_of_mul_eq(d, &p, k, choose_ij, fact_ij, k_pos, mul_eq);
        let div_bk = d.div(fact_ij, k);
        let proof = d.symm(div_bk, choose_ij, cancel);

        let stmt = d.eq(choose_ij, div_bk);
        (stmt, proof)
    })?;
    Ok(())
}
