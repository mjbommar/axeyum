//! `Nat.gcd_comm` — the one piece of load-bearing infrastructure this file
//! lands toward `Nat.totient`'s multiplicative formula
//! (`totient(m*n) = totient(m)*totient(n)` for `Coprime m n`).
//!
//! Filed here rather than in `gcd.rs`/`lcm.rs` (where it conceptually
//! belongs, beside `Nat.lcm_comm`) because this task's brief holds those
//! files off-limits to a concurrent sibling lane's edits; a new file avoids
//! any collision risk. It needed no new induction: `Nat.gcd_dvd_left`,
//! `Nat.gcd_dvd_right`, `Nat.dvd_gcd`, and `Nat.dvd_antisymm` were already
//! enough, via the identical two-mutual-divisibility-then-antisymmetry shape
//! `Nat.lcm_comm` (`lcm.rs::declare_lcm_comm`) already uses for `lcm`. Both
//! `gcd a b | gcd b a` and `gcd b a | gcd a b` follow from `dvd_gcd` fed the
//! matching `gcd_dvd_left`/`gcd_dvd_right` witnesses with the endpoints
//! swapped; `dvd_antisymm` closes it.
//!
//! ## Why this was worth landing on its own
//!
//! `gcd_comm` has been repeatedly flagged as ABSENT from this prelude across
//! three prior totient triages (`docs/plan/status/287-nat-totient.md`,
//! `291-totient-counting.md`, `295-totient-even.md`) and was blocking a
//! concrete step in `295`'s own `totient_even` plan (the
//! `gcd (n-k) n = gcd k n`-shaped chain). It turned out to be a three-lemma,
//! zero-induction composition once the right three pieces (`gcd_dvd_left`,
//! `gcd_dvd_right`, `dvd_gcd`, all pre-existing) were checked directly rather
//! than assumed missing — the standing lesson in this repository's own
//! CLAUDE.md ("the lemma you need usually exists") applied to itself.
//!
//! It is genuinely needed for the multiplicative-formula plan this file's
//! sibling handoff doc
//! (`docs/plan/status/301-totient-multiplicative.md`) describes: totient's
//! own predicate is `gcd k n` (index first, modulus second — see
//! `totient.rs`), while the CRT-style mod-invariance step
//! (`gcd (x mod m) m = gcd x m`, needed to show the residue-pairing map
//! preserves coprimality) falls out of the existing Euclidean recursion
//! equation `Nat.gcd_succ : gcd (succ k) n = gcd (mod n (succ k)) (succ k)`
//! with the ARGUMENTS IN THE OTHER ORDER — `gcd_succ` gives
//! `gcd m x = gcd (x mod m) m`, and bridging that to `gcd x m` needs exactly
//! `gcd_comm`. No route through this plan avoids needing it.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.gcd_comm : ∀ a b, Eq (gcd a b) (gcd b a)`. See the module doc for the
/// mutual-divisibility-then-antisymmetry route, identical in shape to
/// `Nat.lcm_comm`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gcd_comm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gcd_comm, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let gcd_ab = d.gcd(a, b);
        let gcd_ba = d.gcd(b, a);

        // dvd (gcd a b) (gcd b a): gcd a b divides both b and a (in that
        // order), so dvd_gcd(gcd_ab, b, a, ..) gives dvd gcd_ab (gcd b a).
        let dvd_gcdab_b = d.lemma(p.gcd_dvd_right, &[a, b]); // dvd gcd_ab b
        let dvd_gcdab_a = d.lemma(p.gcd_dvd_left, &[a, b]); // dvd gcd_ab a
        let forward = d.lemma(p.dvd_gcd, &[gcd_ab, b, a, dvd_gcdab_b, dvd_gcdab_a]);

        // dvd (gcd b a) (gcd a b): symmetric.
        let dvd_gcdba_a = d.lemma(p.gcd_dvd_right, &[b, a]); // dvd gcd_ba a
        let dvd_gcdba_b = d.lemma(p.gcd_dvd_left, &[b, a]); // dvd gcd_ba b
        let backward = d.lemma(p.dvd_gcd, &[gcd_ba, a, b, dvd_gcdba_a, dvd_gcdba_b]);

        let proof = d.lemma(p.dvd_antisymm, &[gcd_ab, gcd_ba, forward, backward]);
        (d.eq(gcd_ab, gcd_ba), proof)
    })?;
    Ok(())
}

/// `2 ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x` — primality, spelled inline. Local
/// copy of `primes.rs`'s private helper of the same name and construction,
/// per this file's own local-copies-per-file convention (`primes.rs` is not
/// this task's file to edit).
fn prime_condition(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let unit = d.num(1);
    let lower = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hypothesis = d.dvd(c, x);
    let trivial = d.eq(c, unit);
    let whole = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[trivial, whole]);
    let body = d.arrow(hypothesis, disjunction);
    let divisors = d.pi_fv(c_fv, nat, body);
    d.const_app(p.logic.and, &[lower, divisors])
}

/// `Nat.coprime_mul_of_coprime : ∀ x m n, Eq (gcd x m) one → Eq (gcd x n)
/// one → Eq (gcd x (mul m n)) one` (Mathlib's `Nat.Coprime.mul_right`). See
/// the field doc / module doc for the route: `coprime_of_forall_prime_dvd`
/// fed a hypothesis built from `euclid_lemma` plus `dvd_gcd`, transported
/// along each of the two coprimality hypotheses in turn.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_mul_of_coprime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.coprime_mul_of_coprime, 3, &|d, v| {
        let x = v[0];
        let m = v[1];
        let n = v[2];
        let one = d.num(1);

        let gcd_x_m = d.gcd(x, m);
        let gcd_x_n = d.gcd(x, n);
        let h_xm_ty = d.eq(gcd_x_m, one);
        let h_xn_ty = d.eq(gcd_x_n, one);
        let mul_mn = d.mul(m, n);
        let gcd_x_mn = d.gcd(x, mul_mn);
        let target = d.eq(gcd_x_mn, one);

        let h_xm_fv = d.fresh_fvar();
        let h_xm = d.kernel().fvar(h_xm_fv);
        let h_xn_fv = d.fresh_fvar();
        let h_xn = d.kernel().fvar(h_xn_fv);

        // `hyp : ∀ k, prime_condition k → dvd k x → dvd k (mul m n) → dvd k
        // one`, the argument `coprime_of_forall_prime_dvd` needs at `(x, mul
        // m n)`.
        let hyp_for_call = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let prime_k_ty = prime_condition(d, &p, k);
            let dvd_k_x_ty = d.dvd(k, x);
            let dvd_k_mn_ty = d.dvd(k, mul_mn);
            let dvd_k_one_ty = d.dvd(k, one);

            let prime_fv = d.fresh_fvar();
            let prime_k = d.kernel().fvar(prime_fv);
            let hkx_fv = d.fresh_fvar();
            let hkx = d.kernel().fvar(hkx_fv);
            let hkmn_fv = d.fresh_fvar();
            let hkmn = d.kernel().fvar(hkmn_fv);

            let disj = d.lemma(p.euclid_lemma, &[k, m, n, prime_k, hkmn]); // Or (dvd k m) (dvd k n)
            let dvd_k_m_ty = d.dvd(k, m);
            let dvd_k_n_ty = d.dvd(k, n);

            let on_m = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv); // dvd k m
                let dvd_k_gcdxm = d.lemma(p.dvd_gcd, &[k, x, m, hkx, h2]); // dvd k (gcd x m)
                let motive = d.eq_motive(gcd_x_m, &|d, z| d.dvd(k, z));
                let result = d.transport(gcd_x_m, motive, dvd_k_gcdxm, one, h_xm); // dvd k one
                d.lam_fv(h2_fv, dvd_k_m_ty, result)
            };
            let on_n = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv); // dvd k n
                let dvd_k_gcdxn = d.lemma(p.dvd_gcd, &[k, x, n, hkx, h2]); // dvd k (gcd x n)
                let motive = d.eq_motive(gcd_x_n, &|d, z| d.dvd(k, z));
                let result = d.transport(gcd_x_n, motive, dvd_k_gcdxn, one, h_xn); // dvd k one
                d.lam_fv(h2_fv, dvd_k_n_ty, result)
            };
            let body = d.const_app(
                p.logic.or_elim,
                &[dvd_k_m_ty, dvd_k_n_ty, dvd_k_one_ty, disj, on_m, on_n],
            );

            let with_hkmn = d.lam_fv(hkmn_fv, dvd_k_mn_ty, body);
            let with_hkx = d.lam_fv(hkx_fv, dvd_k_x_ty, with_hkmn);
            let with_prime = d.lam_fv(prime_fv, prime_k_ty, with_hkx);
            d.lam_fv(k_fv, nat, with_prime)
        };

        let proof_inner = d.lemma(p.coprime_of_forall_prime_dvd, &[x, mul_mn, hyp_for_call]);

        let inner_stmt = d.arrow(h_xn_ty, target);
        let stmt = d.arrow(h_xm_ty, inner_stmt);
        let inner_proof = d.lam_fv(h_xn_fv, h_xn_ty, proof_inner);
        let proof = d.lam_fv(h_xm_fv, h_xm_ty, inner_proof);
        (stmt, proof)
    })?;
    Ok(())
}
