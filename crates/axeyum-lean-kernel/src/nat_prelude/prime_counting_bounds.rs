//! Order and growth theorems about `Nat.primeCounting'`, the prime-counting
//! function — the shelf ADR-1637 deliberately left empty.
//!
//! ## Why this file exists now and did not exist on 2026-09-05
//!
//! `Nat.primeCounting` / `Nat.primeCounting'` (`prime_counting.rs`) were
//! declared as CONSTRUCTIONS ONLY under ADR-0653, because five of the ten
//! rows of the preregistered held-out family
//! `discrete-step-and-counting-bounds` are statements about that pair, and the
//! family had never been scored. ADR-1637's lane declined the whole shelf on
//! that ground.
//!
//! That family moved `held-out -> development` on 2026-09-05
//! (`artifacts/autogenesis/mathlib-nursery-split-policy-v1.json`,
//! `partition_moves`, authority ADR-0542): a producer contract cited
//! `F:ml430-int-le-sub-one-of-not-le-fc32b89d` by name as a `non_example`, and
//! per ADR-0542 the partition unit is the whole family, so all ten rows moved
//! together. The blind-evaluation value was spent by the citation, not by this
//! file; the move is recorded as irreversible. So the shelf is now writable
//! from `development`, and this file is that shelf.
//!
//! **`natural-max-power-dividing` is still held-out** and it carries
//! `Nat.divMaxPow`'s base cases and Bertrand's postulate. Nothing here
//! mentions `Nat.divMaxPow`, by construction.
//!
//! ## `primeCounting'` is `countRange` under two aliases
//!
//! ```text
//! primeCounting' n := Nat.count Nat.isPrime n        (prime_counting.rs)
//! count dec n      := Nat.countRange dec n           (count_and_div_max_pow.rs)
//! ```
//!
//! Both are `Regular` definitions with strictly decreasing delta heights
//! (14 -> 13 -> 12), so `primeCounting' n` and `countRange isPrime n` are
//! definitionally equal by delta alone — no rewriting, no transport. That is
//! the whole content of the first theorem below: `countRange_le_of_le`
//! (`totient_lemmas.rs`) already IS monotonicity of `primeCounting'`, and the
//! kernel's defeq check unfolds the two aliases while checking the stated
//! type. It is stated here anyway because a name the fact ledger can cite is
//! the deliverable; an unstated defeq is not a theorem.
//!
//! ## What is declared
//!
//! | name | statement |
//! | --- | --- |
//! | `Nat.primeCounting'_mono` | `∀ m n, m ≤ n → primeCounting' m ≤ primeCounting' n` |
//! | `Nat.primeCounting_mono` | `∀ m n, m ≤ n → primeCounting m ≤ primeCounting n` |

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.primeCounting' n`.
fn prime_counting_prime(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.prime_counting_prime, &[n])
}

/// `Nat.primeCounting n`.
fn prime_counting(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.prime_counting, &[n])
}

/// The two monotonicity rows of the prime-counting shelf.
///
/// Both are `countRange_le_of_le` at the predicate `Nat.isPrime`, accepted
/// through the delta chain documented in this module's header. The second
/// additionally uses `succ_le_succ` to move `m ≤ n` to `succ m ≤ succ n`,
/// because `primeCounting n` is `primeCounting' (succ n)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_counting_order(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // primeCounting'_mono : ∀ m n, Le m n → Le (primeCounting' m) (primeCounting' n)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let h_ty = d.le(m, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let pred = d.const_app(p.is_prime, &[]);
        let proof = d.lemma(p.count_range_le_of_le, &[pred, m, n, h]);

        let left = prime_counting_prime(d, &p, m);
        let right = prime_counting_prime(d, &p, n);
        let concl = d.le(left, right);
        let ty = {
            let inner = d.arrow(h_ty, concl);
            let mid = d.pi_fv(n_fv, nat, inner);
            d.pi_fv(m_fv, nat, mid)
        };
        let value = {
            let inner = d.lam_fv(h_fv, h_ty, proof);
            let mid = d.lam_fv(n_fv, nat, inner);
            d.lam_fv(m_fv, nat, mid)
        };
        d.declare_theorem(p.prime_counting_prime_mono, ty, value)?;
    }

    // primeCounting_mono : ∀ m n, Le m n → Le (primeCounting m) (primeCounting n)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let h_ty = d.le(m, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let sm = d.succ(m);
        let sn = d.succ(n);
        let hs = d.lemma(p.succ_le_succ, &[m, n, h]);
        let pred = d.const_app(p.is_prime, &[]);
        let proof = d.lemma(p.count_range_le_of_le, &[pred, sm, sn, hs]);

        let left = prime_counting(d, &p, m);
        let right = prime_counting(d, &p, n);
        let concl = d.le(left, right);
        let ty = {
            let inner = d.arrow(h_ty, concl);
            let mid = d.pi_fv(n_fv, nat, inner);
            d.pi_fv(m_fv, nat, mid)
        };
        let value = {
            let inner = d.lam_fv(h_fv, h_ty, proof);
            let mid = d.lam_fv(n_fv, nat, inner);
            d.lam_fv(m_fv, nat, mid)
        };
        d.declare_theorem(p.prime_counting_mono, ty, value)?;
    }

    Ok(())
}
