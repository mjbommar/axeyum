fn _boundary_before() {}
//! The irrationality of `√2` — Euclid Book X, the oldest surviving theorem of
//! pure mathematics — stated the way this kernel can actually check it: purely
//! over `Nat`, with no real `sqrt` and no rational embedding.
//!
//! `CReal.sqrt` does not exist in this kernel, and adding "therefore √2 is
//! irrational" would need it plus a rational embedding. The content of the
//! classical theorem is entirely captured by
//!
//! ```text
//! Nat.no_rational_sqrt_two : ∀ p q, q ≠ 0 → p·p ≠ 2·(q·q)
//! ```
//!
//! (`p/q = √2 ⟺ p² = 2q²`, so no such `p,q` is exactly "`√2` is irrational"
//! restated without ever introducing `Real` or `Rat`.) The `q ≠ 0` hypothesis
//! is load-bearing: `p = q = 0` satisfies `p·p = 2·(q·q)` without it.
//!
//! ## Route: `euclid_lemma`-flavoured evenness, then infinite descent
//!
//! [`Nat.even_of_even_sq`] (`2 ∣ p·p → 2 ∣ p`) is proved via `gcd p 2 ∈ {1,2}`
//! (the two divisors of the literal `2`, `dvd_two_pow_classify` at `k=1`'s
//! shape spelled out directly rather than reproduced, since the existing
//! spelling — `perfect.rs`'s `divisors_of_two` — is `fn`-private to its own
//! file) plus `gauss_lemma`: if `gcd(2,p)=1`, `gauss_lemma` cancels the coprime
//! factor `p` from `2 ∣ p·p` directly, giving `2 ∣ p`; if `gcd(2,p)=2`, `2 ∣ p`
//! is `gcd_dvd_right` after substituting. This never needs to assemble the
//! `Prime` predicate `euclid_lemma` itself requires (`2 ≤ x ∧ ∀ d, d∣x→d=1∨d=x`)
//! for the literal `2` — a small variant of the same `euclid_lemma`/`primes.rs`
//! family, one layer down.
//!
//! `Nat.no_rational_sqrt_two` then follows by **infinite descent**
//! (`WellFounded.fix` over `lt_well_founded`, the same combinator `Nat.gcd`
//! and `Nat.exists_prime_factorization` use), recursing on `q`: given
//! `p·p = 2·(q·q)`, evenness gives `p = 2·r`; substituting and cancelling a
//! factor of `2` gives `q·q = 2·(r·r)` — the same shape, one step down. `r < q`
//! is derived from that very equation (`q·q = 2·(r·r) > r·r` whenever `r ≠ 0`,
//! so `q > r`, via the monotonicity contrapositive `lt_or_ge` +
//! `mul_le_mul_left`); `r = 0` is a direct contradiction against `q ≠ 0`
//! (`q·q = 2·(0·0) = 0`). No case ever needs a *second* recursive step beyond
//! the one `WellFounded.fix`'s own hypothesis already supplies.
fn _boundary_after() {}
