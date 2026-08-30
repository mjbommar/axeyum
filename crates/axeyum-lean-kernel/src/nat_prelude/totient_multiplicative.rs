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
