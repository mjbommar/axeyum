# Lane: nat-primes-2 — the `Nat.Prime` backlog, second pass

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, nat-primes-2, 2026-08-28).** Closed
five of the ten open `natural-primes` facts, all axiom-free and kernel-checked
in one build (`nat_prelude:: 104/104` after the theorem_names fix, clippy and
rustfmt clean):

- `F:ml430-nat-coprime-primes-5769049f` (`Nat.coprime_primes`) — the target
  the brief called out as unlocking the most. `mp` transports `dvd_refl p`
  along a hypothesised `p = q` to `dvd p q`, then `prime_dvd_iff_not_coprime`'s
  `mp` contradicts the coprimality hypothesis; `mpr` splits
  `coprime_or_dvd_of_prime`, and the `dvd p q` branch applies `q`'s own
  divisor clause to `p`, refuting `p = 1` against `2 ≤ p` and `p = q` against
  the `≠` hypothesis directly.
- `F:ml430-nat-not-prime-of-dvd-of-ne-4ff592c0` — `n`'s own divisor clause
  applied to `m` gives `m = 1 ∨ m = n`; either disjunct contradicts one of the
  two `Not` hypotheses.
- `F:ml430-nat-prime-pred-pos-4e67ac4c` / `F:ml430-nat-succ-pred-prime-4feb123f`
  — both via `pos_implies_succ_pred` (`finite.rs`, cross-file `pub(super)`,
  already used by `binary.rs`/`group.rs`/`fibonacci.rs`) applied to a prime's
  own positivity witness (a locally rebuilt `prime_pos`, mirroring
  `fermat.rs`'s private helper of the same shape byte-for-byte so the built
  `ExprId`s intern identically).
- `F:ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439` — the OTHER named blocker,
  unblocked by `coprime_primes` as the brief predicted. Composes
  `coprime_primes`'s `mpr` with the already-declared `Nat.coprime_mul_dvd`
  (`crt.rs`); declared after `declare_crt` in the build pipeline for that
  reason.

**Not attempted**: `F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786`.
The named blocker (bounded case split over `p ∈ {2, 3, 4}` plus small-numeral
facts) needs a step this pass didn't build — repeated `two_le_succ_or_eq_one`
/`pred`-peeling down from `2 ≤ p` to pin `p` at 2, 3, or 4, then a "4 is not
prime" refutation. Left open rather than rushed; the five landed already
exceed "landing three is a complete success".

Detail moved to [`../notes/213-nat-primes-2.md`](../notes/213-nat-primes-2.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-primes-2 | `Nat.coprime_primes`, `Nat.not_prime_of_dvd_of_ne`, `Nat.Prime.pred_pos`, `Nat.succ_pred_prime`, `Nat.Prime.dvd_mul_of_dvd_ne` — five axiom-free kernel theorems in `nat_prelude/primes.rs`, five `natural-primes` facts flipped to `proved` |
