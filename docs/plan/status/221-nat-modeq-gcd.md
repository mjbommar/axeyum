# Lane: nat-modeq-gcd — close the remaining natural-modular-equivalence / natural-gcd facts

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, nat-modeq-gcd, 2026-08-28).** Six open facts across
two small families (all `development`, none HELD-OUT/MUTATION, verified against
a fresh `scripts/fact-frontier.py` run before touching anything):
`F:ml430-nat-coprime-iff-isrelprime-0c08eb25`,
`F:ml430-nat-coprime-of-dvd-6f652673`,
`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`,
`F:ml430-nat-div-dvd-div-left-b56f6f7c`,
`F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e`,
`F:ml430-nat-modeq-gcd-eq-5167ff4f`.

Landed `Nat.ModEq.gcd_eq` (`F:ml430-nat-modeq-gcd-eq-5167ff4f`) in
`nat_prelude/gcd.rs` as `declare_modeq_gcd_eq`, dispatched after
`declare_dvd_antisymm` (needs `dvd_antisymm`, `gcd_dvd_left/right`, `dvd_gcd`,
`dvd_add`, `dvd_add_iff_right`, `dvd_mul_right_of_dvd`, `add_comm`). Route:
eliminate the balanced-witness `modEq m a b := ∃ u v, a+m*u=b+m*v` twice, show
`gcd a m ∣ gcd b m` and the mirror image, close with `dvd_antisymm`. Kernel
accepted first attempt; `every_nat_declaration_is_checked_and_axiom_free`
caught the missing `theorem_names` entry (recounted, not incremented: 400).
`nat_prelude::` sweep: 110 passed, 0 failed (was 109 before).

Two of the six are judged genuinely out of scope for this lane, both because
they need a NEW predicate/definition the whole kernel lacks, confirmed absent
by grep across `nat_prelude.rs` and every `nat_prelude/*.rs`:
- `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` needs `IsRelPrime` (per the
  brief; agreed after independent check).
- `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` needs `Nat.minFac` (least prime
  factor) — **not previously flagged, newly confirmed absent this session**.
  `exists_prime_dvd`/`least_divisor_search` give existence of *a* prime
  factor, not a computable minFac with defining equations; building one is a
  separate, larger task.

Detail moved to [`../notes/221-nat-modeq-gcd.md`](../notes/221-nat-modeq-gcd.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-modeq-gcd | land `Nat.ModEq.gcd_eq` (gcd.rs); confirm minFac absent, isRelPrime absent |
| 2026-08-28 | nat-modeq-gcd | land `Nat.div_dvd_div_left` (divisibility.rs) |
| 2026-08-28 | nat-modeq-gcd | land `Nat.coprime_of_dvd'` (primes.rs), fixing a build-order UnknownConst |
