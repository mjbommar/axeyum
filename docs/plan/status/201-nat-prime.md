# Lane: nat-prime — close the `Nat.Prime` import backlog (7 open facts)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, nat-prime, 2026-08-28).** Landed three of the
seven open `Nat.Prime` facts: `Nat.prime_odd_of_ne_two`, `Nat.prime_even_iff`,
`Nat.prime_not_dvd_mul`, all in `nat_prelude/primes.rs`. Remaining open:
`prime_dvd_mul_of_dvd_ne` (needs a `coprime_primes` argument, not yet built),
`prime_dvd_of_dvd_pow` (needs an induction on the exponent), and
`prime_five_le_of_ne_two_of_ne_three` (needs a bounded case split ruling out
2, 3, 4). `nat_prelude::` sweep: 97 -> 98 passed, 0 failed.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-prime | `Nat.prime_odd_of_ne_two`, `Nat.prime_even_iff`, `Nat.prime_not_dvd_mul` admitted into the Nat prelude; closes 3 of 7 open `Nat.Prime` import facts |
