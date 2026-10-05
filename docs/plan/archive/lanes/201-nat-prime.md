# Lane: nat-prime — close the `Nat.Prime` import backlog (7 open facts)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, nat-prime, 2026-08-28).** Landed four of the
seven open `Nat.Prime` facts: `Nat.prime_odd_of_ne_two`, `Nat.prime_even_iff`,
`Nat.prime_not_dvd_mul`, `Nat.prime_dvd_of_dvd_pow`, all in
`nat_prelude/primes.rs`. Remaining open: `prime_dvd_mul_of_dvd_ne` (needs a
`coprime_primes` argument -- two distinct primes are coprime -- not yet
built anywhere in the tree; its own fact, `F:ml430-nat-coprime-primes-
5769049f`, is itself open) and `prime_five_le_of_ne_two_of_ne_three` (needs
a bounded case split ruling out `p ∈ {2,3,4}`, which in turn needs small
numeral facts this prelude does not yet carry -- `2 ≠ 4`, `dvd 2 4`, and a
"primality of 4 is false" argument -- none reused from elsewhere). Final
`nat_prelude::` sweep: 98 passed, 0 failed (up from 97 at lane start).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-prime | `Nat.prime_odd_of_ne_two`, `Nat.prime_even_iff`, `Nat.prime_not_dvd_mul`, `Nat.prime_dvd_of_dvd_pow` admitted into the Nat prelude; closes 4 of 7 open `Nat.Prime` import facts |
