# Lane: pow-add-prime-finish — closing the Fermat-prime lemma

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, pow-add-prime-finish, 2026-08-30).**

`F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (`Nat.Prime (a^n+1) -> exists m,
n = 2^m`, the classical fact behind Fermat primes) is now `proved`, axiom-free,
`proof_route: kernel-lean`.

**The prior handoff's sizing of the remaining work did NOT hold up, and it is
worth recording why.** It called the odd-factor extraction ("`n` not a power
of two has an odd factor `> 1`") "a genuine well-founded-recursion
undertaking" needing `WellFounded.fix`, on the grounds that every existing
strong-induction construction in this prelude (`gcd`, `bezout_witnesses`,
`modeq`, `wilson`, `exists_prime_factorization`) uses it. That generalization
was wrong: **ordinary structural `Nat.rec` on a FUEL BOUND** (`Le n fuel`,
instantiated at `fuel := n` via `le_refl`) gives the induction hypothesis for
*every* `n' <= fuel-1`, which is exactly the strong-induction shape this
argument needs (recurse on `half := div n 2`, not on `n`'s predecessor). No
`WellFounded`, no `Acc`, no `lt_well_founded` anywhere in the final
construction. `bit_order.rs`'s `msb_exists_of_le_fuel` already uses this exact
pattern for an unrelated predicate (most-significant-bit existence) and was
the template that made the three-lemma bound (`lt_two_mul_of_pos` +
`lt_of_lt_of_le` + `le_of_succ_le_succ`) cheap to find.

**What landed** (`crates/axeyum-lean-kernel/src/nat_prelude/pow_add_prime.rs`,
extended — same file the prior lane started, ~600 new lines):

Detail moved to [`../notes/378-pow-add-prime-finish.md`](../notes/378-pow-add-prime-finish.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | pow-add-prime-finish | `Nat.pow_two_or_has_odd_factor` (odd-factor extraction, ordinary fuel-bounded `Nat.rec`, NOT `WellFounded.fix` — the prior handoff's sizing was wrong) and `Nat.pow_of_pow_add_prime` — closes `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (open → proved, axiom-free); 222/222 `nat_prelude::` |
