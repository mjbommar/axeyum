# Lane: nat-singles — close the two unassessed `ml430` singleton facts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-singles, 2026-08-29).** Landed both
unassessed facts: `Nat.mod_lcm` and `Nat.dvd_of_forall_prime_mul_dvd`.
Neither needed the stated blockers to be investigated first -- nobody had
looked, and both turned out to have short proofs from infrastructure already
in the prelude (`Nat.lcm_dvd`, `crt.rs`'s `gap_dvd`/`modeq_of_dvd_gap`,
`Nat.exists_prime_dvd`).

`Nat.mod_lcm : modEq n x y -> modEq m x y -> modEq (lcm n m) x y`,
**unconditional** in `n`/`m` (unlike `Nat.crt_unique`, which needs
`gcd n m = 1`). The combination step is `Nat.lcm_dvd : dvd n c -> dvd m c ->
dvd (lcm n m) c`, already unconditional, so the whole proof is `crt_unique`'s
own `crt_le`/`gap_dvd`/`modeq_of_dvd_gap` shape with `lcm_dvd` swapped in for
`coprime_mul_dvd`. `gap_dvd`/`modeq_of_dvd_gap` (`crt.rs`, private) were
widened to `pub(super)` and reused from `lcm.rs` rather than duplicated.

`Nat.dvd_of_forall_prime_mul_dvd : (forall p, Prime p -> p|a -> p*a|b) ->
a|b`. Turned out to need only ONE prime dividing `a` (any one), not
induction over `a`'s factorization: `a=0` uses the hypothesis at `k=2`;
`a=1` needs `dvd_mul`+`one_mul` and never touches the hypothesis; `a>=2`
uses `exists_prime_dvd` for a witness `pw`, the hypothesis at `k=pw` gives
`pw*a | b`, and `a | (a*pw)` (`dvd_mul` + `mul_comm`) chains via `dvd_trans`.
Same nested `lt_or_ge`-on-`a` trichotomy as the neighbouring
`coprime_of_forall_prime_dvd`.

The other two facts (`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`,
`F:ml430-nat-coprime-iff-isrelprime-0c08eb25`) are left `open`, confirmed
still blocked (re-grepped the whole `crates/axeyum-lean-kernel/src/` for
`minFac`/`min_fac` and `IsRelPrime`/`is_rel_prime`/`isRelPrime`: zero hits
outside this status doc and the fact files themselves) -- see "What's still
needed" below for the precise construction each one is missing.

`nat_prelude` count: **85 + 441 -> 85 + 443** (2 new theorems, 0 new
definitions; confirmed by `the_build_is_deterministic`'s own panic message,
not hand-counted).

## What's still needed for the other two facts

Detail moved to [`../notes/240-nat-singles.md`](../notes/240-nat-singles.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-singles | `Nat.mod_lcm`: unconditional lcm-combination of two congruences, closes `F:ml430-nat-mod-lcm-ee6bdd41` |
| 2026-08-29 | nat-singles | `Nat.dvd_of_forall_prime_mul_dvd`: needs only one prime witness, closes `F:ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b` |
| 2026-08-29 | nat-singles | `gap_dvd`/`modeq_of_dvd_gap` (`crt.rs`) widened `fn` -> `pub(super) fn` so `lcm.rs` can reuse them |
