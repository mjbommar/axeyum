# Lane: prime-dvd-mirrors — the `ml430` prime-divisibility mirror cluster

<!-- plan-section: lane-status -->

**DONE (`prime-dvd-mirrors`, 2026-08-30).** 14 of 19 dispatchable `ml430`
prime-divisibility facts closed. New file `nat_prelude/prime_dvd_mirrors.rs`
declares 13 theorems, **all admitted by the kernel on the first attempt**, all
axiom-free, no new `Definition`:

```text
Nat.prime_one_lt                    Prime p -> 1 < p
Nat.prime_one_le                    Prime p -> 1 <= p
Nat.prime_pos                       Prime p -> 0 < p
Nat.prime_ne_one                    Prime p -> p != 1
Nat.prime_ne_zero                   Prime p -> p != 0
Nat.prime_not_dvd_one               Prime p -> ~(p | 1)
Nat.prime_eq_one_or_self_of_dvd     Prime p -> m | p -> m = 1 \/ m = p
Nat.prime_dvd_iff_eq                Prime p -> a != 1 -> (a | p <-> p = a)
Nat.prime_dvd_mul_iff               Prime p -> (p | m*n <-> p|m \/ p|n)
Nat.prime_coprime_iff_not_dvd       Prime p -> (gcd p n = 1 <-> ~(p|n))
Nat.prime_eq_two_or_odd             Prime p -> p = 2 \/ Odd p
Nat.prime_eq_two_or_mod_two_eq_one  Prime p -> p = 2 \/ p%2 = 1
Nat.prime_mod_two_eq_one_iff_ne_two Prime p -> (p%2=1 <-> p != 2)
Nat.prime_coprime_pow_of_not_dvd    Prime p -> ~(p|a) -> gcd a (p^m) = 1
```

A 14th fact, `F:ml430-nat-prime-dvd-or-dvd-4ae88221`, was flipped WITHOUT a
new declaration: its statement is `Nat.euclid_lemma` (`bezout.rs`) verbatim up
to bound-variable names, so its checker cites `euclid_lemma` directly — no
`Nat.prime_dvd_or_dvd` declaration exists and none should be added.

`primes.rs`: `prime_condition` and `prime_parts` made `pub(super)` so the new
file reuses the primality spelling (`2 <= p /\ forall c, c|p -> c=1 \/ c=p`)
rather than re-deriving it.

Checks run: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **203
passed, 0 failed** (202 baseline + 1 new statement-shape test). `cargo fmt
--all --check` clean on touched files (formatted individually with `rustfmt
--edition 2024`, not workspace `cargo fmt`). `cargo clippy -p
axeyum-lean-kernel --all-targets -- -D warnings` clean. `python3
scripts/validate-facts.py`: **2265 facts, 0 errors**.

Detail moved to [`../notes/356-prime-dvd-mirrors.md`](../notes/356-prime-dvd-mirrors.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | prime-dvd-mirrors | `bf25ad981` `1fdea582b` `42ccc8e37` -- 13 new theorems (`nat_prelude/prime_dvd_mirrors.rs`) + 1 direct flip to `euclid_lemma`, closing 14/19 dispatchable `ml430` prime-divisibility facts |
