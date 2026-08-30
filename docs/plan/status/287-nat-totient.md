# Lane: nat-totient — the `ml430` `Nat.totient` mirrors

<!-- plan-section: lane-status -->

**Lane block (`DONE for this dispatch`, nat-totient, 2026-08-29).**

**The task.** Nine freshly-preregistered `ml430` `Nat.totient` mirrors were
dispatchable:

```
F:ml430-nat-totient-eq-zero-3be161d6            F:ml430-nat-totient-eq-one-iff-68d883a0
F:ml430-nat-totient-even-28e0415f               F:ml430-nat-totient-dvd-of-dvd-9622e44a
F:ml430-nat-odd-totient-iff-b6a6596f            F:ml430-nat-odd-totient-iff-eq-one-d0491d84
F:ml430-nat-totient-coprime-totient-iff-3932cf83
F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
F:ml430-nat-dvd-two-of-totient-le-one-3642bf31
F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
```

**Step 0.** `Nat.totient` is a `Definition` (`nat_prelude/totient.rs`,
already there before this lane, along with `Nat.countRange` and one prior
theorem `Nat.totient_prime`). A theorem inventory returns zero rows for it
by construction — confirmed the trap doesn't apply here since the family's
own file already reads it from the environment/source, not from an
inventory. Checked which of the nine already existed under a different
name: **none did** — `theorem_dependency_inventory`/`prelude_theorem_inventory
--include-constructed --release` had no match for any of `totient_eq_zero`,
`totient_eq_one_iff`, `totient_even`, `totient_dvd_of_dvd`,
`odd_totient_iff{,_eq_one}`, `totient_coprime_totient_iff`,
`eq_or_eq_of_totient_eq_totient`, `dvd_two_of_totient_le_one`,
`totient_gcd_mul_totient_mul` before this lane, and `coprime_succ_self`
(the one new supporting lemma this lane needed) was also absent (`gcd_comm`,
`gcd_succ_self` too — the only prior `gcd_comm`-shaped fact in the tree is
`int_prelude`'s, over `Int` arguments).

Detail moved to [`../notes/287-nat-totient.md`](../notes/287-nat-totient.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-totient | `Nat.coprime_succ_self` (new: consecutive naturals are coprime) and `Nat.totient_eq_zero` — 1 of 9 dispatched `ml430` totient mirrors, axiom-free, via a top-index-witness argument (`nat_prelude/totient_lemmas.rs`). The other 8 triaged and left open: blocked on a general existence-witness-to-positive-count lemma and/or the `totient_even` fixed-point-free-involution pairing argument and/or the multiplicative formula for `totient` — none built yet, none a small addition. |
