# Notes: 213-nat-primes-2

Detail moved out of [`../status/213-nat-primes-2.md`](../status/213-nat-primes-2.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Not attempted (the other four originally on the backlog)**:
`F:ml430-nat-coprime-iff-isrelprime-0c08eb25` (needs `IsRelPrime`, a concept
this prelude has no analogue for — `Coprime` is spelled `gcd = 1` inline, and
`IsRelPrime` is a units-based characterization we'd have to invent),
`F:ml430-nat-coprime-of-dvd-6f652673` and
`F:ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b` (both need "every prime
divides some existing prime factor" style existence, effectively a min-prime-
factor argument, not a short composition of what's already declared),
`F:ml430-nat-coprime-of-lt-minfac-0f79bdba` (needs `Nat.minFac`, undeclared).
None carried a HELD-OUT or MUTATION marker; all four are just harder than a
one-sitting composition of existing lemmas.

**Build-order trap**: not hit. None of the five new declarations consume
`Nat.Even`/`Nat.Odd`/`declare_parity_all`, so all landed in the pre-parity
region of the pipeline (`declare_coprime_primes` and
`declare_not_prime_of_dvd_of_ne` right after `declare_coprime_or_dvd_of_prime`;
`declare_prime_pred_pos`/`declare_succ_pred_prime` right after
`declare_succ_pred_of_pos`; `declare_prime_dvd_mul_of_dvd_ne` right after
`declare_crt`, since it needs `coprime_mul_dvd`).

**What the kernel rejected**: nothing, on the first attempt for all five —
every proof term type-checked as designed. The one real hazard encountered
was Rust's borrow checker on nested `d.arrow(...)`/`d.lam_fv(...)` calls
(flattened into sequential `let`s per the standing rule, several instances
across the three multi-hypothesis theorems), not a kernel rejection.

**Inventory check caught a real omission**: the first test run after landing
all five (`nat_prelude:: 103 passed, 1 failed`) failed
`every_nat_declaration_is_checked_and_axiom_free` — the five new names were
live in the prelude but absent from `theorem_names()`. Added them there;
`the_build_is_deterministic`'s pin moved `383 -> 388`, read off the test's own
new panic message after the fix, not hand-incremented.

`nat_prelude` theorem/definition count: `74 + 383 = 457` before this lane,
`74 + 388 = 462` after (five new `Theorem`-kind declarations, zero new
`Definition`s).
