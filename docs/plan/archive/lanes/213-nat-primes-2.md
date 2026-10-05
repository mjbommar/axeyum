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

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-primes-2 | `Nat.coprime_primes`, `Nat.not_prime_of_dvd_of_ne`, `Nat.Prime.pred_pos`, `Nat.succ_pred_prime`, `Nat.Prime.dvd_mul_of_dvd_ne` — five axiom-free kernel theorems in `nat_prelude/primes.rs`, five `natural-primes` facts flipped to `proved` |
