# Lane: totient-dvd-chain — both ADR-0668 divisibility mirrors closed

<!-- plan-section: lane-status -->

**DONE (`totient-dvd-chain`, 2026-08-30).** Both facts assigned to this lane
closed axiom-free, first attempt after fixing bugs found via
`Kernel::render_lean`-based debugging (never by hand-tracing to the end):

    F:ml430-nat-totient-dvd-of-dvd-9622e44a            a | b -> totient a | totient b
    F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7  a | b -> totient a = totient b
                                                          -> a = b \/ 2*a = b

Four new theorems landed in a new file `nat_prelude/totient_dvd_chain.rs`:

```text
Nat.totient_dvd_totient_mul     forall k a, Dvd (totient a) (totient (mul a k))
Nat.totient_dvd_of_dvd          Dvd a b -> Dvd (totient a) (totient b)
Nat.totient_mul_cofactor_bound  Le 1 (totient a) -> Le 2 k ->
                                 Or (Le (2*totient a) (totient (a*k)))
                                    (And (k=2) (totient (a*k) = totient a))
Nat.eq_or_eq_of_totient_eq_totient  Dvd a b -> totient a = totient b ->
                                     Or (a=b) (2*a=b)
```

`nat_prelude::` **206 passed, 0 failed** (202 baseline + 4 new tests).
`cargo fmt --all --check` clean (checked via `-p axeyum-lean-kernel`);
`clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean;
`validate-facts.py` **2265 facts, 0 errors**;
`scripts/check-fact-depends-derived.py --fix` applied cleanly to the second
fact (12 direct-lemma edges added).

## ADR-0668's claim: did "only the induction remains" hold?

**Yes, for Target 1 outright; yes for Target 3 with one addition ADR-0668
did not spell out precisely enough to skip verifying.**

Target 1 needed exactly what the ADR named: a well-founded induction on the
cofactor `k := b/a`, chaining `Nat.totient_dvd_totient_mul_prime` along a
prime peeled one at a time by `Nat.exists_prime_dvd`. No new number theory.

Detail moved to [`../notes/358-totient-dvd-chain.md`](../notes/358-totient-dvd-chain.md).

