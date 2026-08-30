# Lane: totient-prime-power — `Nat.totient_prime_pow`, and the three mirrors reassessed

<!-- plan-section: lane-status -->

**DONE (`totient-prime-power`, 2026-08-30).** Six theorems landed in a new
file `nat_prelude/totient_prime_pow.rs`, **all six admitted by the kernel on
the first attempt**, all axiom-free, no new `Definition`. `nat_prelude::`
**201 passed, 0 failed** (196 baseline + 4 new tests + the coverage assertion,
which fired correctly before the names were registered). `cargo fmt --all
--check` clean; `clippy -p axeyum-lean-kernel --all-targets -- -D warnings`
clean; `validate-facts.py` **2225 facts, 0 errors**;
`scripts/gen-adr-index.py` exit 0.

```text
Nat.countRange_const_true          ∀ n, countRange (fun _ => true) n = n
Nat.coprime_mul_iff_of_dvd         e ∣ m → (gcd k (m*e) = 1 ↔ gcd k m = 1)
Nat.totient_mul_of_dvd             e ∣ m → φ(m*e) = φ(m)*e
Nat.totient_pow_succ_of_prime      Prime q → φ(q^(j+1)) = (q-1)*q^j
Nat.totient_prime_pow              Prime q → φ(q^(j+1)) = q^(j+1) - q^j
Nat.totient_dvd_totient_mul_prime  Prime q → φ(x) ∣ φ(x*q)
```

Three hand-curated ledger facts: `F:nat-totient-mul-of-dvd`,
`F:nat-totient-prime-pow`, `F:nat-totient-dvd-totient-mul-prime`.

## The assessment the task asked for first

**All three remaining `ml430` mirrors are reachable WITHOUT multiset
uniqueness.** The Euler-product route needs it; a prime-peeling induction does
not, and that is the finding — recorded as
[ADR-0668](../../research/09-decisions/adr-0668-the-totient-mirrors-do-not-need-multiset-uniqueness.md)
with the full argument and the simulated inductions.

This **corrects** `349`'s sizing. That lane wrote that both mirrors "need the
non-coprime formula, which needs a totient value at prime powers plus a
product over a factorization" — right about the *Euler-product route*, and it
reads as a statement about the *targets*. It is the standing failure mode this
repository has now hit three times: a handoff reports accurately on its own
route, and the route-local blocker gets promoted into a claim about the goal.

Why uniqueness drops out, in one sentence: each target is **preserved along a
chain of prime steps**, the chain is built from *some* factorisation of the
cofactor, and nothing ever compares two factorisations — so nothing needs them
to agree. Uniqueness is required only to *evaluate* a closed-form product,
which none of these arguments does.

The only number-theoretic inputs are `Nat.exists_prime_dvd` (every `n > 1` has
a prime divisor — far weaker than unique factorisation), `Nat.euclid_lemma`,
`Nat.gcd_mul_right`, and the prime step. **All four now exist.**

## Numeric checks, as re-executable commands

Detail moved to [`../notes/355-totient-prime-power.md`](../notes/355-totient-prime-power.md).

