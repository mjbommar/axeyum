# Target coprime-cancellation root audit plan

Date: 2026-08-21

## Decision

Test the narrow official-target cancellation route in parallel with the
bottom-up public Euclidean repair. The desired cancellation theorem follows
from three target-side interfaces if—and only if—their proof closures are
axiom-free:

1. interpret `gcd a c = 1` as `a.Coprime c`;
2. inherit `d.Coprime c` from `d ∣ a`; and
3. cancel `c` from `d ∣ c * b`.

The exact proof-free roots are `Nat.Coprime.eq_1`,
`Nat.Coprime.coprime_dvd_left`, and
`Nat.Coprime.dvd_of_dvd_mul_left`.

## Fixed audit

One pinned Lean 4.30 export may select the three roots from module `Init`, and
one Axeyum importer pass may report only their identities, direct dependencies,
and kernel-derived footprints. Raw proof streams, expressions, theorem values,
and source bodies are not model-readable.

All three footprints must be empty before a separately preregistered target
support proof may run. This plan authorizes no proof compilation, theorem
submission, Fibonacci target attempt, evaluation credit, fact mutation, or
ledger write.

## Horizon

A passing narrow route can unblock the dependency-ready Fibonacci child while
the broader Euclidean wrapper remains a bottom-up library task. A decline is
also useful: it proves the target shortcut shares the same trusted-base cost and
keeps effort on the foundational route.

## Verification

```sh
python3 scripts/check-autogenesis-coprime-target-cancellation-root-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_coprime_target_cancellation_root_audit_plan
```
