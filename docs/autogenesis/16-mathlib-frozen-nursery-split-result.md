# Mathlib frozen nursery split result

Date: 2026-08-18

## Result

The reviewed, proof-free Mathlib population is now a preregistered evaluation
nursery. The manifest contains 214 evaluation propositions in three fixed
partitions:

| Partition | Facts | Families |
|---|---:|---|
| train | 78 | integer Fibonacci, integer GCD, integer modular equivalence, natural factorial, natural Fibonacci |
| development | 60 | natural bitwise, natural modular equivalence, natural primes |
| held-out | 76 | natural binomial, natural GCD, natural logarithm, natural square root |

The Autogenesis-1 B-to-A pair remains a separate two-fact longitudinal
regression. It is not evaluation yield.

The executable checker reports 214 evaluation entries, 141 declared dependency
components, 48 held-out components, maximum declared dependency depth four,
twelve mutations, seven route-hypothesis labels, zero blockers, and no detected
component, source-group, family, proof-shape, or longitudinal overlap.

## Why the split key is family-scoped

A feasibility census rejected global broad statement shapes. Joining declared
dependency components, theorem families, and labels such as
`unconditional-equality` or `conditional-proposition` connects all 214 facts
into one component. No three-way split can survive that rule.

That collapse is a category error, not evidence that evaluation is impossible:
an equality about Fibonacci recurrence and an equality about bit operations do
not share a proof template merely because both use `=`. The frozen manifest
therefore uses `<family>:<statement-shape>` as the proof-template risk key.
Whole families still stay in one partition, and the independent source review
group is also checked explicitly. This is stricter than relying on fact-ledger
dependencies alone.

## Authority and limitations

[`mathlib-nursery-split-policy-v1.json`](../../artifacts/autogenesis/mathlib-nursery-split-policy-v1.json)
fixes family membership using statement-only metadata and graph structure,
before any Axeyum target episode. The generator binds that policy and the fact
catalog into [`nursery-v1.json`](../../artifacts/autogenesis/nursery-v1.json).

Route hypotheses are guesses derived from theorem families. They do not
register an operation, reveal a Mathlib proof, dispatch a solver, establish a
fact, or authorize admission. The 202 source propositions remain externally
proved but open in Axeyum; the twelve mutations remain externally unknown.
Readiness means the experiment is leakage-controlled and large enough to run,
not that Axeyum can solve it.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_nursery_split
python3 -m unittest scripts.tests.test_check_autogenesis_nursery
python3 scripts/create-autogenesis-mathlib-nursery-split.py --check
python3 scripts/check-autogenesis-nursery.py --require-ready
```

## What comes next

The next action is not to import Mathlib answers or hand-author proof plans.
Run fixed-budget, outcome-recording episodes over train and development while
keeping held-out untouched. Aggregate typed declines by family, statement
shape, missing kernel primitive, and missing reconstruction seam. The first
capability acquisition should be chosen from that measured bottleneck, then
evaluated against the still-frozen held-out partition.
