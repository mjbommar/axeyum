# Nursery foundation result

Date: 2026-08-18

## Verdict

**The split and leakage contract exists; the evaluation population does not.**
This is a useful negative baseline, not Phase 3 progress credit.

The current fact ledger contains 110 facts across six established proof routes,
but those aggregate counts overstate its value as a held-out autonomous proving
population:

- only 23 direct kernel proof-derived edges reach ten consequents;
- fourteen named kernel facts are absent from dependency-inventory coverage;
- all nine open or conjectured facts lack a registered proof route; and
- the two cross-route `depends_on` edges are authored metadata, not accepted
  heterogeneous proof compositions.

Randomly splitting those rows would leak the connected Nat library and known
proof shapes. Selecting isolated rows by route would not measure proof
composition. The first post-Autogenesis-1 increment therefore freezes how a
real nursery will be divided before it authors answers.

## Contract

[`nursery-v1.json`](../../artifacts/autogenesis/nursery-v1.json) records each
population member's provenance class, theorem family, proof shape, route
hypotheses, mutation relation, answer-access policy, and partition. The checker
enforces four separate anti-leakage boundaries:

1. a declared dependency component cannot cross train, development, and
   held-out;
2. a theorem family cannot cross those partitions;
3. a proof shape cannot cross those partitions; and
4. a statement mutation remains beside its source fact and family.

These fields guide evaluation only. `depends_on` cannot earn admission credit
until the accepted proof independently derives the edge, and a route hypothesis
grants no dispatch, checking, or write authority.

The exact `F:nat-zero-add -> F:nat-mul-one` chain is reserved as the
`longitudinal` partition and excluded from every yield metric. This prevents the
successful bootstrap from becoming its own held-out test.

## Executable baseline

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_nursery
python3 scripts/check-autogenesis-nursery.py
python3 scripts/check-autogenesis-nursery.py --require-ready  # must fail today
```

The valid foundation report is `ready=false`, with zero evaluation facts and
nine explicit blockers: the 100--300 population floor, three empty evaluation
partitions, no evaluation provenance or route diversity, no statement
mutation, no held-out component, and no evaluation dependency depth.

Ordinary repository checks require the contract to be accurate and
deterministic. `--require-ready` is a distinct precondition for experiments and
fails until the population is actually frozen and complete. A checker whose
only successful state were “ready” would encourage hiding honest partial work;
a checker that always returned success would encourage the opposite lie.

## Sequenced next work

The next unit is authoring, not planner implementation:

1. select whole Nat and Int theorem families before seeing target outcomes;
2. add statements in independent dependency components, with source and license
   provenance sufficient to regenerate them without vendoring Mathlib;
3. add strength-changing mutations beside each source family;
4. freeze train, development, and held-out assignments;
5. run current dispatch under fixed budgets and retain typed failure episodes;
6. let the measured blocker distribution choose the first proof-plan node or
   engine adapter.

This sequencing works top-down by preserving the future learned-policy and
multi-route evaluation boundary, and bottom-up by making the next 100--300
facts pass an executable contract today. It deliberately does not assume that
Phase 3's first missing primitive is theorem application, induction, CAS, or a
solver adapter; the nursery episodes must decide that.
