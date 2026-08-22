# A bounded-model screen of the open population: 7% coverage, and that is the result

Date: 2026-08-22

## What was asked

`must-decline-mutations-v1.json` records nine statements as FALSE. Those nine
were found by hand. Nothing had checked whether any OTHER statement in the
evaluation population is also false — which matters, because a false statement
sitting in the population unmarked is a trap: a producer that "proved" it would
look like a success, and the gate that voids such a census only knows about the
nine.

So: evaluate every `open` train/development statement over small ranges and look
for counterexamples.

## What came back

| Outcome | Statements |
|---|---:|
| `CANNOT_EVALUATE` | **127** |
| `COUNTEREXAMPLE_FOUND` | 9 — exactly the known set, none new |
| `NO_COUNTEREXAMPLE` | **0** |
| held-out, correctly skipped | 57 |

Both controls passed: the evaluator independently rediscovered all nine
known-false statements *by search* rather than by reading their recorded
witnesses, and found no counterexample for three known-true statements.

## The honest reading

**This screen covered 9 of 136 statements — about 7% — and is inconclusive.**

Note the shape of the table: `NO_COUNTEREXAMPLE` is **zero**. The screen did not
evaluate 127 statements and find them sound; it could not evaluate them at all.
The operators defeating it are ordinary — `Odd`, `Even`, `StrictMono`,
`Symmetric`, `minFac`, `lcm`, higher-order predicates, type-class operations.

It would be easy, and wrong, to summarise this as "no new false statements
found". That sentence is true and useless: an empty result from a tool that was
never pointed at 93% of its subject is indistinguishable from a strong negative
result, which is a standing gotcha in `CLAUDE.md` and the failure this project
gets wrong most often. The correct summary is that **the population is still
unscreened.**

What the screen *does* establish is narrower and worth keeping: the nine
known-false statements are rediscoverable by independent search, so the
must-decline set is not an artefact of how it was originally derived.

## What would make it conclusive

Coverage, not range. The bound (`Nat ∈ [0,12]`, `Int ∈ [-12,12]`) is not what
limited this — 127 statements never got as far as being evaluated at any range.
An evaluator that handles `Odd`/`Even`/`minFac`/`lcm` and simple higher-order
predicates would take coverage from 7% toward most of the population, and the
`CANNOT_EVALUATE` count is the metric to drive down.

Until then, the population's soundness rests on the same footing it did
yesterday: nine hand-found mutations, now independently confirmed
([`must-decline-mutations-v1.json`](../../artifacts/autogenesis/must-decline-mutations-v1.json)),
and no systematic check of the rest.

## Provenance

Produced by a Haiku subagent under a brief that required a positive control
(rediscover all nine by search) and a negative control (find nothing in three
true statements). It reported `CANNOT_EVALUATE` 127 times rather than guessing a
semantics, which is the behaviour that makes the 7% figure trustworthy — a screen
that guessed would have reported far higher coverage and been worth nothing.
