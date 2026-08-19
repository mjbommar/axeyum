# Mathlib nursery dispatch baseline

Date: 2026-08-18

## Result

The first post-freeze census inspected all 138 train and development contracts
and deliberately inspected none of the 76 held-out contracts. Zero facts were
eligible for authoritative dispatch. The initial census had all 138 decline on
surface syntax. The adapter and checked-candidate increments then separated one
row from the unsupported population.

The exact source-bound operation is now registered. The current census is:

```text
already-established                                          1
no-exact-authoritative-operation                           137
eligible-for-dispatch                                        0
```

The census itself still runs no producer, consumes no executor budget, accesses
no proof body or target outcome, and grants no fact credit. The content-
addressed result is
[`mathlib-nursery-dispatch-baseline-v1.json`](../../artifacts/autogenesis/mathlib-nursery-dispatch-baseline-v1.json).

## What this corrects

“Axeyum failed to prove 138 theorems” would be false. One proposition now has an
independently checked kernel goal and one exact registered operation. The
remaining 137 have no exact operation; calling them unsupported by the entire
`lean4-surface` language would now be too broad.

This changes the immediate sequence. Building induction search, library
retrieval, or tactic planning first would produce machinery with no legitimate
input path from the nursery. The narrow bridge must come first:

1. elaborate a frozen `lean4-surface` proposition in the pinned Mathlib
   environment;
2. export only its declaration type, never its theorem value or proof body;
3. import and normalize that type into the independent kernel's goal form;
4. bind source bytes, toolchain identity, exported bytes, and reconstructed
   type in a replayable statement-adapter receipt;
5. register one bounded operation only after negative controls show that a
   changed proposition, proof-bearing export, or unsupported construct is
   rejected.

All five steps, authoritative execution, durable admission, and clean replay
are complete for one train row. The subsequent
[reflexivity census](22-mathlib-reflexivity-coverage.md) measures the reusable
grammar without redispatching that established row.

Fixed-budget proof episodes can now distinguish adapter, producer, kernel, and
assurance boundaries instead of calling every non-dispatch a proof failure.

## Why this is still flywheel progress

The census turns a vague “no operation” into a population-wide architectural
blocker. It also identifies a reusable capability: the statement adapter unlocks
all eight train/development families and, if it generalizes without special
cases, the untouched held-out families later. That is higher leverage than
choosing a familiar theorem and hand-building its proof route.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_create_autogenesis_nursery_dispatch_baseline
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
```
