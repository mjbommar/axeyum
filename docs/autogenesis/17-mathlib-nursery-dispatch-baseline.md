# Mathlib nursery dispatch baseline

Date: 2026-08-18

## Result

The first post-freeze census inspected all 138 train and development contracts
and deliberately inspected none of the 76 held-out contracts. Zero facts are
eligible for authoritative dispatch. The initial census had all 138 decline on
surface syntax. After the first statement-adapter increment, the same frozen
population separates into:

```text
unsupported-formal-language:lean4-surface                 137
statement-adapter-ready:no-authoritative-producer           1
```

No producer ran, no executor budget was consumed, no proof body or target
outcome was accessed, and no fact received credit. The content-addressed result
is
[`mathlib-nursery-dispatch-baseline-v1.json`](../../artifacts/autogenesis/mathlib-nursery-dispatch-baseline-v1.json).

## What this corrects

“Axeyum failed to prove 138 theorems” would be false. The theorem statements
have only crossed the proof-free Mathlib syntax/type boundary. Current
authoritative operations accept exact preregistered facts in `lean4` kernel
form or `smtlib2`. One proposition now has an independently checked kernel goal,
but it deliberately remains non-dispatchable until a producer and checker are
registered. The remaining 137 have no typed goal to give a producer.

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

Only then can fixed-budget proof episodes distinguish missing lemmas, search
limits, reconstruction gaps, and checker failures.

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
