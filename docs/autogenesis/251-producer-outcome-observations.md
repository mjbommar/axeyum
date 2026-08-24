# 251 — Outcome-safe producer observations

The knowledge overlay now has a reproducible view of what the fixed bounded
reflexivity producer actually did on its sealed Mathlib 4.30 train/development
census. It joins each retained outcome to its partition, reviewed fact family,
statement shape, and whether the goal was exact-source or semantically
abstracted. Keeping train and development separate is necessary: one may guide
implementation iteration, while the other remains a non-held-out check on that
iteration.

The current observation covers 138 facts: 24 exact-source and 114
semantic-abstraction rows, split 78 train / 60 development. It retains the
five outcome totals from the original census: two accepted diagnostic proofs,
46 kernel rejections, 49 non-exact-equality producer declines, 40
non-constant-headed-equality declines, and one binder-budget decline. There
are exactly zero held-out rows.

This is deliberately evidence about a **single fixed producer policy**, not a
claim that a family or statement shape is inherently easy or hard. In
particular it records no timing data, cannot rank an unobserved fact, registers
no operation, and cannot alter a fact's status. It makes capability work
falsifiable: a future general producer must be compared against explicit,
partition-safe observations rather than a narrative based on a few successes.

The generator reopens only the hash-pinned train/development observation and
mapping archives. It verifies both file identities, the semantic observation
identity, mapping identity, one row per mapped fact, catalog family agreement,
and exact reproduction of the original census outcome counts. Its structural
validator rejects a held-out count, duplicate fact observation, or invented
outcome count.

```sh
python3 -m unittest scripts.tests.test_validate_autogenesis_producer_outcome_observations
python3 scripts/validate-autogenesis-producer-outcome-observations.py
python3 scripts/gen-autogenesis-producer-outcome-observations.py --check
just autogenesis-producer-outcomes
```
