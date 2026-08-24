# 252 — Partition-safe producer evaluation frontier

The phrase “run a producer on the ready queue” was unsafe: the live frontier
contains 141 dependency-ready facts, including 34 held-out facts and nine facts
outside the nursery evaluation population. This derived frontier is the
deterministic replacement. It selects only dependency-ready facts whose frozen
nursery partition is `train` or `development`, and groups them by partition,
reviewed family, statement shape, and dependency component.

The current input contains 98 facts: 38 train and 60 development, across 86
groups. It names no held-out fact. The remaining 34 held-out and nine
out-of-population ready facts are only aggregate exclusions; they are neither
dispatched nor made visible to producer code through this artifact.

This is an input-selection contract, not a proof or operation contract. It does
not grant a producer authority, prescribe a proof plan, expose target outcomes,
or change a ledger record. A producer evaluation must still pre-register its
budgets and decline taxonomy, issue an outcome for every selected row, decline
negative controls, and independently check/reproduce any proposed proof.

```sh
python3 -m unittest scripts.tests.test_validate_autogenesis_producer_evaluation_frontier
python3 scripts/validate-autogenesis-producer-evaluation-frontier.py
python3 scripts/gen-autogenesis-producer-evaluation-frontier.py --check
just autogenesis-producer-evaluation-frontier
```
