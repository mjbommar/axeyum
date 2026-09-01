# Lane: red-gate-sweep

**Status:** in progress — diagnosis landed, fixes in flight.

## Mandate

Four gates were red on `main` at `b558d9b5a`. Make them green **without weakening
what they check**. A gate greened by relaxing an assertion is worse than a red
gate: it trains everyone to skip the check.

## Re-measured at `b558d9b5a` (this lane, not relayed)

| gate | exit | finding |
| --- | --- | --- |
| `scripts/check-autogenesis-nursery.py` | 1 | 2 partition-leak violation types |
| `scripts/check-generated-artifact-ownership.py` | 1 | 2 multi-writer artifacts (`mirror-divergence-registry.json`, `schema.json`) |
| `scripts/tests/test_check_autogenesis_holdout_isolation.py` | 1 | pin `held_out=146` against live `186` |
| `scripts/tests/test_check_autogenesis_nursery.py` | 1 | same partition leak as row 1 |

`check-dispatchable-frontier.py` (G7, queue below floor) is a concurrent lane's
and is deliberately untouched here.

## Diagnosis in progress

- **Partition leak.** Two dependency components span partitions. Neither
  involves `held-out`, so this is NOT a blind-evaluation contamination: it is
  train<->development plus a component shared with Autogenesis-1's
  `longitudinal` facts (`F:nat-mul-one`, `F:nat-zero-add`). Three honest
  remedies exist (wrong edge / wrong partition assignment / over-strict check)
  and the choice needs evidence, not preference.
- **Stale pin `held_out=146` vs `186`.** Bumping the number is the trap. The pin
  exists to notice change; transcribing the new value converts a detector into a
  rubber stamp. Establish whether 186 is CORRECT first.
- **Multi-writer artifacts.** Two basenames named by several `gen-*.py`
  producers. Needs a check of whether the producers actually collide on one
  path, or whether the checker is matching on basename where paths differ.

This commit records the measurement only. No fix is claimed yet.
