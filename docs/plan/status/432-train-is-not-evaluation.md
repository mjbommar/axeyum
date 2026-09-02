# Lane: train-is-not-evaluation — make the split policy say train is the training partition, not an evaluation partition

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, train-is-not-evaluation, 2026-09-02).** Opened the
lane. The one red partition gate after 431 is
`check-autogenesis-nursery.py`'s cross-population arm: 5 crossing components,
edges train→development 83, development→train 64, held-out→development 4,
held-out→train 2. This lane amends the split policy so `train` is a training
partition rather than an evaluation partition, derives both gates'
`EVALUATION_PARTITIONS` from the policy file, and re-records the edge baseline.
Nothing landed yet.

<!-- plan-section: landed-changes -->

| 2026-09-02 | train-is-not-evaluation | lane opened; status stub |
