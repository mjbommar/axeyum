# Lane: heldout-never-blind — reclassify the held-out rows whose proofs cite drawn facts

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, heldout-never-blind, 2026-09-02).** Opened the lane.
The one remaining red partition gate is `check-autogenesis-nursery.py`, which
reports a single crossing component spanning development/held-out/train. Its
cause is the six edges in `artifacts/autogenesis/partition-edge-baseline-v1.json`
carrying `held_out_endpoint: true`: each runs FROM a held-out fact TO a drawn
train or development fact, so those held-out rows' proof terms depend on facts we
drew and were never blind. Repair in progress is the reclassification precedent
set by draw 17 (ADR-1450) and the `natural-bit-decode` amendment: move the owning
family held-out → development with a dated reason naming the predating commit.

<!-- plan-section: landed-changes -->

| 2026-09-02 | heldout-never-blind | opened the lane; status stub for the never-blind reclassification |
