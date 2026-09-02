# Lane: shape-census — what the ready frontier is shaped like

<!-- plan-section: lane-status -->

**shape-census (`DONE`, shape-census, 2026-09-02).** Measured the shape of the
dependency-ready open frontier, so the next producer can be designed against a
population whose shape is known rather than assumed.
`scripts/frontier-shape-census.py` parses every ready fact's `formal.statement`
into a shape signature and buckets it at two granularities; the artifact is
`artifacts/autogenesis/frontier-shape-census-v1.json`, gated by `--check` as a
fourth guard in `scripts/check-merge-hygiene.sh` and guarded for single
ownership by `scripts/check-generated-artifact-ownership.py`.

**The finding is negative, and it is the deliverable.** 217 dependency-ready
facts; **186 are held-out** blind evaluation population; 31 remain. The primary
population — ready, `proof-route-only`, no matching contract — is **24 facts**,
of which **11 are mutation negative controls** (false by construction) and
**9 are divergence-blocked** (the mirror names a construction that is not ours,
so it is a different proposition and no proof effort closes it). **Four facts
are genuinely targetable, and two of those are Goldbach and the twin prime
conjecture.** The largest coarse bucket holds **one** targetable fact.

The largest bucket by raw size — nine `Nat` equations with no hypotheses, four
of them the same statement over different bitwise operators — has **zero**
targetable members: three are mutation controls and six are blocked on
`Nat.testBit` returning a `Nat` here and a `Bool` in Mathlib. Ranked on size
alone it is exactly where a producer would have been pointed. `Nat.testBit_land`
is already an admitted theorem in this kernel, stated with `AxNat.mul` where
Mathlib has `&&`; the work is done and the mirror still cannot be flipped.
Confirmed independently by `scripts/brief-step0.py`: six targets, six
`DIVERGENCE-BLOCKED` verdicts.

**Second finding, unasked for.** `fact-frontier.py:held_out_fact_ids()` reads
`nursery-v1.json` only. The 2026-08-29 refill preregistered **190 more held-out
rows** in `nursery-v2-extension.json`, **180 of them dependency-ready**, and the
queue's own `⛔ HELD-OUT` warning is blind to every one.
`check-autogenesis-holdout-isolation.py` already reads both and says in a
comment that a gate reading only v1 would pass vacuously; the queue never got
the same fix. The census excludes the union and reports the gap in
`population.held_out_source_gap`. Fixing the queue's loader is a one-function
change and is not this lane's to make.

**Next, for whoever takes the producer question:** read
[`docs/research/11-design-review/2026-09-02-what-the-frontier-is-shaped-like.md`](../../research/11-design-review/2026-09-02-what-the-frontier-is-shaped-like.md)
before writing a third producer contract. Its recommendation is: refill the
queue first, then decide the `Nat.testBit` codomain question (six ready facts
hang on it, and it is a construction decision no producer can take), then fix
the queue's held-out loader. A producer working perfectly on the best available
bucket today would close one fact.

<!-- plan-section: landed-changes -->

| 2026-09-02 | `28c4cfa45` | `check-merge-hygiene.sh` gains the census guard (three outcomes: exit 2 is reported, not failed), mutation M7 kills exactly one test; 24 controls in `test_frontier_shape_census.py`; artifact registered with `check-generated-artifact-ownership.py` (`crates` added to its sandbox, since the frontier's registry validation checks paths under it). |
| 2026-09-02 | `91684bf4e` | `scripts/frontier-shape-census.py` + `artifacts/autogenesis/frontier-shape-census-v1.json`: shape signatures, two bucket granularities, `--check` with exit 2 for unanswerable. |
