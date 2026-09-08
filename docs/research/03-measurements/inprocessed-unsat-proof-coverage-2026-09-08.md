# Inprocessed `unsat`: what the certificate now covers, and what it costs

2026-09-08. Evidence behind
[ADR-1780](../09-decisions/adr-1780-a-reduction-link-carries-the-derivation-and-the-renaming.md).

## The question

Before this measurement, `sat_bv_backend` with `cnf_inprocessing` on checked
its `unsat` proof against the **reduced** formula, so the BVE link was trusted
rather than checked — [ADR-1750]'s own named open item. `ReductionLink` closes
it by carrying the passes' `DRAT` derivation *and* `compact`'s variable
bijection in one object. Three things needed measuring rather than asserting:

1. does an inprocessed `unsat` actually check against the original formula, on
   a real corpus rather than a fixture;
2. how big the certificate gets, split by which pass produced it;
3. what checking it costs.

[ADR-1750]: ../09-decisions/adr-1750-a-reducing-pass-must-record-what-it-derived-not-what-it-deleted.md

## Method

```
./target/release/axeyum-bench <200 QF_BV parity files> \
    --backend sat-bv --prove-unsat --inprocess --vivify \
    --timeout-ms 24000 --jobs 8
```

The corpus is the pinned 200-file list in
`bench-results/parity-lists/QF_BV.txt`, symlinked into one directory (the
harness walks a directory). Release build, `--jobs 8`.

**The host was loaded (load average ~30: a concurrent `clippy --all-features`
and other lanes), so every WALL TIME below is pessimistic and should not be
compared against a number taken on an idle box.** Step counts are
load-independent and are the numbers this note is really about. The
check/solve *ratio* is same-run and same-machine, so it is meaningful even
though its two halves are both inflated.

## 1. Coverage

| | instances |
|---|---:|
| files | 200 |
| `unsat` | 117 |
| `sat` | 55 |
| `unknown` (all timeouts) | 28 |
| disagreements with declared `:status` | **0** |

Of the 117 `unsat`:

| | count |
|---|---:|
| checked against the **ORIGINAL** formula | **117** |
| checked against the reduced formula | 0 |
| carrying neither coverage key | 0 |
| links a pass left unjustifiable | 0 |

The two coverage keys are emitted by one function from the `ProofCoverage` the
check itself returned, so "117 and 0" is a partition and not two independent
counts that happen to sum.

`xor_propagate`'s augmentation was skipped for the proof on **3 of 117** — the
instances where Gaussian elimination found implied units, which are entailed
but not `RUP`. On the other 114 the stage found nothing to add, so the skip
costs nothing there.

## 2. Certificate size, by pass

Steps emitted into the prefix, over the 117 `unsat`:

| pass | median | max | total |
|---|---:|---:|---:|
| subsumption | 33 | 408,981 | 1,035,789 |
| vivification | 0 | 98,946 | 295,672 |
| BVE | 32 | 1,562,115 | 2,757,149 |
| **prefix (all passes)** | **658** | **1,971,102** | **4,088,610** |
| search's own steps | 1 | 12,527 | 50,238 |

Two things worth reading off this table:

**The prefix dwarfs the search, by about 81x in total steps.** That is
ADR-1750's finding reproduced on a different corpus and at a different scale
(it measured 37.7 M against ~36 k on one 3.1 M-variable instance). The
certificate for an inprocessed solve is mostly the reduction, not the search.

**On 85 of 117 instances the search emitted exactly one step — the empty
clause.** The reduction refutes the formula at level zero and the search only
has to notice. So for the majority of this corpus, the thing the old code was
*not* checking was the entire proof, and what it *was* checking was one step.
That is the sharpest available statement of what the gap was worth.

## 3. Checking cost

| | value |
|---|---:|
| total check time, 117 `unsat` | 9,577.7 ms |
| median | 0.1 ms |
| max | 3,408.0 ms |
| total `solve_ms`, same instances | 12,408 ms |
| **check / solve** | **0.772** |

So checking the linked proof costs roughly three quarters of the search it
certifies on this corpus, on a loaded host. That is affordable, and it is far
from the naive "emit everything and check forward" cost the lane was warned
about — because `check_drat_backward` verifies only the steps in the empty
clause's dependency cone. ADR-1750 measured backward at 231x forward on a
corpus-scale proof; this run is downstream of that choice.

**Check time tracks the cone, not the prefix.** The most expensive check
(3,408 ms) had a 82,938-step prefix, while the largest prefix (1,971,102 steps)
checked in 350 ms. Ranking instances by proof size to predict checking cost
would be wrong on this data.

## 4. What this says about the step cap

`MAX_LINKED_PROOF_STEPS` is 8,000,000. The largest prefix observed is
1,971,102, so **the cap clears the worst instance in this corpus by 4.06x** —
thin, and worth saying plainly because the constant's size invites the opposite
assumption. Two consequences:

- A larger corpus should be expected to cross it. That is a visible
  `unsat_proof_checked_against_reduced` with `unsat_proof_reduced_reason = 2`
  and the step count, not a failure — and the right response is to wire the
  streaming route (`ReductionLink::lifting_sink` into a `TextProofSink`,
  checked by `check_drat_backward_reader`), not to raise the constant.
- The peak allocation is about **twice** what the step count suggests, because
  `check_unsat` clones the stored prefix into the concatenation it checks.

## Not measured here

- **Idle-host timings.** Every millisecond above is under load ~30.
- **The `sat` side**, which was separately re-verified as sound earlier the
  same day (173 files cross-checked against declared `:status`, zero
  disagreements) and is unchanged by this work.
- **Whether inprocessing is worth enabling.** It is not, at a 24 s budget, on
  the measurement this repository already has (186 decided / PAR-2 960.5
  against a baseline 184 / 926.8). This note is about whether its proofs check,
  which is a different question with a different answer.
