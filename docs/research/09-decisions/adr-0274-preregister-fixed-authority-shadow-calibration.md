# ADR-0274: Preregister fixed-authority shadow-limit calibration

Status: accepted
Date: 2026-07-19

Result state: executed and accepted; zero census rows

## Context

ADR-0273 completed its exact 42-process calibration and rejected it because no
Axeyum ladder value made both cold and warm cells at least 95% decided. It also
made a more basic combination hazard visible: cold Z3 is Glaurung's sole
exploration/model authority, so increasing Z3's limit changed the measured
ordered stream from 67 checks at tier 0 to 4,846 checks at tier 9. Z3 and
Bitwuzla values selected independently at different tiers therefore were not
tested on one common population and cannot be combined into a confirmation
triplet.

The first calibration nevertheless provides a clean authority bracket. At
`z3-rlimit=100000`, both cold and warm Z3 decide and agree on all 4,846 ordered
checks in each of three byte-stable repetitions, with zero wall/other stops.
That is the smallest ADR-0273 Z3 tier satisfying the registered gate. This ADR
fixes that authority configuration and performs a separate, explicitly
observation-aware shadow calibration. It extends neither ADR-0273's ladder nor
its interpretation.

No ADR-0274 process was executed while defining this protocol.

The zero-row protocol is executable in
`scripts/run-glaurung-fixed-authority-shadow-calibration.py` and
`scripts/analyze-glaurung-fixed-authority-shadow-calibration.py`. They reuse
ADR-0273's frozen source/binary/linkage preflight but emit a distinct ADR-0274
campaign schema. The analyzer adds exact across-tier authority identity,
outcome, finding, and outer-work equality before applying either shadow
selection. Focused tests freeze the 10-by-3 order, constant Z3 limit, ladder
endpoints, independent smallest-tier selection, and missing-backend rejection.

## Decision

Run a new 10-tier, N=3 calibration with Z3 fixed at its qualifying authority
limit and Axeyum/Bitwuzla varied only as non-authoritative shadow cells. Select
their limits only on the resulting invariant ordered stream.

### Frozen identities and authority

Reuse without rebuilding or relinking:

- Glaurung commit
  `dc06a3740d989f5a71f3a1cef4ba5111c5188f36`;
- ADR-0273's measured Axeyum tree identities;
- release `ioctlance` SHA-256
  `d96520a04d5dd4825957dc3e07e1fd11a24bad220c55baae539ec9f8a10db5f7`
  and all 12 dynamic-library paths/hashes registered there; and
- `tcpip.sys` SHA-256
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`.

Cold Z3 remains the sole authority under `AnyModel`, and both Z3 cells use
`GLAURUNG_Z3_RLIMIT=100000` in every process. No concretization policy other
than the default, symbolic memory, timeout continuation, cold retry, or
fallback override is enabled.

### Frozen shadow ladders

Run all ten rows; do not stop when either shadow backend qualifies:

| tier | Axeyum progress checks | Bitwuzla termination polls |
|---:|---:|---:|
| 0 | 8,192 | 1 |
| 1 | 16,384 | 2 |
| 2 | 32,768 | 4 |
| 3 | 65,536 | 8 |
| 4 | 131,072 | 16 |
| 5 | 262,144 | 32 |
| 6 | 524,288 | 64 |
| 7 | 1,048,576 | 128 |
| 8 | 2,097,152 | 256 |
| 9 | 4,194,304 | 512 |

These ladders are deliberately observation-aware. Axeyum starts by reproducing
ADR-0273's failed maximum and then doubles; Bitwuzla replays its complete
registered range because ADR-0273's apparent value 4 came from a smaller
authority stream. Aligned tier numbers are execution order only;
`cross_backend_unit_equivalence` remains false.

### Frozen execution and invariance gates

Run three fresh sequential processes per tier, 30 total, tier-major and
repetition-minor, pinned to logical CPU 2. Reuse ADR-0273's exact fixed
environment, memory guard, 60,000 ms per-check wall safety cap, 2,700-second
outer process cap, unique trace roots, all-findings confidence annotation, and
first-20/338 work boundary. Retain and hash the same campaign, stdout, stderr,
run-record, trace, validator, executable, driver, and linkage artifacts. A
failed process is retained and never silently rerun.

In addition to ADR-0273's per-tier N=3 gates, the analyzer must require across
all ten tiers:

1. an identical ordered check-identity vector (event/check/path/query/purpose/
   scope/constraint identity), proving the authority stream is invariant;
2. 4,846 checks in every repetition;
3. all cold/warm Z3 outcomes decided, mutually agreeing, and identical;
4. identical raw/high-confidence/diagnostic finding output and outer
   exploration-work partitions; and
5. zero authority, wall, outer-deadline, operational, fallback, validation, or
   confinement failure.

Any violation rejects the extension. The observed ADR-0273 stream size is a
fixed reproduction gate, not permission to trim a differing stream.

### Shadow selection rule

For Axeyum and Bitwuzla independently, select the smallest registered value for
which both cold and warm cells on all three repetitions:

1. decide at least 95% of the 4,846 ordered occurrences;
2. reproduce the complete per-occurrence outcome and typed stop-reason vector;
3. have every decided verdict agree with the fixed Z3 authority;
4. type every nondecision as `resource-limit`; and
5. record zero wall-timeout, other, error, no-solver, fallback, or invalid-delta
   occurrence.

If either backend has no qualifying value, ADR-0274 is rejected. Do not add a
larger value, weaken 95%, omit warm or cold, or substitute timing after seeing
the rows without another ADR. Timing remains descriptive and cannot support an
equal-work or solver-speed claim.

### Confirmation boundary

Even a successful ADR-0274 result does not authorize the 338-function census.
A later zero-census ADR must freeze the combined triplet
`{z3=100000, selected Axeyum, selected Bitwuzla}`, rerun it on the first-20
boundary as an exact joint reproduction gate if needed, and preregister the
full-census population, repetitions, finding/work gates, and analysis. The
eventual result remains a bounded cold-Z3-authoritative census, not labeled
recall, precision, equal work, or cross-authority finding parity.

## Evidence

### Observed result

All 30/30 processes complete with validator-clean v4 traces and reproduce one
4,846-check authority stream across every tier. The invariant identity/outcome
hashes are `89d28a2978e4d9fc1bbba78bb1413a80fffc408c0bbc4dcef51b1eb6b5e1e928`
and `f0b5580fcc6bba0accd6a91fc76a1373a60835af84c5982394ca9d6b3312fafa`.
Campaign/analysis hashes are
`0526f925aba7816e61df3598553f7bb0ed323a8b492f5d3e700add6ec193ceb7`
and `7b20e363ee5558de02e5534e047c2645ffe8a65541be239754fc9fd03ad18cf6`;
the compact result is [retained here](../../../bench-results/glaurung-fixed-authority-shadow-calibration-20260719/README.md).

The selector accepts Axeyum 32,768 progress checks (tier 2) and Bitwuzla 512
termination polls (tier 9), beside fixed Z3 rlimit 100,000. All selected
cold/warm cells decide 4,846/4,846 with agreement. Every lower nondecision is
resource-limit; wall/other/operational/fallback/deadline failures are zero. No
census row exists.

ADR-0273's retained result supplies the fixed-authority choice and the need for
this separation:

- Z3 tier 9: 4,846/4,846 cold and warm decisions at `rlimit=100000`;
- highest Axeyum tier: 4,233/4,846 cold and 3,280/4,846 warm decisions at 8,192;
- Bitwuzla's apparent tier-2 qualification: only 143 ordered checks, so it is
  not portable to the tier-9 stream; and
- 42/42 validator-clean processes, stable N=3 vectors, and zero wall/deadline
  stops, making a deterministic fixed-authority extension technically viable.

## Alternatives

- Combine ADR-0273's independently selected values: rejected because those
  values were observed on different authority-generated populations.
- Extend all three ladders together: rejected because it would preserve the
  population confound.
- Set every shadow limit to a very large number: rejected because it would not
  characterize the deterministic decision frontier and could adapt the full
  census to an unmeasured cost.
- Run the 338-function census now: rejected by ADR-0273's failed Axeyum gate and
  the missing common-stream triplet.
- Reinterpret the result as an Axeyum solver defect: rejected. This is a bounded
  progress-limit calibration result; solver optimization remains PLAN item 4.

## Consequences

The harder-driver experiment now has one common-population triplet, but a later
zero-census ADR must jointly reproduce it and freeze the census before any
338-function row. Correctness and deployability still lead; A1 remains
configuration/measurement, A0 remains reproducibility infrastructure, and
symbolic memory stays closed.
