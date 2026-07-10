# ADR-0076: Candidate-Triggered Cross-Array Equality Queue

Status: accepted
Date: 2026-07-10

## Context

ADR-0073 gave every array equality one local diff witness and observations at
indices already relevant to that equality. It deliberately did not cross diff
indices between equality atoms. That kept initial construction linear, but left
transitive equality conflicts incomplete. For example:

```text
a = b
b = c
a != c
```

The `a != c` candidate can choose different reads at its own diff index while
the two true equalities are observed only at their own indices. The partial
model then reaches original replay and conservatively returns `Unknown`, even
though equality transitivity makes the query unsatisfiable.

Eagerly observing every equality at every diff index would recover completeness
but rebuild the quadratic cross-product ADR-0071 removed. Z3 instead keeps array
axioms in explicit new/delayed/applied state and schedules them when e-graph
merges make them relevant (`array_axioms.cpp`, `array_solver.cpp::merge_eh`).

## Decision

Add the first bounded cross-equality queue slice to canonical ABV/AUFBV.

- Retain each online equality's original operands, own diff index, and the ROW
  abstraction's next internal-symbol counter after initial preparation.
- Keep one deterministic queue state per equality: `New`, `Delayed`, or
  `Applied`. A candidate-false equality is delayed when its operands are not
  connected by candidate-true equality flags.
- Build a stable adjacency map from candidate-true equality flags. When a false
  equality's endpoints become connected, use deterministic BFS to select one
  shortest path in equality-discovery order.
- At the false equality's own diff index, add paired observations only to path
  edges that do not already carry that index. Mark the source queue entry
  applied. Do not construct observations for unrelated edges or false
  equalities with no true path.
- Build each new observation through the shared `RowCtx` resolver. Append its
  base-select and store sites to the existing canonical metadata, rebuild the
  select groups, and reuse the initial function replacements. If an observation
  unexpectedly exposes a new UF application, decline to the existing fallback
  instead of solving an under-abstracted term.
- Preserve constant-array read constraints for dynamically added sites.
- Charge each cross observation to the shared 512-interface budget and retain
  the global 4,096 ROW-site ceiling, 64-round limit, and caller deadline.
- Keep `Applied` entries after materialization; reset a non-applied entry to
  `New` when it is no longer candidate-false. A delayed entry is reconsidered on
  every later candidate.

## Soundness Argument

Every canonical round remains a relaxation. A queued observation does not assert
that an equality flag is true. It merely creates scalar reads at one additional
index. The only eventual equality axiom is the valid implication

```text
flag(a = b) -> select(a, k) = select(b, k)
```

for a path edge and the source disequality's diff index `k`. ROW and base-select
consistency for newly created reads are materialized through the same existing
candidate-violation checks. Therefore UNSAT from any partial round transfers to
the original query. SAT is still accepted only after function projection, array
projection, and evaluation of every original assertion.

The path is chosen only from flags that are true in the current complete BV
candidate. A different candidate recomputes connectivity. Deterministic term
ordering and equality-discovery order remove hash iteration from scheduling.
All resource overflows and unseen dynamic UF roots decline to `Unknown`/fallback.

## Evidence

- `a=b`, `b=c`, `a!=c` now returns UNSAT after adding exactly two cross
  observations, with one applied queue entry and at most eight rounds.
- A disconnected `a=b`, `c!=d` model remains SAT and replays with one delayed
  entry and zero cross observations.
- A transitive path whose endpoint is `store(a, f(x), v)` reuses the initial UF
  abstraction, activates ROW, returns UNSAT, and stays within twelve rounds.
- A focused state-machine test exercises `New -> Delayed -> Applied` and pins the
  deterministic two-edge BFS path.
- A 40-array/20-disequality stress case stops after exactly 512 cross
  observations with `ResourceLimit`, never a guessed verdict.
- The 20-shape, 256-seed matrix performs 768 direct/eager,
  front-door/eager, and direct/Z3 comparisons. All remain clean; 456 comparisons
  now carry equality/disequality/store-equality/UF-index/transitive shapes.
- All 788 solver library tests pass.
- Single-run public 1 s measurements preserve decisions and replay:

| corpus | files | decided | disagreements | replay failures | PAR-2 mean |
|---|---:|---:|---:|---:|---:|
| QF_ABV | 193 | 187 | 0 | 0 | 84 ms |
| QF_AUFBV | 53 | 49 | 0 | 0 | 206 ms |

This is a completeness/architecture increment, not a performance claim.

## Alternatives

- **Cross every diff index with every equality during preparation.** Rejected:
  it restores an eager quadratic observation product even when the candidate
  never relates the arrays.
- **Rely on final replay.** Sound but incomplete; it detects the missing
  transitive constraint only after search and returns `Unknown`.
- **Merge projected array models without adding theory constraints.** Useful
  for SAT model quality, but it cannot justify UNSAT and does not repair the
  relaxation.
- **Move immediately to an in-search Z3-style array theory plugin.** This is the
  destination, but it requires dynamic theory-atom/variable insertion and
  backtrackable queue trails in `CdclT`. The bounded outer-round queue proves the
  scheduling contract first without duplicating that larger redesign.

## Consequences

- Canonical ABV/AUFBV closes transitive array equality/disequality conflicts
  without prebuilding cross observations.
- Queue state and cross-observation telemetry make the remaining migration
  measurable.
- Outer canonical rounds still rebuild `CdclT`; queue state is not yet trailed
  with e-graph merges/backtracking. General class-parent select propagation,
  multiple-path scheduling, e-graph-class model ownership, warm reuse, and proof
  logging remain.
