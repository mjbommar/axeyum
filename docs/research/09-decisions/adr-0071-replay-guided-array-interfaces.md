# ADR-0071: Replay-Guided Array Interfaces on Canonical CDCL(T)

Status: accepted
Date: 2026-07-09

## Context

ADR-0070 made UFBV interface creation replay-guided, but arrays still reached
the canonical driver only as function-free scalar consequences or through
separate one-shot lazy/eager routes. The existing `ArrayElimination` already
retained the metadata needed for lazy select congruence, but obtaining its
`abstraction()` first constructed and then discarded every eager quadratic
Ackermann pair. Arrays therefore lacked both a true abstraction-only boundary
and participation in the live equality bus.

The first array slice must preserve ADR-0010's exact read-over-write semantics,
the function-before-array model-projection order from ADR-0013, replay-gated
SAT, and the eager certifying fallback. It must not imply that lazy store axioms
or unbounded extensionality are complete.

## Decision

Add a projection-preserving `abstract_arrays` boundary and materialize violated
base-array select pairs in the same bounded outer loop as dynamic UFBV pairs.

- `abstract_arrays` applies the existing exact read-over-write and bounded
  array-equality rewrites, replaces each remaining select over an array symbol
  with a fresh scalar symbol, and returns deterministic select/projection
  metadata without constructing pairwise select-congruence constraints.
- Array abstraction runs before function abstraction. This preserves the
  established QF_AUFBV reduction order and allows function arguments to contain
  abstracted array reads.
- The first canonical round contains no generated array or function interfaces.
  After a SAT candidate, unmaterialized selects on the same base array are
  scanned in deterministic discovery order. A pair is violated exactly when
  its rewritten indices evaluate equal and its fresh results differ. Proven
  ground-distinct indices are skipped by ADR-0069's exact cache rule.
- Every violated array pair materializes two semantic atoms, index equality and
  result equality, plus the valid array-function congruence clause
  `index_equal -> result_equal`. Both atoms are owned by exact warm BV; any UF
  terms in an index remain visible to the e-graph through the original atom.
- Function and array violations are batched together. The shared limits remain
  64 rounds and 512 raw interface equalities; array pairs cost two equalities.
  The DAG, theory-atom, Boolean, and deadline limits remain unchanged.
- Partial-round UNSAT transfers. A candidate with no violations projects
  functions first, arrays second, then replays every original assertion. Only
  successful replay returns SAT.
- Pure admitted QF_ABV uses route `abv-online-cdclt`; admitted mixed QF_AUFBV
  uses `aufbv-online-cdclt`. Existing cheap array refuters may still decide
  first. Every array-route `Unknown`, including a local resource/deadline bound,
  falls through to the existing array portfolio so the new route is additive.
  Eager reduction and all proof/evidence routes are unchanged.

This decision covers base-array select congruence after exact read-over-write.
It does not implement e-graph-triggered lazy store axioms, diff-skolem
extensionality for wide array disequality, majority-value array models, or
cross-round learned-state retention.

## Soundness Argument

Read-over-write and admitted bounded extensionality are equivalence rewrites.
Replacing each residual base-array select and UF application by an independent
fresh scalar, then asserting only a subset of valid congruence obligations, is
a relaxation of the original query. Every original model induces a model of
every partial round, so UNSAT of any round implies original-query UNSAT.

A SAT assignment is only a candidate. Equal-index/unequal-result array pairs
and equal-argument/unequal-result UF pairs are materialized and re-solved. A
candidate with no violations defines finite function and array tables for all
observed applications and reads. Projection in function-then-array order makes
UF-bearing array indices evaluable. Original-query ground evaluation is the
final acceptance gate; failed evaluation, projection, replay, or convergence
returns Unknown.

## Update (2026-07-10)

ADR-0084 supersedes the original function-first projection order. Canonical
AUFBV now projects class-owned arrays before function tables so array-valued
results and array-valued argument keys are both concrete before replay.

## Evidence

- The abstraction-only rewrite gate builds 24 symbolic reads with 24 rewritten
  assertions; eager elimination builds the same 24 plus 276 pair constraints.
- A forced equal-index/unequal-read case takes exactly two rounds, one candidate,
  one array pair, and two interface atoms before UNSAT.
- A nested array-read-then-UF ordering case takes exactly three rounds and adds
  one array pair followed by one function pair before UNSAT.
- A 24-symbolic-read table returns replayed SAT in one round with zero generated
  interfaces. Its forced-alias/distinct-result control adds 256 array pairs and
  then returns `ResourceLimit` at the 512-equality cap.
- The focused online module has 21 passing tests. Existing array/lazy/route
  suites remain green. A deterministic 256-case matrix agrees direct
  online/eager, front-door/eager, and direct online/Z3: 768 comparisons, no
  direct-route unknowns, no disagreements.
- Public curated runs at a 1 s per-file cap remain sound:

| corpus | files | sat | unsat | unknown | unsupported | oracle agree | disagreements | replay failures | PAR-2 mean |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_ABV | 193 | 94 | 91 | 6 | 2 | 185 | 0 | 0 | 72 ms |
| QF_AUFBV | 53 | 28 | 20 | 4 | 1 | 48 | 0 | 0 | 172 ms |

These are post-change safety/coverage measurements, not a same-tree performance
A/B. No general array-performance or solver-parity claim is made.

## Alternatives

- **Reuse `ArrayElimination::abstraction()` directly.** Rejected because the
  constructor had already paid the full eager quadratic pair build.
- **Treat array selects as synthetic uninterpreted functions.** Plausible, but
  it would introduce artificial function declarations and complicate array
  projection. A direct valid implication over shared semantic atoms is smaller.
- **Keep the one-shot lazy ABV loop as the only lazy route.** Sound, but arrays
  would remain outside canonical conflict learning, BV propagation, and mixed
  array/UF rounds.
- **Move lazy read-over-write and extensionality into this increment.** Rejected
  as too broad. Store-triggered axioms and diff skolems require explicit e-graph
  hooks, axiom queue state, and additional model construction.
- **Replace eager/certifying routes.** Rejected. The online slice has replay but
  no new proof artifact; existing evidence routes remain authoritative.

## Consequences

- Arrays now have a genuine DAG-linear abstraction boundary and participate in
  canonical equality sharing with exact BV and EUF.
- QF_AUFBV can refine an array alias and then expose a UF congruence violation
  in later canonical rounds while preserving replayable models.
- Read-over-write still expands before the bus. The next array depth work is
  P2.2's e-graph-triggered axiom queue, lazy store axioms, extensionality, and
  scalable array defaults; mixed BV+LIA/`str.len` remains the next P1.6 theory
  breadth step after this bounded array slice.
