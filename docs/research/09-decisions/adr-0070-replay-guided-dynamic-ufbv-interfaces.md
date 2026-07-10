# ADR-0070: Replay-Guided Dynamic UFBV Interfaces

Status: accepted
Date: 2026-07-09

## Context

ADR-0069 removed same-function application pairs whose congruence antecedent
was statically impossible, but every remaining symbolic pair was still emitted
before search. That kept construction and admission quadratic for symbolic
tables even when the first function-free model was already consistent.

Axeyum already uses replay-guided functional-consistency refinement in the
offline lazy Ackermann route. Canonical UFBV combination can use the same
soundness pattern while retaining `CdclT`, the e-graph, exact warm BV conflicts,
and BV-to-EUF propagation for every pair that actually becomes relevant.

## Decision

Materialize symbolic UFBV interface pairs from candidate-model violations in a
bounded outer loop around canonical `CdclT`.

- Prepare the projection-preserving function abstraction once. The first round
  contains formula atoms but no generated application-pair interface atoms.
- Run canonical `CdclT` over the e-graph and exact warm BV theory. Expose its
  completed BV candidate assignment without projecting it prematurely.
- Scan same-function application pairs in deterministic discovery order. Apply
  ADR-0069's exact ground-distinct filter first. For each unmaterialized pair,
  evaluate the rewritten argument tuples in the candidate assignment; if the
  tuples are equal and the fresh result values differ, record a violation of
  functional consistency.
- Materialize all violated pairs from that candidate as the existing argument
  and result equality atoms, then rebuild the canonical round. A pair is added
  at most once.
- Stop after at most 64 rounds or 512 raw materialized interface equalities.
  The existing DAG, theory-atom, Boolean, and shared-deadline caps remain.
- If a round is UNSAT, return UNSAT. If a SAT candidate has no violations,
  project `FuncValue` interpretations and replay every original assertion;
  accept SAT only when replay succeeds. Unknown/resource/timeout outcomes stay
  first class under the existing front-door terminal/fallback policy; eager
  reduction remains available where that policy or proof production selects it.

The current slice rebuilds the Boolean driver and warm BV solver after each
batch. Terms are interned and abstraction metadata is reused, but learned
clauses and SAT state do not cross rounds.

## Soundness Argument

Replacing each UF application by a fresh result variable and asserting only a
subset of valid congruence obligations is a relaxation of the original query:
every original model induces a model of every partial round. Therefore UNSAT of
any round implies original-query UNSAT.

A SAT assignment is not treated as proof that omitted pairs are irrelevant. It
is only a candidate:

1. Every equal-argument/unequal-result pair visible in that assignment is
   materialized and the query is re-solved.
2. A candidate with no detected violations is projected to a total function
   interpretation.
3. Every original assertion is evaluated under that projected assignment.

Only successful replay returns SAT. Missing values, failed evaluation,
projection failure, bounds, or non-convergence return Unknown rather than a
verdict. Ground-distinct omission remains exact by ADR-0069.

## Evidence

- A BV-ordering congruence case takes two rounds: one candidate, one violated
  pair, two deduplicated interface atoms, then UNSAT.
- A nested `x = y` / `f(g(x)) < f(g(y))` case with a permissive inner branch
  takes three rounds and two pairs, proving refinement reaches a second-layer
  violation after rebuilding.
- A 24-application symbolic table that previously exceeded the static
  quadratic cap now returns replayed SAT in one round with zero materialized
  pairs.
- The forced control constrains all 24 symbolic keys to zero and all results to
  distinct bytes. It finds one candidate, materializes 256 pairs, and returns
  `ResourceLimit` before exceeding the 512-interface cap.
- `bug520` returns replayed SAT from its first candidate with zero materialized
  pairs. The static mechanism tests still pin BV propagation when a pair is
  materialized.
- Three deterministic 512-case matrices remain clean: direct online/eager,
  front-door/eager, and direct online/Z3 (1,536 comparisons). The public corpus
  remains 6/6 decided and agreeing with zero replay failures. The solver library
  is green at 763 tests.

Ten release-mode public-corpus samples compare the dynamic route with the
immediately preceding ADR-0069 static route measured in the same session:

| route | corpus PAR-2 mean | `bug520` |
|---|---:|---:|
| dynamic violated pairs | median 0.647 ms (0.598-1.320 ms) | median 2.84 ms (2.58-5.72 ms) |
| static ground-pruned pairs | median 2.89 ms (2.64-5.06 ms) | median 8.88 ms (8.35-19.19 ms) |

The median improvement is about 4.47x for the six-row mean and 3.12x for
`bug520`. Z3 measured 9-15 ms on the row (12.5 ms median), so Axeyum is about
4.4x faster on this narrow instance distribution. Six public rows do not
support a general UFBV or solver-parity claim.

## Alternatives

- **Keep every statically possible pair.** Complete, but measured slower and
  rejects harmless symbolic tables at construction time.
- **Accept a candidate after checking only fresh-result consistency.** Rejected:
  projection and original replay remain the SAT soundness anchor.
- **Use candidate model equality to omit pairs permanently.** Rejected. Model
  values guide which valid obligation to add; they do not prove global
  disequality or justify a verdict.
- **Add one violated pair per round.** Sound but creates avoidable rebuilds.
  Every violation in deterministic scan order is batched.
- **Mutate `CdclT` with new semantic atoms in place.** This is the longer-term
  architecture if rebuild cost dominates, but it requires dynamic semantic-atom
  and Boolean-variable APIs, clause extension, and theory registration changes.
- **Use the offline lazy Ackermann loop instead.** It has the same refinement
  proof but loses the canonical e-graph/BV propagation and conflict-learning
  path this phase is meant to establish.

## Consequences

- Symbolic UFBV tables no longer pay or fail the full quadratic interface set
  when their candidate model is already functionally consistent.
- Materialized pairs still use the exact e-graph/BV bus, propagation, conflict
  reasons, and replay route from ADR-0066 through ADR-0069.
- Multi-round cases rebuild SAT/theory state. Preserve state only after corpus
  telemetry shows rebuild time dominates; the bounded current route is simpler
  and already materially faster on the measured slice.
- The next P1.6 breadth step is array participation on the live equality bus,
  followed by mixed BV+LIA/`str.len`; eager certifying fallbacks remain.
