# ADR-0158: Admission-controlled range demand lowering

Status: proposed
Date: 2026-07-14

## Context

ADR-0157 proves that sparse, replay-safe bit lowering is semantically viable,
but its unconditional implementation fails the real Glaurung performance gate.
The default remains about 1.42x Z3 while v1 reaches about 4.49x; bit blast rises
from 47% to 83% of total Axeyum time despite 100% decisions and zero
disagreements.

The implementation explains the result. It first traverses the reachable DAG
to count available bits, then propagates demand one `(TermId, bit)` pair at a
time. It lazily allocates a width-sized Boolean vector for every demanded term,
retains another width-sized optional-literal vector during lowering, and scans
every arena term to materialize the selected graph. This can cost more than the
simple AIG wiring avoided by slicing, especially when barriers or overlapping
requests make most bits live.

A runtime cost model cannot require the full v1 demand result merely to decide
whether computing that result was worthwhile. Admission and exact propagation
must therefore be separate, bounded stages.

## Proposed decision

Keep ADR-0157's force-on diagnostic/experimental route unchanged and off by
default. Add a distinct admission-controlled experiment; do not silently change
the meaning of `demand_bit_slicing` or enable either route automatically.

### Stage 0: cheap structural admission

Traverse only the root-reachable term DAG once with dense term visitation and
constant-size per-term metadata. Do not allocate any width-sized bitset or
per-bit work item. Record:

- reachable term count and summed available bit width;
- widths removed by narrowing structural edges (`extract`, extension high
  constants, concat branches not selected by an enclosing slice, and constant
  rotations);
- the count and total operand width of conservative barriers;
- maximum source/result width ratio for a narrowing edge; and
- whether a register-slice candidate exists at all.

The estimator is deliberately pessimistic about savings: shared/overlapping
requests count once only when that is provable from constant-size metadata, and
uncertain cases count as fully live. Reject before exact analysis unless both an
absolute avoided-bit floor and a wide avoided/available ratio are satisfied.
Thresholds are explicit benchmark-policy inputs until calibrated; they are not
wall-clock adaptive and therefore preserve deterministic behavior.

### Stage 1: bounded range demand

For admitted queries, propagate half-open bit ranges rather than individual
bits. Each term starts as `None`, `Full`, or a small sorted set of disjoint
ranges. Insertions merge overlaps/adjacency and enqueue a term only when its
demand grows. Exact structural transfer maps ranges through extract, concat,
extension, rotation, pointwise operations, and ITE; a non-local operator
promotes its operands to `Full` exactly as ADR-0157 requires.

Use an inline small-range representation. If fragmentation exceeds its fixed
capacity, conservatively promote that term to `Full`; do not allocate an
unbounded range set. Charge every first visit, range insertion, merge, promotion,
and transferred edge against an explicit deterministic analysis budget. Budget
exhaustion abandons the partial plan and invokes the ordinary full lowerer; it
never changes a verdict.

The exact stage computes demanded/available bits without expanding ranges into
width-sized Boolean arrays. Re-check the savings threshold after propagation.
If barriers, sharing, or overlap erase the predicted win, fall back immediately
to full lowering.

### Stage 2: range-backed materialization

Lower reachable demanded terms in topological `TermId` order, but iterate only
their retained ranges. Store sparse `(bit_index, literal)` bindings directly;
do not construct a width-sized `Vec<Option<AigLit>>` for every partial term.
Full barriers continue through the existing complete operator builders. Sparse
symbol completion and mandatory replay retain ADR-0157's soundness contract.

### Telemetry and policy identity

Record separately:

- admission time and decision (`no-candidate`, `insufficient-estimate`,
  `admitted`);
- estimated available/avoided bits and configured thresholds;
- exact-analysis time, work consumed/budget, range merges/promotions, and
  demanded/available bits;
- whether the query sliced or fell back, with a stable fallback reason; and
- ordinary AIG/CNF/stage/verdict/replay metrics.

The benchmark configuration hash includes every threshold and budget. Artifact
summaries partition results by Glaurung family and admission/fallback reason.

## Acceptance gate

- ADR-0157's exhaustive semantic, sparse-model completion, SAT/UNSAT replay,
  deadline, full-lowerer, and incremental-lowerer tests remain green.
- Range propagation is exhaustively equivalent to the v1 bitset planner on
  small structural DAGs, including disjoint shared slices, straddling concat,
  sign-bit reuse, rotations, ITE, and full barriers.
- Budget exhaustion, range fragmentation, failed precheck, and failed exact
  threshold all deterministically select the unchanged full lowerer and match
  its structure/verdict/model behavior.
- On rejected Glaurung queries, aggregate admission overhead is below a
  predeclared low-single-digit ceiling; the first target is 2% of default cold
  time.
- On admitted `register-slice` queries, analysis plus sparse lowering beats the
  full bit-blast stage and reduces AIG/CNF sizes.
- Five representative and full processes remain 100% decided with zero errors,
  disagreements, or replay failures. Whole-corpus end-to-end time must be no
  worse than default and the `register-slice` family must improve. No default or
  auto selection follows without a new acceptance decision.

## Alternatives

- **Choose from the complete v1 demand ratio.** Rejected: it pays the cost that
  caused the 4.49x regression before it can decline.
- **Use elapsed-time cutoffs.** Rejected: hardware/scheduling-sensitive choices
  violate deterministic policy behavior. Use deterministic work budgets and
  measure elapsed time only as evidence.
- **Tune only the v1 bitset implementation.** Rejected as the complete plan:
  faster per-bit propagation still does unnecessary work on unprofitable
  queries and cannot bound downside.
- **Route every syntactic extract directly to a specialized lowerer.** Deferred:
  a focused fast path may follow, but shared terms, concat boundaries, ITE, and
  barriers still require a sound demand union and fallback contract.
- **Prioritize SAT tuning instead.** Rejected for this slice: the failed run
  spends 83% in bit blast, and the default profile still ranks lowering ahead
  of SAT.

## Consequences

GQ4-v2 becomes an admission problem as well as a semantic lowering problem.
The design bounds the cost of declining, makes profitable selection observable,
and replaces per-bit planning/materialization with range-oriented state suited
to lifter slices. It remains experimental and cannot distract from GQ7: warm
reuse still requires a persistent Glaurung solver lifecycle that its current
one-shot trait does not expose.

## Implementation checkpoint (2026-07-14)

The first isolated `axeyum-bv` implementation is complete behind the explicit
`lower_terms_range_demanded` entry point. It adds:

- a root-reachable screen whose extract-use envelope only credits avoided bits
  when every observed use of the narrowed source is an extract;
- four inline disjoint ranges per term, adjacency/overlap merging, conservative
  full promotion on a fifth fragment, and a deterministic work budget;
- a second exact savings gate after range propagation; and
- direct sparse term-bit materialization without width-sized Boolean or
  optional-literal vectors for partial terms.

Rejected and budget-exhausted plans call the ordinary full lowerer and retain a
stable decision reason. Six focused additions cover profitable register slices,
unchanged full fallback, deterministic budget fallback, structural dense-v1
equivalence, fragmentation promotion, evaluator replay, and deadline handling;
the complete BV unit suite is 32/32 green and focused strict Clippy passes under
the repository memory cap.

This checkpoint does not accept the ADR. Solver configuration, artifact policy
identity, per-reason telemetry, and the real `register-slice`/whole-corpus timing
gates remain outstanding. The default and ADR-0157 force-on behavior are
unchanged.
