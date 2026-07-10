# ADR-0078: Explanation-Guarded Parent-Select Scheduling

Status: accepted
Date: 2026-07-10

## Context

ADR-0077 puts array equalities on the canonical backtrackable e-graph, but base
select refinement still groups reads by their original array symbol. A complete
SAT candidate can therefore contain `a = b` in `EufTheory` while the array layer
does not recognize `select(a, i)` and `select(b, j)` as reads from one class.
ADR-0073 compensates by preparing every direct-symbol equality at every relevant
query index. That is sound but rebuilds an equality-by-read cross product before
the Boolean search establishes that the equality is active.

Z3 instead attaches parent selects to array classes and schedules array axioms
when classes merge (`array_solver.cpp::merge_eh` and `add_parent_select`). cvc5
similarly merges per-class index/store metadata in `ArrayInfo::mergeInfo`. Axeyum
does not yet support dynamic SAT-atom insertion during `CdclT`, so the first slice
must preserve the bounded canonical-round boundary while taking relevance from
the live e-graph.

One soundness constraint is load-bearing. A select-congruence lemma between two
different parents is valid only while the equalities that merged those parents
hold. Persisting the lemma unguarded across rebuilt rounds could make another
Boolean branch spuriously UNSAT.

## Decision

Schedule candidate-violated direct-symbol parent-select pairs from final live
e-classes, and guard every cross-parent lemma with its e-graph explanation.

- `EufTheory` may pre-register read-parent terms without asserting anything. At
  a theory-consistent total trail it reports each parent's class root and the
  asserted atom indices explaining equality to the class's first observed term.
- Group base-array read sites by those final class roots rather than by original
  symbol. Within a class, materialize only pairs whose candidate indices are
  equal and whose candidate results differ. Ground-distinct indices remain
  pruned.
- Same-parent select congruence remains unconditional. For distinct parents,
  union the two explanation paths and materialize

  ```text
  explanation_equalities and index_equality -> result_equality
  ```

  The guard terms are existing aligned theory atoms, so the next canonical round
  gives the exact BV component their abstract interpretation and `EufTheory`
  their original equalities.
- Keep materialized guarded lemmas across later canonical rounds. A different
  Boolean branch can falsify their explanation guard, so branch-local class
  membership never becomes an unconditional array equality.
- Stop preparing query-index observations for equalities whose operands are both
  direct array symbols. Retain one diff witness per equality. Equalities involving
  `store`, array-valued `ite`, or another structural term retain the existing
  query/store-index observations until structural parent/ROW/default scheduling
  is implemented.
- Charge each materialized pair to the existing interface, round, theory-atom,
  Boolean-CNF, and deadline bounds. SAT still requires function projection,
  class-owned direct-symbol array projection, and original-query replay.

This is an outer-round parent-select hook, not yet a backtrackable array-theory
queue inside `CdclT`.

## Soundness Argument

For one syntactic array parent, equal indices imply equal select results by
function congruence. For distinct parents, the e-graph explanation is a
conjunction of asserted equality atoms that entails equality of those parents;
adding index equality therefore entails result equality. The emitted implication
is valid on every Boolean branch. If a later branch retracts any merge premise,
the guard is false and the retained lemma imposes no cross-parent result equality.

Every canonical round remains a relaxation of full array semantics. The new
lemmas add only valid select-congruence instances, so partial-round UNSAT
transfers. Removing eager direct-symbol query observations does not admit a wrong
SAT: candidate-violated reads in a true e-class are scheduled, directly equal
symbols share one projected model, false equalities retain a diff witness, and
evaluation of every original assertion remains the final SAT gate. Unsupported
structural ownership or exhausted bounds still returns `Unknown`.

## Evidence

- `a = b` with unequal reads at one concrete index refutes in two rounds through
  exactly one parent-select pair and zero array-equality observations.
- `a = b`, `b = c`, and unequal endpoint reads refutes through one direct
  class-parent pair, again with zero direct-symbol extensionality instances.
- A UF-bearing index case first materializes the function interface, then the
  parent-select pair; it refutes in three rounds without an equality observation.
- A satisfiable `(a = b or a = c)` branch test first schedules cross-parent
  lemmas, then backtracks to `a = c`; explanation guards let the alternate model
  replay. A separate unsatisfiable gate reschedules one read pair under two
  disjoint equality paths. Together they reject unguarded and pair-only queue
  deduplication.
- An 80-array equality chain with 80 distinct query indices returns replayed SAT
  in one round. The former direct-symbol equality-by-index preparation would need
  more than the 4,096 ROW-site cap; the new preparation needs only query reads
  plus per-equality diff reads.
- Structural store equality still exercises both an extensionality observation
  and ROW, pinning the deliberately retained fallback.
- All 794 solver library tests pass. The 20-shape, 256-seed AUFBV matrix performs
  768 online/eager, front-door/eager, and online/Z3 comparisons with zero
  disagreement; 456 comparisons remain equality-bearing.
- Single-run public 1 s measurements preserve decisions and replay:

| corpus | files | decided | disagreements | replay failures | PAR-2 mean |
|---|---:|---:|---:|---:|---:|
| QF_ABV | 193 | 187 | 0 | 0 | 84 ms |
| QF_AUFBV | 53 | 49 | 0 | 0 | 206 ms |

This is an architecture and preparation-scaling increment, not a broad
performance claim.

## Alternatives

- **Persist unguarded cross-parent congruence.** Rejected as unsound across
  Boolean backtracking; equality on one candidate does not hold on every branch.
- **Keep the direct-symbol equality-by-index observations.** Sound, but retains
  the eager cross product after the live e-graph already knows class relevance.
- **Insert dynamic atoms and axioms inside `CdclT` now.** This is the destination,
  but requires a general incremental skeleton/lemma API and a trailed array queue.
  The bounded outer-round contract remains useful while that infrastructure is
  absent.
- **Remove structural observations too.** Rejected for this slice: when
  `store(a, i, v) = b` and only `select(b, j)` exists, the array theory must create
  and schedule the missing structural read/ROW instance. Base-symbol parent pairs
  alone cannot do that.

## Consequences

- Direct base-symbol reads follow candidate e-class merges instead of an eager
  equality-by-query-index product.
- Every cross-parent queue item carries a reusable equality explanation suitable
  for later proof logging.
- T2.2.1 remains WIP: store/ITE/array-valued-UF parent ownership,
  default/ROW scheduling, dynamic in-search insertion, and warm queue reuse remain.
- Non-symbol class models and ROW/diff-witness/equality-chain proof artifacts
  remain separate follow-ups.
