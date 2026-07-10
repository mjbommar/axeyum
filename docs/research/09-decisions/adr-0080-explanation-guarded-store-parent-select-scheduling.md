# ADR-0080: Explanation-Guarded Store-Parent Select Scheduling

Status: accepted
Date: 2026-07-10

## Context

ADR-0078 schedules reads whose direct-symbol parents share a final live e-class,
but a read through `store(a, i, v)` was visible only as a lazy read-over-write
site. Two syntactically different store terms could become congruent after the
e-graph merged their base arrays, write indices, and values, while their reads
remained in separate array-refinement groups. The canonical relaxation could
therefore miss ordinary select congruence between structural parents until a
fallback or original-query replay declined the candidate.

Z3 records parent selects on array e-classes and propagates select/store axioms
after merges. Axeyum still rebuilds bounded canonical rounds, so this increment
extends the explanation-guarded parent hook without claiming the full dynamic
array-theory queue.

## Decision

Treat every abstracted read's original `store` term as an observable select
parent on the canonical array/e-graph bus.

- `RowKind::Store` retains the original store `TermId` in addition to its write
  index, value, and recursively abstracted inner read.
- Array preparation exposes that store term as an `EufTheory` root. Structural
  congruence can therefore place distinct stores in one final class when their
  arguments are equal.
- A store read participates in the same candidate scan as a base-symbol read.
  Within one final parent class, only equal-index, unequal-result candidates
  materialize a select-congruence implication.
- Reads with the same store parent use an unconditional index-to-result
  implication. Reads with distinct but congruent store parents carry the union
  of their e-graph merge explanations as a guard, exactly as in ADR-0078.
- Keep lazy ROW independent. A store read remains a `CombinedRowStore`, so a
  candidate may schedule select congruence, read-over-write, both, or neither.
- Charge every materialized pair to the existing round, interface-atom, CNF,
  theory-atom, and deadline bounds. SAT still requires function-then-array model
  projection followed by evaluation of every original assertion.

Direct constant-array reads remain folded, and array-valued `ite` reads remain
scalarized into branch reads. Neither receives a structural parent event in this
increment. Array-valued UF parents remain outside the admitted structural
boundary.

## Soundness Argument

`store` is an ordinary e-graph application. If two store terms share an e-class,
the explanation literals entail equality of their base arrays, write indices,
and values through asserted equality and congruence. Equal parent arrays and
equal select indices entail equal select results. Guarding a cross-parent lemma
with that explanation makes the implication valid on every Boolean branch; if a
later round retracts one merge premise, the guard becomes false.

Every partial canonical round remains a relaxation of full array semantics.
The new obligations are valid select-congruence instances, so round-level UNSAT
transfers. A candidate that needs ROW semantics still encounters the independent
ROW scan. A candidate with no new obligation is accepted only if its projected
function and array models replay every original assertion. Resource exhaustion
or unsupported ownership returns `Unknown`.

## Evidence

- Two distinct stores over equal bases, equal write indices, and equal values,
  followed by unequal reads at one shared index, refute in two rounds through
  exactly one explanation-guarded store-parent pair and no extensionality
  observation.
- Two reads from one store parent at candidate-equal indices refute through one
  unconditional pair.
- A satisfiable `(a = b or a = c)` case first schedules a store-parent pair and
  then replays through the alternate branch. An unrelated-store control remains
  satisfiable and materializes no structural pair.
- An 80-array equality chain creates 80 congruent store parents read at 80
  provably distinct indices. It replays SAT in one round with zero select pairs
  and zero ROW axioms; eager pair construction would exceed the 512 interface-
  atom bound.
- The new eight-shape, 128-seed matrix adds 384 comparisons: online and front
  door against the eager pure-Rust route, plus online against Z3. It covers
  distinct/same/unrelated store parents, alternate and transitive array paths,
  UF-bearing write indices, SAT equality, and disequality. Together with the
  previous 1,152 array comparisons, all 1,536 are clean and every SAT model
  replays.
- All 802 solver library tests, the seven-test differential integration binary,
  strict clippy, and rustdoc with warnings denied pass. The exact pushed SHA also
  passes the repository pre-push compile/format/corpus/unit gate.
- A fresh host sample still showed four blocked tasks and 13-25% I/O wait. No
  new 1-second corpus aggregate is committed; ADR-0078's comparable baseline
  remains QF_ABV 187/193 and QF_AUFBV 49/53 with zero disagreement and replay
  failures.

## Alternatives

- **Leave store reads only on the ROW path.** Rejected because ROW constrains one
  store against its inner read; it does not provide select congruence between
  two structural parents that become equal by e-graph congruence.
- **Generate every store-parent read pair up front.** Rejected because it
  recreates the cross product removed by ADR-0078 and spends the interface bound
  before a candidate demonstrates relevance.
- **Make structural pairs unconditional.** Rejected as unsound across Boolean
  branches when distinct stores are equal only under retractable premises.
- **Implement dynamic in-search insertion in the same change.** Deferred. It
  requires a general incremental atom/lemma API and a trailed array event queue;
  the bounded outer-round hook is independently useful and testable.

## Consequences

Canonical ABV/AUFBV now observes direct-symbol and `store` parents through one
explanation-guarded candidate scheduler. Structural store congruence composes
with UF indices and lazy ROW without widening the trusted base or changing model
formats.

T2.2.1 remains WIP. Array-valued `ite`/default/UF events, dynamic in-search
insertion, non-symbol class-owned models, warm queue reuse, and
ROW/diff-witness/equality-chain/online proof logging remain.
