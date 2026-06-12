# axeyum-query

First-class query objects for Axeyum: assertions, assumptions, scopes, and
stable labels over terms owned by `axeyum-ir`.

Phase 3 starts assumptions-first. One-shot solver backends enforce assumptions
as ordinary assertions; future incremental backends can map the same query
object to native assumptions without changing query semantics.

The crate also owns the first query-planning contracts:

- structural cache keys over term structure, symbol names/sorts, constants, and
  operators, independent of arena-local `TermId` allocation and labels;
- target-support slicing that may submit fewer constraints to a solver;
- identity projection plus replay against every original assertion and
  assumption before accepting any sliced `sat` model.
