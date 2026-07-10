# ADR-0081: Dynamic In-Search ROW Insertion

Status: accepted
Date: 2026-07-10

## Context

ADR-0072 made read-over-write candidate-guided, but each violated store site
still ended the current canonical search. The next outer round rebuilt the
Boolean skeleton, `EufTheory`, exact BV adapter, and `CdclT`, discarding learned
clauses, phase state, and variable activities even though one store site needs
only three local atoms and two fixed ROW clauses.

This is narrower than general array-theory growth. Function congruence,
cross-parent select congruence, and extensionality can discover pair-dependent
atoms whose number is not bounded per syntax site. A store read's local
same-index, hit-result, and miss-result atoms are known before search and are
bounded by the existing ROW-site and interface limits.

## Decision

Reserve each store site's three local ROW atoms before canonical search, keep
newly reserved Boolean variables dormant, and activate them only when a SAT
candidate violates that site's read-over-write semantics.

- `CdclT` tracks an active-variable mask. Dormant variables are not branch
  candidates and theory propagation cannot assign them.
- Existing semantic/interface atoms reused by a ROW site remain active. Only
  atom variables created solely for the reservation are dormant.
- `CdclT::add_permanent_clause` activates every variable named by the clause,
  appends a non-reducible permanent constraint, and preserves the current
  trail, learned clauses, phase state, and variable activities. The next
  `solve` resumes that search and backtracks if the retained assignment violates
  the new clause.
- A violated store site inserts the two valid ROW clauses
  `not(same_index) or hit` and `same_index or miss`, with exact constant folding.
  The site is then marked materialized and the same `CdclT` instance resumes.
- The existing shared interface cap remains exact: materializing one site is
  charged three interface atoms. Deadline, theory-atom, Boolean-variable, and
  clause bounds still degrade to `Unknown`.
- Pair-generating UF, parent-select, and extensionality refinements continue to
  rebuild bounded outer canonical rounds. This ADR does not claim arbitrary
  dynamic atom insertion or a complete Z3-style array event queue.

## Soundness Argument

The reserved variables have no semantic effect while dormant: they occur in no
initial clause, are not selected for decisions, and cannot receive theory
propagation. Activating them only through a permanent ROW clause adds a theorem
of array semantics. Both clauses are the standard case split for
`select(store(a, i, v), j)`: equal indices force the stored value, while unequal
indices force the inner read.

Adding a valid clause to the live clause database preserves every learned
clause. If the retained total assignment falsifies the new clause, ordinary
propagation/conflict analysis backtracks before another result is returned.
Round-level UNSAT therefore still transfers to the original query. SAT remains
accepted only after function projection, array projection, and evaluation of
every original assertion. Exhausted bounds or failed replay return `Unknown`.

## Evidence

- Generic driver tests show that a reserved variable is ignored by branching
  and theory propagation until activation, and that permanent clauses can
  resume from SAT and resolve a later conflict by selecting a different branch
  without rebuilding the driver. A contradictory dormant theory propagation
  becomes UNSAT only after the variable is activated.
- The existing ROW hit and miss conflicts move from two canonical rounds to
  one. Two nested violated store reads also close in one outer round through two
  in-search refinements.
- A satisfiable equality-branch case inserts ROW, backtracks, and returns a
  replaying model. A UF-bearing index hit closes in one round without a separate
  outer function-pair refinement because the activated equality is already
  aligned with `EufTheory`.
- The shared 512-interface boundary is pinned under dynamic insertion; the
  over-cap control returns resource `Unknown` rather than partially activating
  a site.
- An eight-shape, 128-seed matrix adds 384 comparisons: online and front door
  against the eager pure-Rust route, plus online against Z3. It covers hit,
  miss, replayable branch, nested miss, no-op miss, UF index, shadowed store,
  and equality-branch backtracking. Together with the previous 1,536 array
  comparisons, all 1,920 are clean and every SAT model replays.
- All 807 solver library tests, the nine-test AUFBV differential integration
  binary, strict clippy, and rustdoc with warnings denied pass. The exact pushed
  SHA passes the repository pre-push compile/format/corpus/unit gate.
- No new public 1-second aggregate is committed because the host remains under
  unrelated I/O load. ADR-0078's comparable QF_ABV 187/193 and QF_AUFBV 49/53
  baseline remains authoritative pending a low-load run.

## Alternatives

- **Continue rebuilding after every violated ROW site.** Rejected because it
  discards search state for two clauses over three atoms whose complete local
  vocabulary is known before search.
- **Insert entirely new atoms into a live theory dynamically.** Deferred. It is
  needed for pair-generating parent/UF/extensionality events, but requires
  coordinated growth of the Boolean skeleton, e-graph roots, BV adapter, and
  proof logs. Bounded reservation proves the state-retention mechanism first.
- **Activate every reserved ROW atom at search start.** Rejected because dormant
  sites should not create branch choices or theory traffic before a candidate
  demonstrates relevance.
- **Restore eager ROW preprocessing.** Rejected because it recreates the store-
  chain expansion that ADR-0072 removed.

## Consequences

Candidate-guided ROW is now a true same-search final-check refinement. Multiple
local store obligations can reuse one canonical `CdclT` instance and its learned
state, and the solver reports the count separately as in-search ROW
refinements.

The reservation costs at most three atom slots per admitted store site and stays
under the existing explicit caps. Outer rounds remain for pair-generated UF,
parent-select, and extensionality atoms. Array-valued ITE/default/UF events,
merge-triggered parent/select scheduling, non-symbol and warm model ownership,
and ROW/diff-witness/equality-chain/online proof logging remain P2.2/P3.5 work.
