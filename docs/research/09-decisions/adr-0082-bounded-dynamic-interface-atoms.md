# ADR-0082: Bounded Dynamic Interface Atoms in Canonical Search

Status: accepted
Date: 2026-07-10

## Context

ADR-0081 proved that a candidate final check can add permanent ROW clauses and
resume one `CdclT` search when every possible atom was reserved before search.
The remaining UFBV/AUFBV refinements were pair-dependent: a candidate can expose
a previously irrelevant pair of function applications, parent selects, or
array-equality observations. Reserving every possible equality recreates the
quadratic products removed by ADR-0070/0071/0078, while rebuilding an outer
round discards learned clauses, phases, activities, and the warm BV state.

The key representation obstacle is that an appended theory atom need not have
the same numeric index as its SAT variable. The initial theory atoms precede
Tseitin auxiliaries, but a later atom must be appended after all existing SAT
variables without renumbering the live clause database.

## Decision

Permit bounded dynamic equality atoms over terms observed by the e-graph before
search, and insert every candidate-violated UFBV/AUFBV interface refinement into
the current canonical search.

- `CdclT` owns explicit SAT-variable-to-theory-atom and
  theory-atom-to-SAT-variable maps. Initial atoms retain identity mapping;
  `add_theory_variable` appends a dormant SAT variable after any Tseitin
  auxiliaries and appends the corresponding theory atom without renumbering
  existing state.
- `EufTheory` may append an equality atom only when both sides were pre-observed.
  Registration adds no e-nodes, so the atom survives decision-level backtracking;
  assignments, merges, disequalities, and explanations remain normally trailed.
- The exact BV component owns a clone of the term arena. It can intern the
  abstract equality and negation, extend its atom-aligned assignment and
  propagation vectors, and retain the same persistent incremental BV solver.
- The combined theory registers an equality in EUF, exact BV, and `CdclT` as one
  aligned transaction, deduplicating existing abstract equalities.
- Violated same-function pairs activate argument/result equality atoms; EUF
  congruence supplies the semantic implication. Violated parent-select pairs add
  the guarded clause `not(guards) or not(index_eq) or result_eq`. Violated
  equality observations add `not(flag) or read_eq` or `flag or not(read_eq)`,
  with constant folding. Existing local ROW clauses use the same retained search.
- Candidate batches are checked against the shared 512-interface cap before
  materialization. Theory-atom, Boolean-variable, Boolean-clause, final-check,
  and deadline bounds remain explicit and return `Unknown` on exhaustion.

This decision generalizes ADR-0081's retained-search mechanism. It does not add
new e-graph terms during open scopes, implement array-valued ITE/default/UF
events, provide warm incremental array ownership, or produce online theory
proofs.

## Soundness Argument

The SAT/theory maps are a representation change: every theory assignment,
propagation, reason, and conflict is translated through the same bijection.
Appending a dormant variable cannot affect the current search until a valid
refinement activates it, and no existing variable or clause index changes.

Dynamic EUF atoms refer only to existing e-nodes. Their registration is
persistent metadata, while all assignment effects remain under the established
push/pop trail. Dynamic BV atoms denote exact Bool/BV equalities in the
theory-owned arena. Function pairs rely on ordinary congruence; select and array-
equality clauses are valid instances of select congruence or extensionality
observations, including the e-graph explanation guards required for retractable
parent merges.

Every partial interface set remains a relaxation, so a derived UNSAT transfers
to the original query. SAT is accepted only after function and array model
projection and evaluator replay of every original assertion. Any cap,
registration mismatch, deadline, or replay failure returns `Unknown`.

## Evidence

- A generic `CdclT` test appends a theory atom after a Boolean auxiliary and
  proves that conflict and reason translation use the explicit map.
- An `EufTheory` test registers an equality while a decision scope is open,
  backtracks its assignment, and reuses the persistent atom.
- Canonical mechanism gates pin one outer round for a function pair, a nested
  two-pair UF fixpoint, base and structural parent-select pairs, mixed
  array-then-UF refinement, and array equality/extensionality composed with ROW.
- Branch/replay tests prove retained clauses and atoms backtrack to replayable
  alternatives. Scale gates prove no query-index or application cross product is
  prepared. Over-cap batches return `ResourceLimit` without partial shared-
  interface materialization.
- An eight-shape, 128-seed matrix adds 384 comparisons: online and front door
  against the eager pure-Rust route, plus online against Z3. It covers strict UF
  congruence, nested UF, base selects, guarded parent branches, congruent stores,
  equality plus ROW, mixed array-to-UF fixpoints, and replayable UF branches.
  The complete array belt is now 2,304 clean comparisons and every SAT model
  replays.
- All 809 solver library tests and the 11-test AUFBV differential binary pass.
  Strict Clippy is clean, and commit `39cc92ce` passes the exact-SHA pre-push
  compile/format/corpus/unit gate.

## Alternatives

- **Reserve every pair equality before search.** Rejected because it restores
  the quadratic interface construction and cap failures removed by replay-guided
  refinement.
- **Continue rebuilding outer rounds.** Rejected as the normal path because it
  discards useful search and warm-theory state after every candidate.
- **Assume SAT variable equals theory atom index.** Rejected because appended
  atoms necessarily follow existing Tseitin variables.
- **Add arbitrary e-graph terms during an open scope.** Deferred. The current
  e-graph undo log would remove such nodes on pop; pre-observation gives a small,
  explicit invariant instead of weakening backtracking.

## Consequences

Function, parent-select, and bounded array-equality refinements now share ROW's
same-search path. The canonical mechanism tests that previously required two or
three outer rounds complete in one while retaining learned clauses, phases,
activities, e-graph state, and exact BV state.

The next array-engine work is event breadth and ownership rather than dynamic
scalar equality plumbing: array-valued ITE/default/UF and merge-triggered ROW
events, non-symbol and warm class models, nested/extended arrays, online proof
logging, and a comparable low-load public aggregate remeasurement.

## Update (2026-07-10)

ADR-0084 closes the array-valued UF-result event without open-scope term growth:
application parents are observed before search and their fresh result arrays are
projection owners. Structural ITE/default and merge-triggered new-term events
remain.
