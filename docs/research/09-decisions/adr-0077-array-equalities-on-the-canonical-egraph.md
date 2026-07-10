# ADR-0077: Array Equalities on the Canonical E-Graph

Status: accepted
Date: 2026-07-10

## Context

ADR-0073 replaces each array equality with a fresh Boolean flag and adds bounded
observed-index/diff-witness semantics on demand. ADR-0076 noticed that those flags
were opaque to `EufTheory`: a candidate could assign `a = b`, `b = c`, and
`a != c` without the canonical e-graph seeing an equality conflict. Its first
repair carried the false atom's diff index across one candidate-true path.

That queue was sound, but it repaired equality transitivity through array
extensionality. Equality transitivity and congruence already belong to the
backtrackable e-graph. The indirect route also needed dynamic ROW sites, a second
fresh-symbol counter, queue state, a 512-observation cap, and multiple rebuilt
canonical rounds for a conflict that EUF can close immediately.

SAT model projection had the dual ownership gap. Each base-array symbol chose its
majority default independently. A true transitive class with disjoint observations
could therefore produce individually valid finite maps that were not extensionally
equal, leaving original replay to decline an otherwise satisfiable candidate.

## Decision

Put canonical array equality on the existing equality bus and give direct symbol
classes one projected model.

- Keep the fresh Boolean flag as the exact BV/Boolean skeleton atom, but register
  the corresponding original `lhs = rhs` array term at the same atom index for
  `EufTheory`.
- A true flag now merges its array operands in the live backtrackable e-graph. A
  false flag records their disequality. E-graph explanations therefore handle
  reflexivity, transitivity, and congruence through the ordinary `TheorySolver`
  push/pop trail.
- Remove ADR-0076's cross-diff path queue, dynamic observation builder, retained
  diff-index metadata, and secondary fresh-symbol counter. Local observed-index
  and per-atom diff-witness refinement remain unchanged for the genuinely
  array-specific extensionality directions.
- Before SAT replay, union every candidate-true equality whose two operands are
  direct array symbols. Combine the observed entries of each class, reject a
  conflicting duplicate index conservatively, choose one deterministic
  majority-default finite map, and assign that value to every class member.
- Keep non-symbol array equalities (`store`, `ite`, and future array-valued
  applications) on the e-graph for conflicts, but do not claim class-owned model
  reconstruction for them yet. Replay remains the final authority.
- Retain all existing theory-atom, interface, ROW-site, round, Boolean-CNF, and
  deadline limits. The removed cross-observation limit is no longer relevant to
  plain equality transitivity.

ADR-0077 supersedes ADR-0076's implementation choice. ADR-0076 remains the
historical evidence that exposed the missing equality-bus connection; its
eager-cross-product rejection still stands.

## Soundness Argument

An array equality is an ordinary equality atom in the array theory. Interpreting
its Boolean flag as the original equality in EUF adds only consequences valid in
every array model: reflexivity, symmetry, transitivity, and congruence. EUF does
not infer array extensionality in the reverse direction. False array equalities
still receive their per-atom diff witness, and true equalities still receive
observed-read implications when array-specific semantics are needed.

Every e-graph conflict is explained by asserted atom indices and uses the same
explanation machinery exercised by the independent scalar-UF congruence checker.
The exact BV component continues to see the aligned fresh flag, so both theories
consume one SAT trail literal with different sound interpretations.

Class-owned projection changes only unconstrained model completion. All observed
entries in a class must agree at duplicate indices; otherwise the route declines.
One total array value is then copied to every directly equal symbol. Original
query evaluation still gates `Sat`, so unsupported store/ITE class ownership or
a projection mistake degrades to `Unknown` rather than a wrong model.

## Evidence

- The atom-construction gate checks that an abstract array flag's `original` atom
  is the literal array equality while its `abstracted` atom remains the flag.
- `a = b`, `b = c`, `a != c` now returns UNSAT in one canonical round, with no SAT
  candidate and no extensionality instance.
- `a != a` and `store(a, f(x), v) = b`, `b = c`,
  `store(a, f(x), v) != c` also refute in one round without ROW materialization.
- The former 40-array/20-disequality cross-observation cap case now refutes in one
  round instead of returning `ResourceLimit` after 512 observations.
- A SAT `a = b = c` case with a read pinned only on `a` and a different-index read
  pinned only on `c` returns one shared model for all three symbols and replays.
- A Boolean `(a = b or a = c) and a != b` case backtracks away from the
  conflicting equality and projects the surviving `a = c` class.
- The 20-shape, 256-seed matrix still performs 768 direct/eager,
  front-door/eager, and direct/Z3 comparisons with zero disagreement. Its
  transitive SAT shape now carries disjoint class observations; 456 comparisons
  remain equality-bearing.
- All 790 solver library tests pass.
- Single-run public 1 s measurements preserve decisions and replay:

| corpus | files | decided | disagreements | replay failures | PAR-2 mean |
|---|---:|---:|---:|---:|---:|
| QF_ABV | 193 | 187 | 0 | 0 | 84 ms |
| QF_AUFBV | 53 | 49 | 0 | 0 | 205 ms |

This is an architecture and model-completeness correction, not a broad
performance claim.

## Alternatives

- **Keep the cross-diff queue as the primary transitivity mechanism.** Rejected:
  it duplicates the e-graph's job, consumes array observations, and needs rebuilt
  rounds for a pure equality conflict.
- **Merge only projected models.** Rejected as incomplete: it repairs SAT replay
  but cannot justify transitive UNSAT.
- **Prebuild all cross observations.** Rejected by ADR-0076: it restores the
  quadratic product the lazy route was designed to avoid.
- **Build full store/ITE/e-class model ownership now.** Deferred: direct symbol
  classes close the demonstrated replay gap without inventing incomplete inverse
  semantics for store terms. General class-parent model construction remains a
  separate measured slice.

## Consequences

- Array equality now participates in the same live, backtrackable congruence bus
  as scalar UF; plain transitive conflicts no longer consume extensionality work.
- Directly equal array symbols have deterministic class-owned finite-map models,
  including transitive classes with disjoint observations.
- The canonical code loses the dynamic cross-observation path and its associated
  metadata, reducing the state that future warm reuse must preserve.
- Parent-select merge scheduling, class ownership for store/ITE/array-valued UF
  terms, warm solver reuse, ROW/diff-witness proof logging, and portable equality-
  chain Alethe artifacts remain open.
