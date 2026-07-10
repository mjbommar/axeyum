# ADR-0073: Candidate-Guided Array Extensionality on the Canonical Bus

Status: accepted
Date: 2026-07-09

## Context

ADR-0072 made read-over-write lazy on canonical QF_ABV/QF_AUFBV, but array
equality still made that route decline. The fallback lazy-extensionality solver
already had the required sound semantics: replace each array equality by a
Boolean flag, constrain true flags at observed indices, give false flags a diff
witness, reconstruct arrays, and replay the original formula. Reimplementing
those rules in `ufbv_online` would create a second extensionality definition.

The next P2.2 step therefore needs to reuse `RowCtx::abstract_with_array_eq`
while preserving the canonical route's relaxation-UNSAT and replay-SAT trust
boundary. It must also remain bounded: crossing every equality with every diff
index would recreate a quadratic construction before search.

## Decision

Admit BV-indexed/BV-valued array equality atoms on canonical ABV/AUFBV by
preparing bounded observations through the shared ROW/extensionality abstraction
and materializing only candidate-violated equality or diff implications.

- `abstract_rows_for_online` now calls the existing
  `RowCtx::abstract_with_array_eq`. Each `a = b` atom becomes one internal Bool
  flag, exactly as in the one-shot lazy-extensionality route.
- Each equality receives one internal diff index and paired reads of `a` and `b`
  there. It also observes query-read and finite store indices already relevant to
  that equality. Diff indices are not crossed between equality atoms.
- All observation indices/read terms become auxiliary function-abstraction roots.
  UF applications occurring only in an observed index therefore retain aligned
  application metadata and share the canonical EUF/BV bus.
- A true flag with unequal observed reads materializes
  `flag -> select(a,i) = select(b,i)`. A false flag whose own diff reads are equal
  materializes `!flag -> select(a,diff) != select(b,diff)`.
- Each materialized extensionality instance contributes one scalar equality to
  the shared 512-interface cap. The existing 64-round, 1,024-theory-atom,
  4,096-ROW-site, 256-diff-witness, Boolean, node, depth, and deadline caps apply.
- Partial-round UNSAT transfers because omitted extensionality, ROW, select, and
  UF instances leave a relaxation. SAT still requires function projection,
  base-array reconstruction, and replay of every original assertion.
- Array online probes run on a cloned arena at both front-door dispatch points.
  Original symbol/function IDs are stable across the clone, so decided models
  remain valid, while an online `Unknown` cannot pollute or enlarge the fallback
  arena.
- Internal equality flags, diff indices, ROW reads, and function-application
  symbols are excluded from the returned model. Existing eager and certifying
  routes remain unchanged.

## Soundness Argument

Replacing an array equality by an unconstrained flag is a relaxation. Every
materialized true-direction observation is an instance of array congruence, and
every false-direction instance is the standard extensional diff-witness axiom.
Adding any subset of those valid consequences preserves the fact that a partial
round's UNSAT implies original-query UNSAT.

A converged SAT candidate has no violated prepared observation. Its scalar and
function values reconstruct base arrays, including the own-diff entries needed
by false equality flags. The ground evaluator then checks the original array
equalities and all surrounding Boolean structure. Missing values, an unsupported
array base, an unobserved cross-atom dependency, a cap/deadline, projection
failure, or replay failure yields/falls through as Unknown rather than SAT.

## Evidence

- Focused canonical gates cover: true equality plus unequal observed reads
  (one axiom, two rounds, UNSAT); self-disequality (one diff axiom, two rounds,
  UNSAT); satisfiable disequality with projected/replayed arrays; store equality
  requiring both extensionality and ROW; and a UF-bearing observed-index
  disjunction requiring function, select, and equality refinement.
- Two dispatch gates prove pure ABV and mixed AUFBV online probes leave the
  caller arena unchanged while returned models replay on that original arena.
- The canonical online module passes 30 focused tests.
- The deterministic AUFBV matrix still performs 256 direct-online/eager,
  256 front-door/eager, and 256 direct-online/Z3 comparisons. Half of each
  matrix now carries array equality/disequality, store equality, Boolean
  equality polarity, or UF-indexed cross-array reads: 384 equality-bearing
  comparisons, 768 total, no Unknown direct verdicts or disagreements.
- Single-run public measurements at a 1 s cap preserve coverage and soundness:

| corpus | ADR-0072 decisions | extensionality decisions | disagreements | replay failures | PAR-2 mean |
|---|---:|---:|---:|---:|---:|
| QF_ABV (193) | 187 | 187 | 0 | 0 | 84 ms (was 77 ms) |
| QF_AUFBV (53) | 49 | 49 | 0 | 0 | 221 ms (was 155 ms) |

These are coverage/safety measurements, not a performance gain. QF_AUFBV still
contains a separate fallback deadline-overrun row; clone isolation prevents
online-arena pollution but does not repair that downstream deadline hole.

## Alternatives

- **Keep all equality on the one-shot fallback.** Rejected because canonical
  array/UF/BV interaction and learned conflicts would remain equality-blind.
- **Copy extensionality into `ufbv_online`.** Rejected because two semantic
  implementations would be a long-term soundness risk.
- **Cross every equality with every diff witness.** Rejected because it is
  quadratic before search. Cross-atom observations require the future
  merge-triggered queue.
- **Create observations dynamically after each candidate.** Deferred. New read
  sites can contain UF-bearing terms and must be registered consistently with
  function abstraction and model projection; the bounded pre-observation slice
  establishes semantics first.
- **Accept a candidate once prepared observations agree.** Rejected. Prepared
  observations are incomplete; original-query replay remains mandatory.
- **Replace eager/certifying routes.** Rejected. This increment adds no proof
  artifact and does not alter evidence precedence.

## Consequences

- Canonical QF_ABV/QF_AUFBV now admits array equality, disequality, store
  equality, Boolean equality polarity, and UF-bearing observed indices in the
  bounded variable/store/const/ite array fragment.
- Equality flags, select congruence, lazy ROW, UF congruence, and exact BV refine
  in one deterministic outer loop with replayed models.
- T2.2.3 is complete only for this candidate-guided observed-index/diff slice.
  Full phase exit still requires merge-triggered new/delayed/applied queue state,
  cross-atom observation scheduling, scalable majority-default models, warm
  reuse, and proof/evidence integration.
