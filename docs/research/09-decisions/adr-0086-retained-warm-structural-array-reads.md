# ADR-0086: Retained Warm Structural Array Reads

Status: proposed
Date: 2026-07-10

## Context

ADR-0030 requires incremental symbolic-memory queries to keep array reasoning
warm instead of rerunning eager elimination on every check. The current
`IncrementalBvSolver` has two partial routes:

- a syntactic simplifier expands an observed
  `select(store(a, i, v), j)` into a scalar ITE before warm BV lowering; and
- direct `select(a, i)` reads over supported array symbols receive retained
  scalar owners, same-array congruence lemmas, and replay-projected leaf models.

The first route decides useful memory shapes but rebuilds the structural ROW
expansion for each assertion or one-shot branch query. The second retains CNF
and learned clauses, but only after every structural array parent has already
been eliminated. Consequently it does not establish the deferred half of
ADR-0030: array semantics themselves are not retained as warm definitions.

The canonical one-shot AUFBV engine now has exact structural array semantics
(ADR-0085), but embedding that whole search object inside the incremental BV
solver would duplicate selector, lowering, and SAT ownership. The next warm
increment should instead extend the existing retained abstraction in place.

## Decision

`IncrementalBvSolver` will retain observed structural reads over finite-scalar
array parents. The admitted array components remain BV indices and Bool/BV
elements. For a fresh internal scalar owner `r_t` of read term `t`, install the
following exact definitions in the persistent warm CNF:

```text
r_select(const(v), j)       = v
r_select(store(a,i,v), j)   = ite(i = j, v, r_select(a,j))
r_select(ite(c,a,b), j)     = ite(c, r_select(a,j), r_select(b,j))
```

Definitions recursively abstract generated base/branch reads and scalar UF
applications through the existing warm machinery. Exact same-index and
literal-distinct ROW simplifications may still fold before abstraction, but an
undecided structural read is no longer expanded into a throwaway scalar tree.

These definitions are permanent rather than frame-scoped. That is sound because
each relates a private internal owner to the denotation of its source term and
does not assert the source term itself. It is the same role as a persistent
Tseitin definition. User roots remain guarded by their frame or one-shot
assumption selector. Congruence between distinct array symbols that depends on a
scoped asserted array equality also remains selector-scoped.

Direct symbol-parent reads remain the only model-projection owners. Structural
reads have no independent array slot: stores, constant arrays, and array ITEs
derive their values from children. The permanent definitions constrain their
internal scalar values, leaf reads populate concrete array models, function
tables are projected as before, and every SAT result replays every original
active assertion and one-shot assumption.

The retained slice is bounded deterministically:

- at most 512 unique structural array nodes/read sites per admitted root; and
- at most 256 structural parent edges from a read to a leaf.

An over-limit or unsupported parent is not partially encoded. A committed root
stays deferred for `check_with_memory`; branch preflight selects the existing
one-shot dispatcher. No wrong SAT/UNSAT follows from an incomplete definition.

Array-valued UF parents, array disequality witnesses, general structural array
equality, non-BV indices, non-Bool/BV elements, and candidate-triggered rather
than observation-triggered warm axioms remain outside this increment. The
canonical one-shot path continues to decide those supported shapes.

## Soundness Argument

Each permanent definition is an SMT-LIB array identity. Constant-array read and
array-ITE read are direct evaluation equations; store read is total ROW. Fresh
owners are private and occur only in definitions, encoded roots, and valid
congruence lemmas, so installing a definition before or after a scope cannot
constrain any user-visible value beyond the source term's semantics.

UNSAT therefore follows from the active user roots plus exact definitional
extensions and valid congruence. SAT still requires leaf-array/function model
projection and evaluation of the original, unabstracted assertions. A missing
leaf value, conflicting projection, unsupported dependency, or replay failure
degrades to `Unknown` or an explicit unsupported/deferred route, never an
accepted model.

## Required Validation Before Acceptance

- Warm SAT replay and UNSAT for symbolic hit/miss reads over store, constant,
  and array-ITE parents, including a symbolic base array.
- Nested store/ITE reads and Bool-element arrays.
- Push/pop showing a scoped structural root retracts while its harmless private
  definitions may remain.
- Repeated checks and opposite one-shot branch assumptions showing structural
  definitions and CNF variables are reused rather than reinstalled.
- Exact 512-node and 256-depth admission boundaries with one-over controls
  routed to deferred/dispatcher handling.
- Deterministic differential cases against `check_auto`, plus Z3 under the
  native feature; every warm SAT model replays the original terms.
- The EVM warm-array storage-depth measurement rerun, reported honestly even if
  the retained route does not yet beat frontend ITE folding.
- Full solver units, EVM warm-array/fuzz gates, strict clippy, rustdoc, links,
  and the exact-SHA pre-push gate.

## Alternatives Considered

### Cache the old expanded scalar ITE only

Rejected as the architectural increment. It can reduce traversal overhead but
still erases array semantics before the warm engine and does not advance the
deferred half of ADR-0030.

### Embed a second canonical `CdclT` session inside `IncrementalBvSolver`

Deferred. It duplicates SAT/selector ownership and requires a larger contract
for scoped e-graph atoms, model reuse, and proof state. Retained exact
definitions use the already-persistent incremental CNF and are sufficient for
the observed symbolic-memory slice.

### Make structural definitions selector-scoped

Rejected. The definitions are valid independently of any user root, and
re-guarding them on every branch recreates the work this increment is intended
to retain. Equality-dependent cross-array consequences remain scoped because
their validity does depend on an active user assertion.
