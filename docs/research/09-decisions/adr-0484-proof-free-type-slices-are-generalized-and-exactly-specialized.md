# ADR-0484: Proof-free type slices are generalized and exactly specialized

Status: accepted
Date: 2026-08-19
Index-summary: Replace proof-bearing implementation closure with explicit non-Prop parameters in a fresh kernel, then require checked specialization to the exact source proposition

## Context

ADR-0480 correctly rejects a statement stream containing any theorem, axiom,
opaque declaration, or quotient primitive. The first sealed coverage census
therefore rejects 114 of 138 train/development statements before a producer can
run. Those are adapter outcomes, not mathematical failures.

The follow-up type-boundary census measures both closures for every unsealed
target. All 114 rejected rows have zero trusted declarations in the syntactic
closure obtained by following the target proposition and then only the declared
types of referenced constants. Trusted declarations appear only after following
implementation bodies. Across all 138 rows, the full implementation closure has
67,099 declaration occurrences while the type boundary has 1,806.

Simply deleting bodies is not a semantic operation. A global constant without
a declaration is ill-typed; installing an axiom exposes an assumption; and
proving a generalized proposition does not by itself establish the exact frozen
fact. The representation and the specialization obligation must therefore be
decided before importer authority widens.

This closes the corresponding question in the
[research register](../08-planning/research-questions.md) and refines, rather
than weakens, ADR-0480.

## Decision

A proof-free type slice is a pair:

1. a proposition generalized over explicit, typed parameters in a fresh kernel;
2. a checked specialization receipt showing that applying those parameters to
   exact source constants yields the original source proposition.

The operation is versioned and fail-closed under the following rules.

### Source and identity

- The receipt binds the entire source-stream digest, official Lean and exporter
  identities, exact target declaration identity, original goal identity, slice
  policy version, and sliced goal identity.
- Each abstracted occurrence class is keyed by declaration content identity and
  canonical universe arguments, not rendered name alone. Its instantiated type
  identity, binder position, and source occurrence count are bound.
- Equal keys share one parameter; distinct universe instances do not.

### Retention and abstraction

- The target proposition is traversed first. Required declaration types are
  traversed transitively in dependency order.
- A declaration may be retained in the producer kernel only when its complete
  retained implementation closure is independently admitted and contains no
  axiom, theorem, opaque declaration, or quotient primitive.
- A constant whose declaration cannot be retained across that trust boundary
  may instead become an explicit `Pi` parameter. Its exact instantiated type is
  recursively sliced before the binder is constructed.
- If that instantiated type itself inhabits `Prop`, the slice is rejected. A
  proof or proposition-valued assumption never becomes a parameter by relabeling.
- V1 rejects quotient participation, abstracted projection type names,
  dependency cycles, unsupported universe constraints, and any missing
  transparent reduction needed by type inference or definitional equality.
  Later support requires a new measured policy; it is never inferred from this
  decision.

### Fresh-kernel boundary

- The broad imported source kernel is validation input only. The producer sees
  a newly constructed kernel containing exactly the retained proof-free
  declarations and the generalized goal.
- Arena handles are never transplanted. Names, levels, expressions, and
  declarations are reconstructed with an explicit old-to-new identity map and
  checked through ordinary admission gates.
- The sliced goal must independently infer to `Prop`, be closed, and have an
  empty trusted-declaration closure before a producer runs.

### Exact specialization

- A generalized proof receives no exact-fact credit until a checker rebuilds it
  in the source-validation kernel, applies the bound source constants in binder
  order, and independently checks the result against the original goal.
- The specialized result must be definitionally equal to the exact source
  proposition identity already frozen by ADR-0480. Surface-text similarity is
  insufficient.
- A producer must return a replayable construction plan or canonical term
  representation; `ExprId` equality across kernels is meaningless. The first
  bounded reflexivity operation may use its existing deterministic plan, but
  this does not grant generic producer authority.
- Evidence reports both the generalized proof's ordinary full dependency
  closure and the specialization arguments. Concrete source definitions are
  classified as explicit instantiations, never silently removed from the
  report.

The held-out partition remains sealed until this policy, budgets, and at least
one useful train/development operation are frozen and reproduced.

## Evidence

The immutable diagnostic bound by
[`mathlib-type-slice-feasibility-v1.json`](../../../artifacts/autogenesis/mathlib-type-slice-feasibility-v1.json)
analyzes all 138 train/development streams and no held-out row. It finds:

- 114 implementation closures containing trusted declarations;
- 138 type closures containing no trusted declaration;
- all 114 prior strict-adapter rejections inside that clean type-boundary set;
- type-boundary sizes from 2 to 80 declarations, median 8; and
- 962 definition occurrences at candidate abstraction boundaries.

Nine executable controls cover unrelated theorems, theorem use only through a
helper body, a direct theorem reference that remains rejecting, malformed
expression topology, duplicate targets, held-out mutation, coverage mutation,
and inner-artifact identity mutation. The analyzer explicitly grants no proof
or ledger credit and does not claim proposition-valued-type checking.

## Alternatives

- **Delete theorem records from the export.** Rejected because retained
  definition bodies would become ill-typed, and deletion supplies no semantic
  account of the missing constant.
- **Install body-free constants as axioms or opaque declarations.** Rejected
  because it widens the producer environment with trusted declarations and
  makes assumption auditing depend on a label rather than a binder.
- **Run the producer in the broad checked source environment and audit only its
  final term.** Rejected because an untrusted producer could inspect unrelated
  answers; ADR-0480's environmental isolation remains load-bearing.
- **Credit the generalized theorem directly to the concrete ledger fact.**
  Rejected because the theorem is stronger but not identical. Exact
  specialization is a separately checked obligation.
- **Copy every type-reachable definition body.** Rejected because this recreates
  the measured 114-row contamination and defeats the slice.
- **Abstract every global, including inductives and quotient primitives.**
  Rejected for V1 because projections, recursor computation, and quotient
  reduction carry semantic structure that a function parameter does not
  reproduce automatically.

## Consequences

- The next implementation boundary is concrete: canonical cross-kernel cloning,
  typed parameter abstraction, and a specialization checker—not broader proof
  search.
- A successful slice may decline when computation is required. Such a decline
  is an honest capability signal for selective transparent retention.
- Receipts become larger because they bind source constants and universe
  instances, but they remain small compared with external Mathlib streams and
  stay suitable for Git.
- The generalized proof can be independently stronger than the source fact;
  exact-fact authority still depends on the specialization check.
- ADR-0480 remains the default strict adapter. This ADR adds an explicit second
  route; it does not relax the original route or reinterpret its historical
  evidence.
