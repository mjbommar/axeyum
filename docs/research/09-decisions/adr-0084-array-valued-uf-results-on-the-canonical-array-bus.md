# ADR-0084: Array-Valued UF Results on the Canonical Array Bus

Status: accepted
Date: 2026-07-10

## Context

The IR and evaluator already carry all semantic machinery needed for a function
to return an array: `Op::Apply` is sort-polymorphic, `Value` represents finite
total arrays, and `FuncValue` switches to full-value storage whenever a parameter
or result is array-sorted. `TermArena::declare_fun` nevertheless rejects array
results because no solver route could project the model.

Canonical AUFBV currently abstracts arrays before functions. `RowCtx` resolves
`select` over stores, array-valued `ite`, symbols, and constant arrays, but
declines `select(f(args), i)`. Simply allowing the declaration or replacing the
application by a fresh array symbol is insufficient:

- the scalar SAT model constrains observed reads, not the fresh array itself;
- function projection needs the fresh array value as an application result;
- array-valued applications with equal arguments must denote one extensional
  array, including observations made through different syntactic applications;
- array arguments to functions need their projected values before function-table
  keys are constructed.

The canonical e-graph already solves the semantic equality problem. It observes
original application terms, merges congruent applications, and supplies guarded
parent-select scheduling for reads whose parents finish in one e-class. The
missing piece is a projection bridge from those semantic parent classes to the
fresh arrays owned by function abstraction.

## Decision

Admit array-valued uninterpreted-function results in the IR and support their
finite Bool/BitVec reads on the canonical AUFBV bus.

- `TermArena::declare_fun` accepts a flat first-class `Sort::Array` result after
  the same component validation used for array symbols. Datatype and sequence
  results remain under their existing separate gates.
- The eager `eliminate_functions` route continues to decline array-valued
  results: replacing an application by an array symbol leaves array equality in
  Ackermann constraints and therefore does not produce its promised scalar
  target. `abstract_functions`, which adds no eager congruence constraints,
  accepts the result sort for canonical combination.
- The online-only ROW abstraction recognizes an array-valued application parent.
  It creates the usual fresh scalar read site and retains the original
  application term as the semantic parent. Generic lazy-ROW callers remain
  unchanged and continue to decline this shape.
- Function abstraction still creates one fresh result-sort symbol per distinct
  application. Canonical preparation associates every application-backed read
  with that fresh array as its projection owner, while the select bus continues
  to observe the original application term on the e-graph. Rewritten index terms
  are retained for projection so no original `Apply` must be evaluated before
  function interpretations exist.
- Array-result applications are excluded from scalar argument/result interface
  refinement. EUF congruence merges equal-argument application parents; guarded
  select congruence enforces equal values at equal observed indices; direct array
  equality/disequality continues through the existing flag, witness, and
  extensionality path.
- At a total candidate, projection groups fresh application arrays and ordinary
  array symbols whose corresponding select parents share a final e-class. It
  unions their observed entries into one deterministic majority-default array,
  then projects function interpretations from that array-complete assignment.
  This array-first/function-second order also supplies accurate full-value keys
  for existing functions that take arrays as arguments.
- An unconstrained application result missing from the scalar model receives the
  result sort's well-founded default during function projection. This is a model
  choice, not a semantic assertion; original replay remains mandatory.
- Admission remains the ADR-0079 finite scalar array boundary and all existing
  ROW, diff-skolem, interface, Boolean, encoding, and deadline caps remain. Other
  array component theories may be represented by the IR but canonical AUFBV
  declines them.

This decision does not claim eager array-valued Ackermann elimination, nested
arrays, a general warm incremental array owner, or a proof-producing theory
lemma stream.

## Soundness Argument

The ROW abstraction is a relaxation: each observed read becomes an unconstrained
scalar until valid ROW/select/extensionality clauses constrain it. Original
array-valued applications remain e-graph terms, so ordinary UF congruence is the
only reason two semantic parents share a class. The parent-select scheduler adds
only the valid implication that equal arrays at equal indices have equal reads.

Projection does not establish satisfiability. Grouping projection owners by a
final e-class merely chooses one total array consistent with all scalar reads
already required to agree at duplicate indices. A conflict while unioning
entries declines. Function tables are then built from concrete argument and
result `Value`s, with equal keys normalized by `FuncValue`. Every original
assertion is evaluated against the projected arrays and functions; a missing,
conflicting, or incorrectly chosen value yields `Unknown`, never `Sat`.

`Unsat` remains sound because every canonical round is a relaxation strengthened
only by valid EUF, ROW, select-congruence, or extensionality consequences. The
new IR declaration changes representability but not evaluator semantics.

## Consequences

Positive:

- SMT-LIB can represent ordinary non-zero-arity functions returning arrays.
- `select(f(args), i)`, stores over such results, array-valued `ite` branches,
  equal-argument application congruence, and direct application-array equality
  can share the retained canonical search.
- The projection order becomes correct for both array-valued results and
  array-valued function arguments.
- No eager cross product or new scalar encoding of array equality is introduced.

Costs and limits:

- Canonical preparation carries separate semantic-parent and projection-owner
  metadata for application reads.
- Projection may conservatively decline structural array equalities that finite
  observations cannot replay extensionally.
- The eager certifying fallback remains unavailable for array-result UFs, so
  online proof logging is still required for zero-trust coverage.

## Required Validation Before Acceptance

- IR declaration, evaluator, `FuncValue`, and SMT-LIB parse/write tests for an
  array-valued function result.
- Function-abstraction projection from a concrete fresh array result, plus an
  eager-elimination negative gate.
- Canonical SAT replay for one application read and for stores/`ite` over an
  application result.
- Canonical UNSAT for same-application and equal-argument/different-application
  read congruence, including observations split across applications.
- Direct equality/disequality interactions and a negative unsupported-component
  control.
- Front-door parity, deterministic analytic differential cases, and direct Z3
  comparison when the native feature is enabled.

## Acceptance Validation

Accepted on 2026-07-10 in `e944f7c1` after all required routes passed:

- IR declaration/evaluation, full-value `FuncValue`, function abstraction,
  eager-decline, and SMT-LIB parse/write tests;
- six focused canonical solver tests covering replay, congruent application
  reads, disjoint-observation projection union, stores, direct equality, and an
  unsupported Int-component control;
- a 96-seed semantic matrix run through the direct canonical route and
  `check_auto`, with every SAT model replayed, plus the same 96 cases compared
  directly to Z3 under the native feature: 288 comparisons, zero disagreements;
- the existing 11-test AUFBV all-feature differential binary, the complete 815
  solver-unit suite, the IR/rewrite/SMT-LIB suites, strict changed-crate
  all-target/all-feature clippy, and the exact-SHA pre-push gate.

The matrix includes same- and different-argument applications, split
observations, direct equality/disequality, store and array-ITE reads,
array-valued results used as scalar-UF keys, and both SAT and UNSAT outcomes.

## Alternatives Considered

### Bit-blast equality between fresh application arrays

Rejected: arrays are not scalar BV values, and encoding extensional equality at
the function interface would duplicate the existing array theory and its bounded
witness machinery.

### Project functions before arrays and repair afterward

Rejected: an array result is unavailable when the function table is first built,
and array-valued argument keys can change when arrays are subsequently projected.
Repeated ad hoc repair would recreate a fragile cyclic model builder.

### Eagerly reserve every application-result array equality

Rejected: this restores the quadratic application pair set removed by
ADR-0070/0082. E-graph congruence plus candidate-triggered parent-select events
already provide the relevant semantic relation.

### Treat each application read as a synthetic scalar UF

Rejected: it loses extensional sharing across indices and duplicates function
declarations, while making array equality and model projection harder rather
than simpler.

## Subsequent Decision

[ADR-0085](adr-0085-bounded-structural-array-class-equations.md) closes the
structural equality residual recorded here. Exact array-ITE equality
decomposition and bounded observed-read-preserving store/ITE/constant
realization now compose with the array-result projection order established by
this decision.

[ADR-0088](adr-0088-retained-warm-array-valued-uf-parents.md) reuses that
array-first/function-second ownership order in `IncrementalBvSolver` for
scalar-keyed array-valued applications. It retains private application arrays,
enforces conditional read congruence, groups concrete argument tuples, hides
private owners, and replays originals. Warm structural equality/extensionality
lands in ADR-0089/0090, relation flags in ADR-0091, and direct array-valued UF
parameters in ADR-0092. Structural array-valued parameter expressions,
nested/extended arrays, and proofs remain separate work.
