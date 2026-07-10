# ADR-0088: Retained Warm Array-Valued UF Parents

Status: accepted
Date: 2026-07-10

## Context

ADR-0084 admits finite-scalar array-valued UF results on the canonical AUFBV
bus: application parents participate in the e-graph, final classes own result
arrays, function tables project after arrays, and original replay gates SAT.
ADR-0086/0087 independently make bounded structural reads genuinely warm in
`IncrementalBvSolver`, but their leaf boundary still stops at array symbols.
Consequently `select(f(x), i)` and a store or array-ITE rooted at `f(x)` leave
the warm path and rebuild through the one-shot dispatcher even when every
function argument, array component, and observed result is finite scalar.

The next warm increment should preserve the application parent and its model
key rather than flattening it into an unrelated array symbol or claiming whole-
array equality from finitely many reads. This follows the array/UF ownership
question in the
[research register](../08-planning/research-questions.md), advances the deferred
half of ADR-0030, and composes the canonical ADR-0084 projection order with the
incremental ADR-0087 final-check loop.

## Decision

`IncrementalBvSolver` will retain observed reads over supported array-valued UF
applications as warm projection leaves.

The admitted signature is deliberately semantic rather than width-special:

- every function parameter is `Bool` or `BitVec`;
- the result is `Array(BitVec, Bool|BitVec)`; and
- arguments and read indices may contain any scalar expression already covered
  by warm abstraction, including scalar Bool/BV UF applications and wide BVs.

For each retained array-valued application `f(args)`:

- recursively abstract its scalar arguments through the existing warm UF/BV
  machinery and retain both original and abstracted argument terms;
- allocate one private array projection owner with the exact result sort;
- give each observed `select(f(args), i)` the normal private scalar read owner,
  retaining an abstracted index for CNF congruence and candidate/model
  evaluation;
- treat the application as a leaf of ADR-0087's transitive store/constant/ITE
  summary, so `select(store(f(args), i, v), j)` and array-ITE compositions stay
  warm without defining the application as a scalar array expression.

Read congruence is exact and selector-scoped:

```text
args1 = args2 and i = j  =>  read(f(args1), i) = read(f(args2), j)
```

The same application term omits the argument guard. Scalar argument equalities
use the abstracted warm terms, so nested scalar UF arguments share their own
existing congruence contracts. The lemma belongs to the frame or one-shot
assumption that brings the read pair together; application/read owners remain
private and persistent.

After a candidate satisfies every active ADR-0087 summary, projection proceeds
deterministically:

1. project observed scalar read owners into each private application-array
   owner;
2. evaluate abstracted argument tuples with the candidate's internal scalar
   owners;
3. group same-function applications by equal concrete argument tuple and merge
   their disjoint observations into one exact array value, rejecting conflicting
   values at one concrete index;
4. define that array result at the tuple in a full-value `FuncValue`, using the
   result sort's well-founded default array elsewhere;
5. remove every private scalar/array owner from the public model and replay all
   original active assertions and one-shot assumptions.

The existing 512 structural-node/read-site and 256-depth limits remain. At most
64 distinct array-valued UF application parents are admitted per root, bounding
the quadratic conditional-congruence surface. One-over roots defer before any
partial warm assertion is committed. Application records and harmless private
owners may survive pop; only reads from active frames/assumptions participate in
congruence and projection.

Array-valued UF parameters, non-BV array indices, non-Bool/BV elements, nested
array results, array equality/disequality involving applications, general warm
extensionality, and proof logging remain outside this increment. Direct finite-
array parameters subsequently land in ADR-0092; structural array-key
expressions continue to use the canonical/fallback routes.

## Soundness Argument

An application read owner is a definitional abstraction constrained only by
valid function congruence and, when structurally wrapped, exact ADR-0087 array
identities. If equal concrete arguments and equal concrete indices produce
different read values, the conditional congruence lemma refutes the candidate.
UNSAT therefore follows only from user roots plus valid first-order/array
lemmas, and selector scoping prevents a popped equality consequence from
persisting.

For SAT, grouping by concrete argument tuple constructs one total result array
per observed function point. Conditional congruence guarantees consistency at
overlapping concrete indices; deterministic zero/default values cover every
unobserved index and function point. The full-value function table then makes
the evaluator's original `Apply` and `Select` terms denote exactly the projected
observations. Private owners are hidden, and evaluator replay remains the final
acceptance gate. Missing values, conflicting projection, unsupported shapes,
deadline/resource exhaustion, or replay failure cannot yield accepted SAT.

## Acceptance Validation

- Ten all-feature mechanism and differential tests cover single-application
  model projection, private-owner filtering, equal-argument/index conflicts,
  split-observation merging, nested scalar UFs, store/ITE parents, Bool and
  BV256 components, push/pop, one-shot cores, and unsupported-shape deferral.
- The exact parent boundary admits 64 distinct applications and defers 65
  without partial retained state. Int keys, array keys, Int result indices, and
  whole-array equality involving an application also defer cleanly.
- A deterministic 64-seed matrix contributes 64 warm, 64 `check_auto`, and 64
  direct-Z3 comparisons. All 192 agree, and every warm SAT model replays the
  original query.
- All 816 solver unit tests, 77 symbolic-execution tests, the canonical three-
  test array-result-UF integration, and the complete EVM test/fuzz suite pass.
  The EVM corpus does not construct array-valued UFs, so this decision makes no
  EVM timing claim.
- Strict solver/EVM clippy, warning-denied solver/EVM rustdoc, documentation
  links, foundational-resource generation, and the exact-SHA push gate pass.
  Design commit `41019413` and implementation commit `f2bb16ab` are on
  `origin/main`.

## Alternatives

### Replace each application with an unrelated user-visible array symbol

Rejected. It loses same-function congruence and cannot reconstruct the original
`FuncValue`; replay would fail or require an unsound interpretation shortcut.

### Assert whole-array equality for applications with equal arguments

Rejected as a warm Boolean encoding. Array values are not bit-blasted, and
finitely observed reads are not extensional equality. Conditional congruence on
the observed scalar reads is exact and sufficient for model construction.

### Route every array-result application to canonical AUFBV

Retained as fallback, not as the warm implementation. It is sound and broader,
but rebuilds the theory/search object on each symbolic-execution branch and
does not advance ADR-0030's retained-state requirement.

### Admit array-valued parameters in the same slice

Deferred in this slice. Their argument equality requires warm array equality
ownership rather than scalar argument comparison. ADR-0092 later admits the
direct-symbol finite-array subset by reusing ADR-0091 relation flags for
candidate-sensitive key congruence; ADR-0093 later admits supported
store/constant/array-ITE structural keys. Nested array-valued application keys
remain a separate boundary.

## Consequences

Array-valued UF results become first-class warm memory leaves and compose with
candidate-triggered ROW, retained scalar UF arguments, push/pop, model replay,
and learned SAT state. Canonical and warm array/function projection use the same
array-first/function-second semantic order.

The warm solver gains private array owners and must filter them from public
models. Projection groups use full values and deterministic application order,
and conditional congruence adds a bounded quadratic surface. Structural array
equality/extensionality follows in ADR-0089/0090, nested Boolean relation flags
follow in ADR-0091, direct array-valued parameters follow in ADR-0092, and
supported structural array-valued parameters follow in ADR-0093. Nested
array-valued application keys, proof artifacts, memory BMC/k-induction, and the
remaining EVM performance gap remain later work.

## Subsequent Decision

[ADR-0089](adr-0089-retained-warm-array-relations.md) closes the whole-array
relation boundary for those private owners. Positive equality can merge symbol/
application projection classes before function construction, while one exact
private diff witness handles disequality across all supported structural
parents. Positive structural equality follows in ADR-0090, arbitrary Boolean
relation flags follow in ADR-0091, and direct finite-array parameters follow in
ADR-0092. Structural array-valued parameter expressions, proofs, and the
performance gap remain.
