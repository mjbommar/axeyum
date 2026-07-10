# ADR-0090: Retained Warm Structural Array Equality

Status: proposed
Date: 2026-07-10

## Context

ADR-0089 retains exact top-level array disequality over every warm-supported
parent, but positive equality still requires both operands to be independently
projectable leaves. Consequently `store(a, i, v) = b`, constant-array equality,
and array-ITE equality rebuild through the canonical dispatcher even though:

- ADR-0087 already gives every observed structural read an exact,
  candidate-triggered scalar summary;
- ADR-0088 gives scalar-keyed array-valued applications private total-array
  projection owners; and
- ADR-0085 already establishes the bounded observed-read-preserving model
  realization contract for structural array equations on the canonical path.

Finite read agreement alone still cannot justify positive array equality. The
warm path needs a total model owner for each equality operand, equality
observations that interact with old and future reads, and bounded realization
of each structural owner from its original constructor term. This is the
positive semantic branch that arbitrary Boolean relation flags will need next.

## Decision

`IncrementalBvSolver` will admit top-level positive equality between any two
same-sorted warm-supported array parents over a BV index and Bool or BV
elements: symbols, stores, constant arrays, array ITEs, and scalar-keyed
array-valued UF applications.

### Structural projection owners

Each distinct structural parent used by an active equality receives one cached
private array symbol. The symbol is a model-construction owner, not a semantic
replacement. The solver also records a function-free structural equation

```text
owner(A) = rewrite(A)
```

where direct symbols remain themselves, array-valued UF applications become
their ADR-0088 projection owners, and scalar guards, indices, values, and UF
arguments use the existing warm scalar abstraction. Reusing a parent reuses its
owner and dependency metadata. Private owners never appear in returned models
or assumption cores.

Observed reads over an owned structural parent keep their ADR-0087 exact
summary. Giving the read a projection owner additionally lets the existing
same-index equality congruence machinery connect it to reads from other members
of the equality class; it does not bypass constructor semantics.

### Equality observations

A structural equality materializes paired reads at a bounded deterministic set
of indices:

- indices of already-active warm reads;
- every store index reachable in either operand; and
- one private probe index for the equality.

The paired scalar values are asserted equal in the equality's frame or one-shot
scope. When a later assertion or assumption introduces a new read index, every
active structural equality receives the corresponding paired observation in
that newer scope. This makes equality interact with a later disequality's exact
diff index and with reads asserted on either side before or after the equality.
Each structural read still closes through candidate-triggered exact summaries.

The probe is an observation, not finite-domain extensionality. It catches
constructor contradictions such as unequal constant arrays, while total model
realization and final replay establish positive equality at every index.

### Class-aware structural model realization

Model construction remains ordered:

1. project scalar reads and scalar UF applications;
2. merge every active positive array-owner equality class;
3. realize each active structural owner equation to a bounded fixed point;
4. build array-valued function tables from the resulting private owners;
5. filter private symbols and replay every original root.

Realization follows ADR-0085 but updates an entire warm equality class whenever
one owner changes:

- assigning an owner class to a target array is allowed only if every observed
  read of every class member keeps its candidate scalar value;
- realizing `store(base, i, v)` as a target requires `target[i] = v`, then
  realizes `base` as that target;
- realizing `ite(c, a, b)` follows only the candidate-selected branch;
- a constant array must already equal the target; and
- unsupported or non-convergent equations decline.

For each mismatch, first try assigning an owner class from the evaluated
structural side, then try realizing the structural side from the owner target.
Structural-to-structural equations iterate deterministically because shared
leaves and equality chains can invalidate an earlier equation. The shared query
deadline, 512-node/256-depth limits, a bounded realization-step count, and the
existing refinement-round ceiling apply.

### Admission and lifecycle

- Admission remains literal-only. Array equality nested under arbitrary Boolean
  structure remains deferred until retained relation flags are added.
- All shape, depth, node, application-parent, and prospective observation limits
  are checked before warm solver mutation. One-over roots defer cleanly.
- Equality edges, paired observation roots, and active owner equations are
  selector-scoped. Cached private owners and exact read summaries may survive a
  pop, but cannot participate without active frame or one-shot metadata.
- Missing owners, observation conflicts, expired deadlines, failed fixed-point
  realization, or replay uncertainty return `Unknown`; they cannot yield SAT.
- Array-valued parameters, nested/extended arrays, and online proof logging
  remain deferred.

## Soundness Argument

Every paired observation is a direct consequence of an active array equality.
For structural reads, ADR-0087's exact summary ties the scalar owner to the
original store, constant, or selected ITE semantics before a candidate can be
accepted. These valid implications may refute a candidate but cannot remove a
model of the original assertion set.

The private structural owner is sound only as model metadata. A successful
realization establishes its equation over a total array value. Class-aware
assignment preserves every scalar observation, store realization checks the
write point, and ITE realization follows the evaluated guard. Rechecking all
equations to a fixed point prevents shared-owner updates from silently breaking
an earlier equation. Array-valued functions are projected only after this
array-complete assignment exists.

No SAT verdict follows from finite observations or local repair alone. The
ground evaluator must still replay every original structural equality and all
other active roots after private owners are filtered. UNSAT uses only encoded
user roots plus equality congruence and exact read/ROW consequences. Therefore
resource exhaustion or an unsupported cycle can reduce completeness only by
returning `Unknown`.

## Required Validation Before Acceptance

- No-read SAT replay for symbol/store, store/store, symbol/constant,
  symbol/array-ITE, and array-valued-UF/store equality.
- Equality before and after conflicting reads, including a store write-index
  contradiction and an equality chain mixing structural and projection owners.
- Unequal constant arrays and selected-ITE equality plus branch disequality
  decide UNSAT; an unselected branch disequality remains SAT.
- Bool elements and BV256 indices/elements project and replay.
- Push/pop and opposite one-shot assumptions scope owner equations,
  observations, and user-facing cores; private owners remain filtered.
- Positive equality nested under Boolean structure, unsupported signatures,
  exact depth/node/application/observation one-over inputs, and an expired
  realization deadline defer without an accepted partial model.
- A deterministic 64-seed warm/`check_auto`/direct-Z3 matrix covers structural
  SAT/UNSAT, equality chains, ITE selection, constants, Bool values, and
  array-valued UF composition with zero disagreement and replay of every SAT.
- Full solver, symbolic-execution, EVM/fuzz, strict clippy, warning-denied
  rustdoc, link, foundational-resource, and exact-SHA push gates pass.

## Alternatives

### Treat matching finite reads as total equality

Rejected. It is not extensionality and can accept different unobserved defaults.

### Replace every structural constructor with an unconstrained array symbol

Rejected. The owner is useful for equality classes, but without its exact model
equation and replay it is an unsound flattening.

### Encode every constructor equation in CNF at every index

Rejected. Wide BV index domains make this exponential. Candidate-triggered
scalar summaries plus total model realization cover the required boundary.

### Add Boolean relation flags in the same step

Deferred in dependency order. A flag's true branch needs the structural
equality contract defined here, while its false branch can reuse ADR-0089's
diff witness. Landing and validating the positive branch first keeps the next
flag decision mechanical and independently auditable.

## Consequences

Top-level positive equality over every currently retained structural parent can
reuse the warm CNF/SAT state and produce replayed total models. Structural
parents gain cached private model owners, and equality observations add a
bounded cross-product surface over active relation/read indices.

Arbitrary Boolean relation flags, array-valued parameters, memory BMC/
k-induction, online array proofs, nested/extended arrays, and the remaining EVM
performance gap remain later work.
