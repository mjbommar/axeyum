# ADR-0489: Contract bodies are residualized before real target selection

Status: accepted
Date: 2026-08-19
Index-summary: Decline real semantic-contract target selection until every omitted nonrecursive constant in a transparent definition body is residualized as an exact ordered parameter with a checked source specialization

## Context

ADR-0488 and the source-bound receipt prove that a local behavior contract can
remain outside the trusted base. The next proposed step was to preregister one
real Mathlib pointwise-function target. That requires more than a source
definition with a small body: the contract proposition itself must be closed in
the proof-free producer environment.

The exact target-demand census joined all 15 pointwise definition identities to
their 50 train/development bindings and independently re-imported every source
stream. Zero of 50 proof-free slices retain every nonrecursive constant named
directly by the transparent definition body. A direct defining equation cannot
currently be stated in any of them.

## Decision

Do not preregister a real theorem target or run a contract-aware producer yet.
First implement checked contract-body residualization:

1. walk the transparent source body and replace each omitted non-`Prop`
   constant instance with an exact, dependency-ordered local parameter;
2. replace recursive occurrences of the source definition with its already
   existing abstract function binder rather than adding a circular parameter;
3. retain declaration-content, instantiated-type, and universe identities for
   every new parameter;
4. require the source kernel to specialize all parameters back to the exact
   constants and check the residualized equation definitionally;
5. bind the residualized equation, parameter telescope, and specialization
   result into the semantic-contract receipt; and
6. grant no target, producer, proof, or ledger credit from residualization
   alone.

The first mechanism control is the unique axiom-free row with one missing body
dependency: `r018.ndjson`'s exact `Int.gcd` identity, whose body is
`Nat.gcd (Int.natAbs m) (Int.natAbs n)` and whose proof-free slice retains
`Int.natAbs` but omits `Nat.gcd`. This selects a representation control, not the
`Int.gcd_div` theorem as a proof target. Target selection resumes only after
the control specializes exactly and all wrong-order, wrong-identity,
self-reference, and omitted-dependency mutations fail.

## Evidence

- 15/15 pointwise identities and 50/50 affected rows were re-imported from the
  immutable Lean 4.30 train/development archive.
- Direct-equation environment eligibility is 0/50.
- Five rows miss exactly one direct body dependency; only `r018` also has an
  axiom-free source definition footprint.
- The `r018` source definition is 11 nodes, occurs twice in an equality goal,
  and the row already has three statement abstractions. These facts make it a
  narrow residualization control but do not establish proof sufficiency.

## Consequences

The sequence gains one explicit representation layer: type slicing removes
untrusted implementation closure; contract residualization restores only the
transparent behavior expression as a closed local telescope; the source kernel
then discharges it. Later contract selection may measure target usefulness only
after this layer passes. A 0-yield producer run is avoided because its input
language is currently incapable of expressing the proposed contract.
