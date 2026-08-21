# ADR-0535: Dependency-bound receipts enter the ledger through a distinct operation

Status: accepted
Date: 2026-08-20
Index-summary: Ledger admission of a compositional theorem must preserve the exact direct-premise identities and transitive replay digest from its sealed receipt

## Context

ADR-0534 permits a semantic theorem receipt to name intentional direct library
premises. The existing authoritative receipt executor and fact transaction were
deliberately narrower: they admit only the zero-dependency V1 receipt used for
`Nat.fib_add_two`, and reject every retained theorem dependency.

The first dependency-bound receipt covers exact official
`Nat.fib_coprime_fib_succ`. It binds eight direct theorem names and canonical
declaration identities, 115 transitive diagnostic identities, two independent
full reconstructions, and an empty complete axiom footprint. Reusing the old
driver would either reject valid evidence or erase the distinction between an
isolated theorem and a compositional library theorem.

## Decision

Register a distinct authoritative dependency-theorem-receipt operation. Its
executor must replay the complete sealed evidence checker and bind:

- the canonical fact statement and exact receipt manifest;
- source, candidate, goal, proof, and target declaration identities;
- the complete nonempty sorted direct-premise rows and their set digest;
- the transitive theorem count and replay digest; and
- the empty complete axiom footprint and zero search/evaluation/ledger-write
  counters of the evidence-producing stage.

The prepared transaction retains those identities in the fact evidence row.
It may derive one ordinary `open` to `proved` ledger transition only through
the existing crash-safe intent, recovery, durable-event, and readiness-delta
protocol. The settled-fact checker independently replays the same receipt and
requires byte-for-byte equality with the retained binding.

The original zero-dependency driver and its settled facts remain unchanged.
Direct premise identities authorize composition; transitive identities remain
diagnostic replay bindings and do not become a broad premise whitelist.

## Evidence

The exact Fibonacci receipt is
`34b9aad06fc8a640c81df0951b1af37a464f2d9305c048784e4f590b83ff0d0e`.
Its eight-row direct set is
`d407340befc681d6d9abd187bbfead1f6ca1a7395c7dcf908950fd9c4d02e4d5`,
and its 115-row transitive replay set is
`fa08448a022db2ba1fdd4226979a86854e561888658801d295f4dba0dc3ef84e`.
Focused controls reject changes to either digest, removal of a direct premise,
receipt mutation, or weakening of the transaction assurance.

## Alternatives

Generalizing the old V1 driver was rejected because settled isolated-theorem
evidence must continue to mean zero direct theorem dependencies. Recording only
the receipt digest was rejected because the permanent fact row would hide the
premise basis that distinguishes this proof route. Treating all 115 transitive
theorems as ledger dependencies was rejected because those rows diagnose the
kernel closure rather than describe the fact DAG's authored mathematical
prerequisites.

## Consequences

Autogenesis can now turn an exact compositional library receipt into durable
knowledge without misreporting it as an isolated proof. Fact evidence becomes
larger, but it remains explicit, replayable, and fail-closed. Future receipt
schemas or premise policies require separate registered drivers rather than an
optional permissive branch in the settled V1 contract.
