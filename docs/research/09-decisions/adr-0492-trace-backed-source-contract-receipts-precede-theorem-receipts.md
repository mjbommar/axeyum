# ADR-0492: Trace-backed source-contract receipts precede theorem receipts

Status: accepted
Date: 2026-08-19
Index-summary: Issue a distinct replayable source-contract receipt from exact residualization, specialization, source identity, one selected delta step, and an empty source axiom footprint before any theorem receipt

## Context

ADR-0491 established that the exact `Int.gcd` body follows from one selected
structural delta step while `Nat.gcd` remains opaque. The prior semantic
function-contract receipt cannot consume that evidence: it requires a theorem
declaration witnessing the specialized contract, then rejects the declaration's
complete 52-theorem closure.

Replacing that rejection inside the theorem receipt would conflate two claims:

1. an exact source definition instantiates a residualized behavior contract;
2. an independently proved generic theorem consumes that contract to establish
   a downstream proposition.

Only the first claim is currently available for real Mathlib data.

## Decision

Introduce a separate versioned trace-backed source-contract receipt. Issuance
and replay recompute and bind:

- the exact source declaration instance, binder name, universe arguments,
  instantiated type, and canonical content identity;
- every residual and retained direct body instance, with ordered roles and
  exact identities;
- checked body accounting, residualization, generalized contract, and exact
  source specialization;
- one bounded selected-definition delta step and its exact before/after
  identities;
- the single consulted source declaration; and
- the source definition's complete axiom footprint, which must be empty.

Residual or retained instances whose direct declaration kind is axiom, theorem,
or opaque are rejected. An axiom hidden transitively below an ordinary residual
definition is rejected by the source axiom-footprint gate. The generalized
template must contain no exact source or residual constant instance.

The receipt creates no theorem declaration. It is a prerequisite that a later
theorem receipt may consume explicitly; it does not inherit or imply theorem,
producer, held-out, or ledger authority.

## Evidence

- Synthetic issuance/replay binds the complete payload and rejects mutations to
  source identity, generalized contract, delta output, consulted declarations,
  and binder identity.
- An omitted helper fails body accounting.
- A direct trusted instance fails before residualization credit.
- An axiom hidden one definition below the residual helper is found by the
  source footprint and rejected.
- The exact pinned `Int.gcd` control issues and exactly replays one receipt with
  residual `Nat.gcd`, retained `Int` and `Int.natAbs`, one selected delta, and
  zero source axioms or witness theorems.

## Consequences

`Int.gcd` now has a real source-contract receipt, but no downstream theorem has
been selected or proved. The next turn must join this bottom-up contract with
top-down demand: select one train/development proposition whose proof needs the
contract, preregister the proof grammar and budgets, and only then attempt a
generic proof and semantic theorem receipt.
