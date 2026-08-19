# ADR-0481: Reflexivity proposals are untrusted, fixed-budget, and separately admitted

Status: accepted
Date: 2026-08-18
Index-summary: Let a bounded syntactic producer propose Pi-wrapped Eq.refl terms, but grant no authority until an independent kernel and dependency audit accept the exact candidate

## Context

ADR-0480 created a proof-isolated kernel goal for one frozen Mathlib nursery
fact. The next flywheel arrow needs to construct a proof without importing the
upstream theorem. Treating a small producer as trusted would enlarge the TCB,
while immediately writing its successful output to the ledger would combine
proposal, checking, and durable admission into an unauditable event.

## Decision

The first producer is a syntactic, untrusted operation with fixed limits of
eight Pi binders and sixteen constructed expression nodes. It accepts only a
Pi telescope ending in an exact `Eq` application and proposes `Eq.refl` on the
left side, wrapped by the original binders.

The existing independent kernel is the authority on whether that proposal has
the requested type. After admission as a transient theorem, an explicit audit
must find zero axiom dependencies, zero theorem dependencies, and no dependency
on the transparent target definition. The receipt binds the goal, proof,
target declaration, budgets, environment size, and dependency results.

This increment performs no ledger write. Operation registration and durable
fact admission remain a separate next transaction.

## Evidence

The producer constructs a four-node, one-binder proof for
`F:ml430-nat-ascfactorial-zero-fd183202`. Its goal and proof digests are
respectively `87e37902...e3853d7` and `16600053...e08b53`. The independent
kernel accepts it with zero axiom and theorem dependencies and no target
dependency. An adversarial unequal-side input reaches the proposer but is
rejected by the kernel, demonstrating that producer acceptance carries no
authority.

## Alternatives

- Trust the producer's equality test. Rejected because definitional equality
  belongs to the kernel.
- Import the upstream Mathlib proof. Rejected because it measures translation,
  not autonomous proof construction.
- Mark the fact established immediately. Rejected because the authoritative
  registry, durable transaction, and clean post-state replay have not run.
- Generalize the search grammar now. Deferred until this exact operation can
  cross the durable admission boundary without weakening the evidence chain.

## Consequences

The repository now distinguishes a checked proof candidate from both a mere
adapted goal and an admitted fact. The extra state is more verbose, but it
prevents a local successful check from silently becoming ledger credit. The
next increment can reuse the exact candidate operation while concentrating on
registration, transaction identity, and clean replay.
