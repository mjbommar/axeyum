# ADR-0505: Fibonacci admission consumes only the checked semantic receipt

Status: accepted
Date: 2026-08-19
Index-summary: Register one exact crash-safe admission route for the checked Nat.fib_add_two receipt

## Context

The `Nat.fib_add_two` candidate has an immutable receipt produced by two fresh
kernel imports, with identical theorem identity, no axioms, no direct theorem
dependencies, no search during replay, and no ledger write. The fact frontier
still correctly refuses admission because candidate checking is not authority
to mutate the fact ledger.

## Decision

Register one authoritative operation for
`F:ml430-nat-fib-add-two-b86e0c82`. Its executor accepts only the frozen
checked-theorem receipt manifest, immutable archived observation, exact source
stream and theorem hashes, exact target definition, and empty axiom and direct
theorem-dependency sets. The ordinary typed execution and crash-safe
prepare/apply transaction remain the only route to ledger credit.

The operation records all four gates that mention the fact as reviewed. Any
new gate coupling returns the frontier to refusal until it is reviewed.

## Evidence

Registry, execution, transaction, and settled-fact replay mutation tests reject
changed receipt identity, source identity, proof identity, assurance counters,
operation authority, or admission binding. With the exact operation present,
the machine frontier has one admissible selection and no unreviewed gate
mentions; it predicts three direct child facts would become dependency-ready.

## Consequences

The semantic receipt can now be converted into durable knowledge without
caller-authored admission metadata. Registration alone changes no fact: the
execution must run from a clean commit, and the resulting transaction must
still survive preparation, application, event replay, fact replay, and child
eligibility measurement.
