# ADR-0502: V3 success is a candidate until receipt and admission

Status: accepted
Date: 2026-08-19
Index-summary: Retain the axiom-free Nat.fib_add_two candidate but require a semantic receipt and ordinary admission before ledger credit

## Context

The v3 operation admitted a fresh `Nat.fib_add_two` theorem declaration with
zero axioms and theorem dependencies under the frozen two-submission budget.
The producer itself issued no semantic theorem receipt and made no ledger write.

## Decision

Retain the result as a checked candidate with zero evaluation and ledger credit.
Next issue and independently replay a semantic theorem receipt binding source,
goal, proof, declaration, operation, budget, and dependency audits. Only a
separate ordinary fact transaction may establish the ledger row and expose its
child as newly eligible.

## Consequences

The Fibonacci/GCD path has a real proof candidate, but the flywheel has not yet
advanced the durable knowledge state. This separation prevents kernel
acceptance inside an experiment from silently becoming fact authority.

