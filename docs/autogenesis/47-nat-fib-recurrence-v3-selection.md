# Fibonacci recurrence v3 selection

Date: 2026-08-19

## Decision

Authorize one v3 `Nat.fib_add_two` execution against tooling commit
`a0ee2a4c9`. Keep the original ceiling: one helper schema, two ordered
templates, two kernel submissions, one executor invocation, and zero retries.

V3 is bound to the eight passing stage identities from the zero-submission
control. The recurrence template now carries the explicit right-hand bridge
required by ADR-0500; the grammar and target are otherwise unchanged.

## Boundary

This selection has not executed the target and grants no receipt, evaluation
credit, or ledger write. Success would produce only a kernel-accepted candidate
until a semantic theorem receipt and ordinary fact admission land separately.

