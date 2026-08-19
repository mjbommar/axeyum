# Fibonacci checked-theorem receipt selection

Date: 2026-08-19

## Decision

Authorize one semantic receipt invocation for the sealed `Nat.fib_add_two`
candidate. The receipt driver imports the exact r080 stream into two fresh
kernels and reconstructs only the already selected v3 plan. It performs no
search. Both kernels must admit the exact goal/proof/declaration identities and
issue identical receipts.

The receipt API additionally binds the source stream, target definition, fact
ID, candidate observation, operation, and original search budget. It rejects
axioms and direct theorem dependencies rather than merely reporting them.

## Boundary

The receipt operation may submit the fixed theorem once in each fresh kernel,
but may run only once and may not retry. It grants one semantic theorem receipt
and still grants zero evaluation or ledger credit. Admission remains a separate
crash-safe transaction.

