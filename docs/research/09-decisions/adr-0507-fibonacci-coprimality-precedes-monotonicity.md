# ADR-0507: Fibonacci coprimality precedes monotonicity

Status: accepted
Date: 2026-08-19
Index-summary: Select Fibonacci coprimality by downstream leverage and measured relation shape

## Context

Admission of `Nat.fib_add_two` made two children ready:
`Nat.fib_coprime_fib_succ` and `Nat.fib_le_fib_succ`. Selecting by adjacency
alone would ignore both the long-range theorem programme and the capability
boundary exposed by the actual imported terms.

## Decision

Pursue `Nat.fib_coprime_fib_succ` first. Before proof search, freeze a bounded
gcd-coprimality induction plan using the admitted recurrence as its sole
theorem premise. Keep monotonicity ready but deferred until the system has an
explicit inductive-relation proof route for `Nat.le`.

## Evidence

The foundational plan already places coprimality on the route to
`Nat.gcd_fib_add_self` and `Nat.fib_gcd`. The exact train streams show a second,
independent reason: weak-head reduction turns `Nat.Coprime` into an `Eq` goal,
whereas the monotonicity goal remains headed by `Nat.le`. The selected fact
therefore both opens the planned GCD chain and reuses the equality-oriented
composition boundary already exercised by the recurrence.

The sealed observations and tracked manifest record zero proof search, kernel
submissions, evaluation credit, and ledger writes. No proof body or held-out
row was inspected.

## Consequences

The next increment is plan construction and premise accounting, not theorem
admission. Success must expose every definition, eliminator, arithmetic fact,
and induction step the kernel term will need. Failure is useful if it names a
reusable missing gcd or induction primitive; it must not be hidden by importing
the target theorem or expanding the trusted base.
