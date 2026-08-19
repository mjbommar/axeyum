# ADR-0498: Corrected recurrence reuses the original budget

Status: accepted
Date: 2026-08-19
Index-summary: Authorize one Nat.fib_add_two v2 run after target-free Eq.rec controls without widening the original search budget

## Context

ADR-0496 retained the exhausted v1 rejection, and ADR-0497 closed its exact
`Eq.rec` universe-order defect with target-free controls. The target remains the
zero-dependency foothold selected by ADR-0495.

## Decision

Authorize one v2 execution bound to tooling commit `1880e56db` and the exact
composition-control identities. Preserve one helper, two templates, two kernel
submissions, one executor invocation, and zero retries. Continue excluding
proof bodies, held-out data, and historical successful target outcomes.

The v1 failure may justify the constructor repair but contributes no proof
premise. Any accepted candidate remains uncredited until receipt and admission.

## Consequences

The second run tests one falsifiable repair under the same search capacity.
Failure must be retained without retry. Success closes candidate construction
only; it does not by itself establish the ledger fact or unlock the Fibonacci/
GCD descendant chain.

