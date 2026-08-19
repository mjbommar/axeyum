# ADR-0490: Contract witness independence uses the complete theorem closure

Status: accepted
Date: 2026-08-19
Index-summary: Reject semantic-contract witnesses with any theorem in their complete declaration closure; direct theorem dependencies alone miss answers hidden behind transparent definitions

## Context

ADR-0489's first exact residualization control successfully turns omitted
`Nat.gcd` into a local binder and checks that specialization recovers the
transparent `Int.gcd` equation. Its bounded source witness is `Eq.refl`, has no
axioms, and reports zero through `Kernel::theorem_dependencies`.

That zero is direct-only. The complete declaration closure contains 52
theorems reached through `Int.gcd`, `Nat.gcd`, and their transparent helpers.
An adversarial synthetic control confirms the general hole: a witness may name
only a transparent definition whose value names an upstream theorem. Direct
theorem enumeration returns empty even though the answer is one edge below.

## Decision

Semantic-contract receipt independence is evaluated over
`Kernel::declaration_dependency_closure`, filtered by declaration kind, not by
the direct theorem helper. Generic proof and source witness admission reject
any theorem anywhere in that closure. The concrete receipt's theorem inventory
is likewise transitive and must equal exactly the independently accepted
generic theorem and witness when those two closures are otherwise theorem-free.

Do not whitelist Mathlib termination, accessibility, equation-compiler, or
helper theorems merely because the candidate proof term is reflexivity. A
printed proof term and a direct dependency list do not establish which
transparent definitions or reductions the kernel relied upon.

The `Int.gcd` result therefore receives residualization and specialization
credit only. It is not receipt-eligible and does not authorize a contract,
target proof, or ledger transition.

The next mechanism must preserve the strict closure rule while avoiding the
irrelevant implementation tail: construct a proof-free residual definition
template with local binders, bind it structurally to the exact source
declaration, and check a bounded one-step source delta witness whose trace may
unfold only the selected source definition. Residual constants such as
`Nat.gcd` remain opaque local parameters; their implementations and theorem
closures are not consulted.

## Evidence

- The exact `r018` control residualizes `Nat.gcd`, retains `Int` and
  `Int.natAbs`, exposes two function arguments, and specializes exactly.
- The source equation's fixed reflexivity witness has zero axioms and zero
  direct theorem dependencies but 52 transitive theorem dependencies.
- A synthetic theorem hidden behind a transparent definition passes direct
  enumeration and is now rejected by receipt issuance.
- Existing clean synthetic contract receipts remain accepted after the audit is
  strengthened.

## Consequences

Previously issued synthetic receipts remain valid because their complete
closures are theorem-free. No real Mathlib contract is admitted. Future
source-side witnesses must provide either a theorem-free complete closure or a
separately checked bounded reduction trace; direct dependency counts can remain
diagnostics but never assurance authority.
