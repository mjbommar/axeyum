# ADR-0534: Library theorem receipts preregister direct premise identities

Status: accepted
Date: 2026-08-20
Index-summary: A semantic receipt may cover a theorem with direct library premises only when every premise name and canonical declaration identity is preregistered

## Context

The original checked semantic theorem receipt was designed for autonomous
zero-premise candidates. It correctly refuses every direct theorem dependency.
That contract admitted and receipted `Nat.fib_add_two`, but it cannot represent
the next library theorem: exact official `Nat.fib_coprime_fib_succ` has eight
intentional, axiom-free direct theorem premises.

Treating those dependencies as diagnostics would be too weak. Allowing an
untyped name whitelist would be worse: a changed proof under the same theorem
name could silently enter the authority set. Canonical declaration identity
already recursively binds direct dependency names to their admitted content
under ADR-0350, so it is the correct unit for explicit premise authority.

## Decision

Keep the zero-dependency receipt schema and issuer unchanged. Add a distinct
dependency-bound semantic theorem receipt that issues only when:

- the exact source artifact, target definition, fact, goal, candidate proof,
  candidate declaration, operation, and budget are preregistered;
- the expected direct theorem list is nonempty, strictly name-sorted, unique,
  and binds every name to its canonical declaration SHA-256;
- the independently admitted theorem reproduces the exact candidate
  identities;
- its complete kernel-derived axiom footprint is empty; and
- its observed direct theorem rows equal the preregistered rows exactly.

The receipt records canonical identities for both direct and transitive theorem
dependencies. Only the direct rows are premise authority. The transitive rows
are replay-bound diagnostics; they cannot be supplied as a permissive
whitelist. Receipt verification reconstructs and reissues the complete object
in a fresh kernel.

## Evidence

The first synthetic positive control derives one theorem from one separately
admitted theorem and issues an exact dependency-bound receipt. Adversarial
controls reject a changed dependency digest, an empty dependency authority, and
a mutated receipt. The existing V1 tests continue to require zero direct
theorem dependencies and retain their original schema and digest behavior.

The intended first real consumer is exact official
`Nat.fib_coprime_fib_succ`, whose eight direct premise names and candidate
identity were already sealed before receipt issuance.

## Alternatives

Changing the original V1 authority to accept an optional dependency list was
rejected because it would change a settled evidence schema and risk invalidating
the previously sealed recurrence receipt. Accepting names without declaration
identities was rejected because name stability is not proof-content stability.
Treating all transitive dependencies as premise authority was rejected because
it inflates the admitted basis and obscures which library results the proof
actually invokes directly.

## Consequences

Axeyum can now receipt ordinary compositional library theorems without
pretending they are premise-free. The added authority is deliberately narrow:
every direct premise is exact, visible, and replayed, while any reached axiom or
dependency drift fails closed. Admission and ledger mutation remain separate
operations; this receipt format alone grants no evaluation credit.
