# ADR-0483: Factorial-zero reuse shares proof-free source but keeps authority exact

Status: accepted
Date: 2026-08-19
Index-summary: Generalize the checked factorial-zero adapter and reflexivity grammar across two frozen train facts while retaining one exact source-bound authoritative operation per fact

## Context

ADR-0482 rejected a generic surface-language authority because only one exact
statement had survived proof isolation, candidate construction, kernel checking,
and durable admission. The sealed train/development census now supplies new
evidence: the same bounded producer independently proves both
`Nat.ascFactorial_zero` and `Nat.descFactorial_zero`, with identical budgets and
zero axiom, theorem, or target-definition dependencies. The second fact remains
open and therefore tests reuse rather than replay of existing credit.

The family evidence does not justify granting authority to every Pi-wrapped
equality. The coverage census includes seven equality-shaped candidates whose
proposed reflexivity terms are rejected by the kernel, and 114 rows cannot yet
enter the proof-isolated adapter.

## Decision

Create one tracked Lean source containing exactly two transparent `Prop`
definitions for the natural-factorial zero family. Export and independently
check each target in isolation. The family checker binds both immutable streams,
the prior sealed coverage identities, zero proof-body and held-out access, and
the fresh-kernel dependency audits.

Reuse the existing bounded reflexivity producer and independent checker, but
register `Nat.descFactorial_zero` as its own exact authoritative operation. Its
fact ID, statement digest, adapter manifest, external stream, target definition,
goal, proof, target content, budgets, and admission policy remain fixed. The
already-admitted ascending-factorial fact retains its original operation and
historical evidence identities.

## Evidence

The shared source exports both family members from pinned Mathlib v4.30.0 and
Lean 4.30.0. Fresh Axeyum kernels reproduce the census goal and proof identities
for both targets. Mutation controls reject held-out access, family expansion,
shared operation authority, changed receipts, and admission fields on an open
fact. The operation validator and nursery dispatch census identify the new row
without executing it or writing the ledger.

## Alternatives

- Expand ADR-0482's operation to all exact equalities. Rejected because seven
  measured equality candidates fail kernel checking and the adapter frontier is
  still narrow.
- Rewrite the first fact's historical operation to use the new family stream.
  Rejected because that would invalidate its immutable admission binding for no
  assurance gain.
- Vendor either NDJSON stream. Rejected under ADR-0479; the streams remain
  immutable external resources with tracked identities and reproduction data.

## Consequences

The system now has a reusable proof-free adapter family and proof operation,
while authority remains per-fact and fail-closed. Registration grants no credit:
the open descendant fact must still be selected from a clean commit, executed,
crash-recovered, replayed, and recorded through the ordinary transaction chain.
