# ADR-0482: External statement reflexivity is an exact authoritative driver

Status: accepted
Date: 2026-08-18
Index-summary: Register one Mathlib surface fact by binding its immutable adapter, external export, fixed reflexivity budget, kernel result, and durable replay contract end to end

## Context

ADR-0480 established a proof-isolated surface-to-kernel goal, and ADR-0481
established a fresh checked reflexivity candidate without ledger credit. The
general authoritative executor previously understood only SMT evidence and two
internal Nat episode drivers. Leaving the candidate outside that executor would
make it a demonstration rather than one turn of the autonomous flywheel.

The proof-free import is an external 52 KiB content-addressed object. Vendoring
it would duplicate the project-wide external-artifact policy, while treating a
missing mount as success would make the fact's checker non-failing.

## Decision

Add `axeyum-lean-import/statement-reflexivity-v1` as a fourth authoritative
driver, exact to `F:ml430-nat-ascfactorial-zero-fd183202`. The registry binds
the tracked adapter and reflexivity manifests, external artifact identity,
target definition, and fixed construction budgets. The executor independently
checks the external bytes and fresh kernel receipt on every run.

Extend the transaction builder and settled-fact checker with the same closed
driver contract. Missing or changed external bytes are a replay failure. The
candidate manifest remains an immutable pre-admission input; any admission is
recorded in a separate result artifact and ledger evidence row.

## Evidence

Registry mutation controls reject changed targets or budgets. Execution receipt
controls reject a changed proof digest. Transaction and settled-fact controls
bind the manifest, external artifact, goal, proof, statement, and construction
limits. The capability census moves exactly one row from a pre-execution
decline to eligibility while consuming zero executor budget.

## Alternatives

- Vendor the NDJSON stream. Rejected because the canonical object already has
  immutable shared storage and a complete regeneration recipe.
- Let missing external data count as a skipped successful replay. Rejected
  because a checker that cannot fail cannot support authoritative proof credit.
- Add a generic surface-language operation. Rejected because only this exact
  statement shape and proof route have passed the independent checks.
- Apply the fact update during registration. Rejected because authoritative
  execution requires a clean source commit and durable admission is a separate
  compare-and-swap transaction.

## Consequences

The machine frontier can select one real nursery row through the ordinary
authoritative executor. Fleet or CI hosts that replay the settled fact must
mount the content-addressed artifact store or regenerate the exact object. The
next commit can execute and admit from a clean, immutable registry prestate.
