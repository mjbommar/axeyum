# ADR-0474: Fixture operation scope cannot escalate through canonical path

Status: accepted
Date: 2026-08-18
Index-summary: A counterfactual-only operation must reject authoritative transaction preparation even when its input is the canonical fact path

## Context

The fixture kernel transaction adapter determined
`source_is_authoritative` solely by comparing its input path with the canonical
fact-ledger path. Its registered operation,
`autogenesis-kernel-premise-evidence-v1`, is explicitly scoped
`counterfactual-fixture-only`.

Those two facts were not connected. A caller able to present an open canonical
fact row and a valid fixture experiment could ask the fixture adapter to emit a
transaction whose precondition claimed `source_is_authoritative: true`.
Initial application still replays preparation, so this was not a demonstrated
unilateral write exploit, but the proposal layer had crossed its declared
authority boundary. Building Autogenesis-1 on that path would turn a test
fixture into production authority by pathname.

## Decision

The fixture `build_transaction` path now rejects
`source_is_authoritative=True` before constructing any delta. Only
`build_authoritative_transaction`, which consumes a receipt from an operation
whose registry scope is `authoritative`, may produce an authoritative proposal.

The existing fixture admission remains usable against an explicit fixture fact
root. The applicant continues to require `source_is_authoritative: false` in
that mode and `true` in production mode.

## Consequences

- The qualified counterfactual B -> A experiment can select a chain for the next
  engineering step but cannot authorize a ledger write.
- An authoritative kernel B operation and executor receipt must be registered
  before the chain can cross the production compare-and-swap boundary.
- A regression test exercises the exact attempted scope escalation.
