# Imported candidate agent read surface

Date: 2026-08-26

## Result

The agent can now query the generated imported-candidate index through a ninth
tier-R tool, `imported_candidates`. It accepts exactly one query axis:

- a shell-style exact-name glob; or
- an exact canonical-type substring.

The tool returns typed rows containing source identity, canonical and
alpha-stable type identity, measured footprint, direct theorem-dependency
count, retrieval disposition, and separate strategy/execution eligibility.
It is additive and read-only. It does not merge imported rows into the native
lemma index and is absent from tier C.

For the live query `name_glob="Nat.testBit_*"`, the tool returns exactly one
row:

- `Nat.testBit_bitwise`;
- `retrieval_disposition = reconstruct-required`;
- `strategy_eligible = true`;
- `execution_eligible = false`;
- 29 direct theorem dependencies; and
- the exact five-member quotient/`propext` footprint.

A canonical-type query for `AxNat.bitwise` returns the same row. Empty queries
and two-axis queries fail closed. The toolset fingerprint automatically changes
because the read surface changed, so later episodes cannot claim the earlier
tool policy hash.

## Why this is a real boundary

Previously the agent could see only native constructed-kernel lemmas. The
correct generic theorem existed upstream but was invisible, leading the plan
toward rebuilding a theorem before even auditing it. Conversely, simply adding
the imported theorem to `lemma_candidates` would make an assumption-bearing
proof look interchangeable with an axiom-free native premise.

The separate typed surface preserves both useful facts:

1. the theorem is highly relevant strategy guidance; and
2. its current proof must not execute or transport.

## Next implementation

Add a reconstruction proposal kind that consumes an exact
`reconstruct-required` descriptor plus a proof-isolated target kernel. Its
output must be a new candidate term, not the imported proof. The existing
independent checker must then admit that term and measure an empty footprint
before any specialization or production credit. Until that proposal path
exists, the agent may cite the row in strategy but cannot dispatch it.
