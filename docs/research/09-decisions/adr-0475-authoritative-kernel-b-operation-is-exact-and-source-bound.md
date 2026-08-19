# ADR-0475: Authoritative kernel B operation is exact and source-bound

Status: accepted
Date: 2026-08-18
Index-summary: Register one exact authoritative Nat.zero_add induction operation whose receipt binds the formal statement and whose fresh-kernel evidence is axiom-free and free of retained answers

## Context

The primary chain is operationally qualified, but its producer/checker operation
was scoped to counterfactual fixtures. ADR-0474 correctly prevents that operation
from acquiring write authority merely because its input happens to be a canonical
fact path.

The existing induction checker is not generic despite its structural proposal
grammar. Its fresh kernel target is hardcoded to `Nat.zero_add`, and its retained
answer deny set is exactly `Nat.zero_add` and `Nat.mul_one`. Advertising it as a
general Nat induction executor would therefore move the overclaim from chain
selection into route dispatch.

The fact frontier also derives gate mentions by scanning scripts. The B fact is
named by three fixture controls. Treating every textual mention as an eternal
block would make reviewed coupling impossible; ignoring the list would make a
new gate dependency invisible.

## Decision

Register `authoritative-kernel-nat-zero-add-induction-v1` with:

- sole applicability to `F:nat-zero-add`;
- exact driver `axeyum-lean-kernel/nat-zero-add-induction-v1`;
- target theorem `Nat.zero_add`;
- exact deny set `Nat.mul_one`, `Nat.zero_add`;
- exactly two catalog-only structural induction plans;
- fresh-kernel checking through
  `autogenesis_induction_plan_check`; and
- required empty axiom footprint and retained-answer dependency set.

The executor constructs a proof-body-free goal catalog from the selected fact's
formal statement, derives the deterministic plans, runs the checker in a fresh
process, parses the typed kernel evidence, and compares its canonical type back
to the source fact. Ambient executable overrides are rejected, so the receipt's
`caller_authored_command: false` field cannot coexist with a caller-selected
checker binary. Its receipt binds the clean Git commit, frontier, registry,
fact, formal-statement digest, target, deny set, budget, result, and assurance.

The three existing fixture-script mentions are recorded on the operation as an
exact reviewed list. The frontier rejects an additional live mention, a missing
review entry, or a stale review that no longer corresponds to a live mention.
It also rejects zero or multiple matching authoritative operations before a fact
can be called admissible.

## Compatibility

`reviewed_gate_mentions` is optional and defaults to empty. It is deliberately
absent from the already-admitted SMT operation, so that operation's content hash
and the settled fact's durable checker binding remain unchanged. Adding an
unrelated operation changes the registry digest, but historical rows bind the
registry at execution and the immutable operation object separately.

## Evidence

The real driver produced canonical type
`((x0 : AxNat) -> Eq.{1} AxNat (AxNat.add AxNat.zero x0) x0)` at plan rank 2 of
2, with empty axiom footprint and retained-answer dependencies. The normalized
receipt prepared an authoritative kernel transaction, and the resulting
after-fact replayed through `check-autogenesis-fact-operation.py`. Mutation
controls reject a changed canonical type, target theorem, deny scope, gate
review, formal-statement digest, footprint, and assurance.

## Consequences

- B now has a real authoritative operation contract; the already-settled live
  fact is not rewritten.
- A still lacks an authoritative operation, so this does not complete the chain.
- Generalizing the kernel checker remains future work and is required before a
  fallback chain can honestly reuse this driver.
