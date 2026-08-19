# ADR-0506: Fibonacci recurrence admission must measure real child readiness

Status: accepted
Date: 2026-08-19
Index-summary: Admit Nat.fib_add_two and reproduce its non-leaf readiness delta exactly

## Context

The registered `Nat.fib_add_two` receipt operation became the machine
frontier's sole admissible selection. The fact has three direct ledger
children, but direct adjacency alone does not imply that every child becomes
ready: a child may retain other open dependencies.

The existing isolated-admission replay asserted that every reproduced
admission had an empty `newly_ready` set. That was sufficient for the two
factorial-zero leaf admissions but incorrectly painted the generic replay tool
into a leaf-only corner.

## Decision

Apply the receipt-backed transaction through the ordinary durable-intent and
recovery protocol, then derive child readiness from the before and after
frontiers. Require isolated replay to reproduce the retained `newly_ready`
value exactly rather than require it to be empty.

The historical replay report field name remains unchanged so existing sealed
leaf reports continue to verify; its check now means exact readiness-delta
reproduction for both leaves and non-leaves.

## Evidence

The deliberate after-intent fault exited 75 and left the fact byte-identical.
Recovery committed transaction `b37e368a87cdf8dd497c835afd3d92df131e5f16d54289d79d03a10fa677fe3e`
and durable event `1a868c6ab73c220c5c965859e81512b2a6bb569d9cc8ae2b97d7e4bb00972587`.
The settled operation replay and all 324 fact validations pass.

The measured readiness delta has one authoritative write, zero fixture writes,
and exactly two newly ready children: `Nat.Coprime (fib n) (fib (n+1))` and
`fib n <= fib (n+1)`. The third direct child, the integer recurrence, remains
blocked by the still-open integer-to-natural Fibonacci cast fact.

## Consequences

This is the first semantic theorem receipt to become durable axiom-free ledger
knowledge and the first admission in this programme that measurably opens more
work. A clean isolated replay must reproduce both newly ready children before
the admission archive receives final replay credit.
