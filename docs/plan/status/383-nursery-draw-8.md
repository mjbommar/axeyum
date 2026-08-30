# 383 — nursery draw 8

<!-- plan-section: lane-status -->

**Status: IN PROGRESS (early stub, committed before any measurement is
complete).** `check-dispatchable-frontier.py` reports FAIL: G7
queue-below-floor, 1 dispatchable, floor 10. This lane authors draw 8 or
declines it with reasons.

Predecessors:
[ADR-0654](../../research/09-decisions/adr-0654-draw-7-is-authored-and-the-lawful-family-set-was-forced-not-chosen.md)
(draw 7 authored, family set forced),
[ADR-0653](../../research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md)
(an unblocking lane declares the construction and nothing else),
[ADR-0695](../../research/09-decisions/adr-0695-the-construction-spends-the-closed-rows-not-the-evaluation-test.md)
(a construction spends its own closed-evaluation rows at `add_declaration`;
`fermat-numbers` amended out of held-out as a whole).

Draw 7's lane predicted draw 8 has no held-out supply and named
`NatCast.natCast` (14 rows) or `Nat.nthRoot` (13 rows) as the unblock. That
prediction is to be **verified on this tree, not inherited** — a handoff's
account of what remains is a hypothesis.

Measurements will land in [`../notes/383-nursery-draw-8.md`](../notes/383-nursery-draw-8.md).
