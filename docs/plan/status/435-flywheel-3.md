# Lane: flywheel-3 — the first multi-target closure the exit criterion asked for

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, flywheel-3, 2026-09-02).** **The August exit
criterion is met.** One registered operation,
`authoritative-mathlib-nat-bit-constructor-family-v1`, closes **four**
previously open sibling facts (`Nat.bit_false`, `Nat.bit_false_apply`,
`Nat.bit_true`, `Nat.bit_true_apply`) with **no per-target proof code**, each
an axiom-free kernel term over a proof-isolated statement import (60
declarations, 0 axioms) and independently rechecked. The producer,
`propose_bounded_induction`, was written in August against *train* facts and
was not modified by this lane.

The whole live population of the contract was dispatched: **4 accepted, 6
declined, 0 errors**. The six declines are three distinct findings, not one —
four are `UnsupportedIffShape` (the producer has no `Iff.intro` leg and stops
at the shape test, never approaching its binder or induction budget, so the fix
is a leg not a bound), one is `TerminalNotClosed` on real `Nat.div` arithmetic,
and one is `TrustedDeclaration("dif_pos")` in the **importer**, before the
producer ran at all — the same structurally-earlier gate that took 15 of 27
dispatches on 2026-08-27, reconfirmed on a family neither seed contract covered.

`scripts/check-autogenesis-nat-bit-constructor-family.py` is the recheck and its
exit depends on four separate findings: accepts replay bit for bit, facts bound
to the operation exactly once with an empty footprint, the **six declines still
decline and are still open**, and a FALSE outcome-blind mutation is still
refused. Four mutation controls, one per finding, all exit 1 — table in the
gate's docstring.

**Two findings the next lane inherits, both measured.**
(1) `scripts/check-development-partition.py` reports PASS on this operation
**because it cannot see it**: `NURSERY` is `nursery-v1.json` alone and all four
closed facts live in `nursery-v2-extension.json` (0 occurrences in v1, 4 in v2).
Its rule — an operation closing a development fact must also close a train fact
— would otherwise fire. This lane deliberately did **not** fix the loader:
repairing a gate in the same change that registers the operation the repair
would flag is a lane clearing its own gate. The second reader with this exact
v1-only defect (`fact-frontier.py` was the first, found 2026-09-02).
(2) The census review's "do not build a producer against this frontier" was
correct at 4 targetable and is now stale at 23 — draw 19 landed in between. A
frontier measurement quoted without its ledger digest is a snapshot, not a
finding.

**Next task, pre-sized:** the `Iff` terminal leg. Population is the four
declines here plus the 40 `Iff`-headed facts ADR-1510 counted; the contract is
already written and stays un-retired at 6 live members; and `check_declines()`
fails loudly the day a decline turns into an accept, so the follow-up cannot
land silently. Honest bound: an `Iff` leg alone closes at most two of the four
(one also needs conjunction introduction, two need `Nat.mod` arithmetic).

Gates run and green: `validate-facts.py` (2,682 facts, 0 errors, 2,411 proved),
`validate-producer-contracts.py` (3 contracts), `validate-autogenesis-operations.py`
(30), `validate-producer-contract-declines.py` (33), `check-development-partition.py`,
`check-autogenesis-holdout-isolation.py` (226 held-out, 0 references),
`check-dispatchable-frontier.py`, `check-partition-edges.py`. No prelude field
was added, so `prelude_fields.rs` needed no regeneration. Nothing was pushed.

<!-- plan-section: landed-changes -->

| 2026-09-02 | flywheel-3 | opened the lane; status stub before any frontier work |
| 2026-09-02 | flywheel-3 | `producer-contract-natural-bit-constructor-family-v1` sized per ADR-1510 against ten live open facts, with the train-row absence stated rather than omitted |
| 2026-09-02 | flywheel-3 | dispatched all ten members: 4 accepted, 6 declined with typed reasons, 0 errors; four facts flipped to `proved`, `kernel-lean`, empty axiom footprint |
| 2026-09-02 | flywheel-3 | `check-autogenesis-nat-bit-constructor-family.py` — four findings, four mutation controls, all four kill |
| 2026-09-02 | flywheel-3 | ADR-1570: the exit criterion is met, the six declines partition into three findings, and two stale/blind gates are disclosed rather than repaired here |
