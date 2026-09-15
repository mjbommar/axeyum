# Lane: derived-order — Phase 4, a ladder order derived from the outcome ledger

<!-- plan-section: lane-status -->

**Lane derived-order (`DONE`, derived-order, 2026-09-15).** Phase 4 of
[dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md#5-phase-4--derived-ladder-policy-conditional),
on the two classes lane LEDGER-STRUCTURE nominated. **[ADR-2106]** —
`proposed`, because the ship criterion (0 stable losses) is NOT met and the
derived order lands OFF with the measurement rather than being smoothed.

**SIZING FIRST, and both classes came back under five files.** The ledger's
ceiling is in TIME on files that already decide, so the question is how many
UNDECIDED rows a reorder could convert. `QF_NIA`/`Int`: 115 undecided of 199,
raw ceiling 47, **refined 3** — 42 of the 47 declined with a CNF-SIZE refusal
(`estimated 130191180 CNF clauses ... exceeds budget 64000000`) that renders
through the same `DeclineReason::Budget` word as a clock expiry, and 2 more are
a bounded-width refusal; more clock buys none of them.
`UFNIA`/`Int|Function`: **0 of 6**, and its 126,764 ms of "prefix cost" is not
a prefix at all — `q:skolem-qf` records a PROBE, hands off to the whole
quantifier-free ladder, and records its decision when that returns, so the
hand-off was being counted as time above the decider. It appears twice on all
24 trails and the clock before its first entry is **0 ms on every one**. That
refutes the second of the two classes Phase 4 was conditioned on.

**Shipped: the mechanism, not the order.** `dispatch_nonlinear_int_tail`'s six
rungs are behind `int_tail_order::IntTailRoute`, so the order is data
(`HAND`/`DERIVED`) and `AXEYUM_LADDER_ORDER` gives an interleaved A/B both arms
from ONE binary. `SHIPPED` points at `HAND`.

**Why not the derived order.** Phase 4's key — "(decision rate, then median
elapsed)" — does not say WHOSE elapsed. `int-blast-ladder` wins in a **339 ms**
median and LOSES in a **12,566 ms** median (max 23,189 against a 24,000 ms
budget) on 112 of its 177 attempts; at the ladder's HEAD that is paid out of
every rung below it. Five committed `hypothesis_min::tests` capability fixtures
go red under `derived` at their own 2 s budget and all ten pass under `hand`.

**Measured.** Interleaved one-binary A/B, 24 s / 8 GiB, 12 pinned core pairs on
s5/s6/s7, divisions serial per shard. Pinned draw (the files the order was
derived from): **400 rows, A 137 / B 129, net −8, 3 gains, 11 losses, 0 flips,
0 exit-status differences, 92 `:status` comparisons with 0 disagreements, 0
malformed**; all 14 movers re-run 3× per arm gave **11 STABLE-LOSS, 1
STABLE-GAIN, 2 BOTH-DECIDE, 0 UNSTABLE**. Held-out draw of 200 fresh files per
division (seeded, excluding every pinned path and every path any committed
ledger row carries) agrees. The trade in the other direction is real and is
reported rather than buried: on the 75 `QF_NIA` rows BOTH arms decide the
derived order costs **129.0 s against 767.9 s**, median 10,918 ms → **407 ms**
— 27× faster on what it decides, five net files worse at deciding.

Mutation: `derived-ladder-order` in `scripts/tests/mutation_controls.py`, two
mutations each killing EXACTLY ONE named fixture from a 5-test baseline;
`--check-anchors` stale=0. The fixture had to move to
`docs/plan/fixtures/derived-ladder-order-20260915.tsv` because
`mutation_controls.py` EXCLUDES `bench-results` from the tree it copies — an
`include_str!` from there makes every mutation report `BASELINE DID NOT BUILD`,
which is not a result.

Evidence, per-row lists and every script:
[`bench-results/derived-order-20260915/`](../../../bench-results/derived-order-20260915/README.md).

[ADR-2106]: ../../research/09-decisions/adr-2106-derived-ladder-order.md
