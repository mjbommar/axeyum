# Lane: nra-trace — QF_NRA is two gaps, and only one of them is a CAD gap

<!-- plan-section: lane-status -->

**The QF_NRA gap is sized and split** (`DONE`, nra-trace, 2026-09-15). The board
records 117 of 200 against z3's 187. The 83 undecided files were censused
through `--trace` into 83 outcome-ledger rows, then traced against z3 three
ways — its own tactic, forced `qfnra-nlsat`, and incremental linearization with
`smt.arith.nl.nra=false` so it cannot fall back into nlsat.

**z3's linearization arm, the one shaped like `nra.rs`, decides 29 of 83. Its
CAD arm decides 45 more — 44 of them in under one second, median 108 ms.** The
control on that table is that `z3-default` decides 70 here and 117 + 70 = 187 is
exactly the head-to-head's z3 column.

The two largest buckets point opposite ways. The 26-file `refinement reached a
fixpoint` bucket (3 variables, degree 8, one assertion, 23 of them
`meti-tarski`) is 26/26 for CAD and 5/26 for linearization. The 22-file
atom-capacity bucket (`LassoRanker`, ~450 variables, degree 2) is 14 for
linearization and 10 for CAD. A fix for one is not a fix for the other, and
ADR-2110 says so in its own "what this does not say".

`nra-real-root` declined `not-applicable` for every shape it refuses, and that
token was in the trail of **78 of the 83**. It now records which of twelve
guards stopped it, through `note`, which is the identity on `Some`. It answered
on first use: the largest bucket's example declines `non-conjunctive` as
shipped — one `or` ends the exact decider before any projection — and
`projection` once reduced to a single conjunct.

`AXEYUM_NRA_CAD` ships `default` (byte-identical to the previous engine) and is
registered dated. Its A/B on QF_NRA's 200 is **A 117 / B 119, net +2, 0 losses,
0 flips, 0 `:status` disagreements over 234 comparable verdicts**, with arm A
reproducing the board's own 117.

Two instruments lied before they were right and both are recorded in the ADR:
the first bucket key read the last trail decline and reported two QUANTIFIER
routes as this division's largest buckets, and the shape reader called 40 and
then 31 files "divisions" before the right question — is the DENOMINATOR
constant — gave 0 of 83 and 0 of all 200.

The ADR is `proposed`, not `accepted`: the attribution landed unconditionally,
but no default moved -- `AXEYUM_NRA_CAD` ships OFF. Movers were re-run 3x per
arm: **2 STABLE-GAIN, 0 STABLE-LOSS** across both divisions, with QF_NIA's raw
1-gain/1-loss both resolving to ambient (BOTH-DECIDE and UNSTABLE with an
identical pattern in each arm).

Detail: [ADR-2110](../../research/09-decisions/adr-2110-qf-nra-what-decides-the-seventy.md),
artifacts in `bench-results/nra-trace-20260915/`.

<!-- plan-section: landed-changes -->

| 2026-09-15 | `4a9638930` | Census of the 83 undecided QF_NRA files: 83 of 83 outcome-ledger rows, buckets keyed on the route that held the budget, shape features from a parser rather than a grep. Records the two wrong readings the instruments gave first. |
| 2026-09-15 | `4def0b025` | `nra_real_root::CadDecline` — twelve causes behind what was one `not-applicable` for 78 of 83 files — plus the `AXEYUM_NRA_CAD` lever registered dated, and the three-arm z3 + cvc5 reference trace that sizes the gap. |
| 2026-09-15 | `40b99ced8` | ADR-2110: the CAD-versus-linearization split, two design-difference claims with `file:line` on both sides, the QF_NRA A/B (+2, 0 losses, 0 flips), and the `nra-cad-attribution` mutation suite (three guards, each deletion killing exactly one named test). |
| 2026-09-15 | `HEAD` | QF_NIA A/B (+0, 0 flips, 0 `:status` disagreements over 166 comparable verdicts) and the 3x mover recheck: 2 STABLE-GAIN, 0 STABLE-LOSS. ADR set to `proposed` -- the attribution landed unconditionally but no default moved. |
