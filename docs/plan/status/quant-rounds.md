# Lane: quant-rounds — the 177-file "round budget" family

<!-- plan-section: lane-status -->

**Lane quant-rounds (`DONE`, quant-rounds, 2026-09-13).** ADR-1950 named the
largest actionable blocker on the six-division board: `e-matching instantiation
did not refute within the round budget`, **177 of 390 winnable files (45 %)**,
giving up with a median **23,994 ms of a 24,000 ms budget unspent**. This lane
was sent to A/B the round cap. **The answer is: do not raise it, and the reason
is measured — 0 of 177 rows reach it.**

**The classification was read off a string THREE different loop exits emitted.**
`qinst_egraph.rs`'s own dump label for the point already said so: it was spelled
`"fixpoint-or-break"`. A fixpoint at round 1 and a 512-round ceiling exit both
leave the clock untouched, so ADR-1950's `ms_left` evidence column — which
separates ROUND from CLOCK — cannot separate ROUND from SHAPE.

**The sizing bracket: 177 blocked → 0 reachable.**

    population           n   SHAPE   CLOCK   ROUND   other   max rounds entered
    LRA                117     117       0       0       0       7
    AUFLIA              48      40       4       0       4      99
    BV + NRA + UFLIA    12      10       1       0       1      65
    TOTAL              177     167       5       0       5      99

The ceiling is **512**. The deepest row in the whole family entered **99**; the
LRA majority entered **one**. This is the most extreme of the week's brackets
(143→6, 51→2, 173→10, 84→49).

Stronger than the table: scanning the WHOLE trace rather than the first give-up
line, **the round-budget string appears in 0 of the 177 runs**, and the zero is
not a grep that missed its subject — every row carries a give-up line and 171
carry the fixpoint string the same scan looks for. Every non-`SHAPE` row was
re-run three more times: **`ROUND` is 0 across all 30 solves.**

**The value sweep is flat at zero from the first step.** Four arms — shipped
512, 2x, 4x, 8x — back to back on one pinned core per file, arm order rotating,
**all 177 rows**: gained 0, lost 0 at every arm, `conflicting decided verdicts
across arms: 0`, totals unchanged (LRA 50.9/49.7/49.7/51.4 s, AUFLIA
499.8/500.0/502.9/500.8 s). ADR-1945's QF_UFBV sweep read +31/+44/+45 and used
the curve's SHAPE to decide; this curve never leaves zero, which is a different
finding from "8x was not enough".

**The cost on decided work is nil.** All 692 already-decided rows at the 8x arm:
**0 lost, 0 gained, 0 sat/unsat disagreement**, median 109 ms on both arms,
722.2 s against 722.4 s in total, and the same 8 rows above 20 s on both.
ADR-1945's 40x watchdog blow-up does not reproduce, for the reason the bracket
gives.

**The cost control the brief named was three-quarters vacuous, and the number is
published.** QF_UFLIA, QF_UFLRA and QF_DT are quantifier-FREE, so the e-matching
loop cannot run on them: the `q:egraph` rung is attempted on **0 of 200 QF_DT
files, 0 of 200 QF_UFLIA and 0 of 200 QF_UFLRA** (NRA: 9 of 200). That is
ADR-1945's own `ufbv_online`-on-0-of-400 hole reproduced. The non-vacuous
control is the **692 files the board says we already decide** in the same six
quantified divisions — same corpus families, same ladder, same loop, and a
verdict to lose.

**What the 167 fixpoint rows actually are — the next lane's lever.** All 117 LRA
rows under `AXEYUM_QPROBE=1`: **103 (88 %) fixpoint with an EMPTY e-graph
(`ground=0`)**, 63 carry at least one triggerless universal. 98 of the 117 are
`LRA/2010-Monniaux-QE` — a ten-deep alternating `∀∃∀∃…` prefix over the reals
**with no free constant anywhere**, so there is not one ground term for a
trigger to match; the other 19 are `scholl-smt08`, the same quantifier-
elimination shape. `q:fourier-motzkin` does not appear in their route trails at
all. **No round count and no ground-term ceiling expresses a fix for a query
with nothing to instantiate over.** The BV and AUFLIA remainders are a separate
finding and must not inherit this one.

**Shipped: the instrument, not a raised cap.** `InstantiationLoopExit` records
which of the three conditions stopped the loop and the give-up detail names it
(`RoundCeiling` keeps the historical string unchanged, because the historical
string was accurate for exactly that exit). Three `cap_lever!` levers —
`AXEYUM_QINST_ROUNDS`, `AXEYUM_QINST_CADENCE`, `AXEYUM_QINST_ROUND_HEADROOM` —
with defaults byte-identical and registered as `config_registry` `env_override`s.
**No verdict changed**: 117 pinned LRA rows, 117 `unknown` before and after, and
0 conflicting decided verdicts across all four sweep arms. Guards
mutation-controlled: **7 mutations, 7 killed**, six of them killing exactly one
test; the seventh is the soundness mutation and kills the whole "never refutes a
satisfiable query" family, `no_round_ceiling_arm_refutes_a_satisfiable_query`
included.

**[ADR-1956](../../research/09-decisions/adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md)
records it**, and adds two rules to ADR-1950: a ranked give-up string may not be
classified by its wording when more than one exit can emit it (the *producer*
must distinguish them, because a remaining-budget distribution cannot), and a
control population must be shown to REACH the code under test, with the number.

**Next actions.** (a) The 167 fixpoint rows are a quantifier-ELIMINATION
population, not an instantiation one — price real QE / a real-model MBQI against
`2010-Monniaux-QE` + `scholl-smt08` (117 pinned rows, 98+19). (b) AUFLIA's 4
CLOCK + 4 other rows and BV's 10 non-trivial fixpoints are separate and unsized.
(c) The 38 `mbqi`→BV-backend declines board-six left open.

<!-- plan-section: landed-changes -->

| 2026-09-13 | quant-rounds | ADR-1950's top blocker re-measured: **0 of 177** rows are bound by the round ceiling (167 fixpoint, 5 clock), a 2x/4x/8x sweep gains **0** and loses **0**, and 88 % of the LRA family fixpoints with an EMPTY e-graph on quantifier-elimination benchmarks; `InstantiationLoopExit` splits the three exits that shared one give-up string, three `cap_lever!` levers with byte-identical defaults, ADR-1956 |
