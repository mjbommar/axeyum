# The quantified ladder's clocks: which budget, whose rung, and what more of it buys

**2026-09-13, lane `QBUDGET`.** [ADR-1970]'s handoff named what was left on
`UFNIA`/`UFLIA`: *"the 32-row family that stops with a third of the clock
unspent — whose remedy is a rung that does not exist, not a budget"*. This lane
takes that family.

Half of that sentence is right. The half that matters is not: there **is** a
budget the loop is denied, the denial is measurable to the millisecond, and
handing it back is worth nothing — for a reason that turns out to be a
capability statement about the instantiation loop rather than a scheduling one.

Every number below is re-derivable from the committed TSVs by `ab-summarize.py`
and `confirm-summarize.py`. Nothing here is transcribed.

## 1. The budget architecture — ONE deadline, sibling slices inside it

The two give-up strings in the census are **not two clocks**. There is one root
deadline (the caller's `SolverConfig::timeout`, 24 s on the boards), turned into
a single `deadline: Option<Instant>` that `finish_quantified_solve`
(`auto.rs:405`) threads through every rung. Each rung calls
`config_with_remaining_timeout` (`auto.rs:210`) to re-derive *what is left of the
root clock*, and some then cut a `LadderSlice` out of that remainder. So the
clocks are **nested** — every slice lies inside the root deadline — and one
rung's slice is a **sibling** of the next rung's.

| # | rung | slice of what is left | constant |
|---|---|---|---|
| 0 | valid-universal elimination | **all but 1/4** | `quant_valid_universal_budget` (ADR-1975, ships ON) |
| 1 | `q:forall-exists-witness` | all | — |
| 2 | `q:finite-expansion` | all | — |
| 3 | `q:uf-fmf-probe` | `uf_fmf_probe_budget` | — |
| 4 | `q:mbqi-quick` | **1/8** | `MBQI_FIRST_REFUSAL_SLICE` |
| 5 | `q:egraph` | all | `quant_egraph_budget` (ADR-1970, ships OFF) |
| 6 | `q:mbqi` | all | — |
| 6a | └ the Skolemized e-graph **retry**, inside rung 6 | **1/2** | `QINST_EGRAPH_RETRY_SLICE` |
| 7 | `q:uf-fmf-full` | all | — |

- **`quantified solve time budget exhausted after <stage>`** is
  `quantified_timeout()` (`auto.rs:309`) — the **root** deadline passing.
- **`e-matching: instantiation time budget exhausted`** is `egraph_timeout()`
  (`qinst_egraph.rs:2698`) — a rung's **own slice** expiring strictly inside the
  root deadline.

A row carrying the second string as its final give-up therefore still had root
clock when it stopped. Measured, on merged `main`: median `24,000 − wall` is
**+8,675 ms** (`UFNIA`, 37 rows) and **+2,822 ms** (`UFLIA`).

## 2. The second string is `q:mbqi`'s, not `q:egraph`'s

`run_egraph_quantified_fallback` (`auto.rs:345`) **declines** its `Unknown`
rather than returning it, so rung 5 cannot be what emits that string as a
verdict. Rung 6 is:

    prove_unsat_by_mbqi_inner            auto.rs:9582
      -> shape guard (5 sites: 9613, 9620, 9630, 9638, 9654)
      -> prove_unsat_by_ematching        auto.rs:9976
        -> skolemized_egraph_retry       auto.rs:10126
          -> prove_quantified_unsat_via_egraph   <- the SAME loop as rung 5,
                                                    on the SKOLEMIZED assertions
          under QINST_EGRAPH_RETRY_SLICE = fraction(1/2)

**The e-graph instantiation loop runs TWICE** on any quantified query reaching
`q:mbqi`. The census's own `bound_by` column already said so and was not read: it
is **`q:mbqi` on 27 of the 37** `UFNIA` rows in this family.

## 3. The starvation question, answered by measurement

The census `qtrace` reads `egraph@24.017:declined;(+23 segments of other stages
dropped)`. **That `(+N dropped)` is a rendering limit on the trace string**, and
nothing here is inferred from it: it cannot distinguish "those stages ran for
microseconds" from "ran fully and declined" from "never started".

`AXEYUM_QPROBE=1` prints the lines that can. On four files of the family
(`qprobe/UFNIA.family.base.tsv`, base arm, board envelope, one pinned core):

    wall 15,316 / 15,222 / 15,320 / 15,217 ms   of 24,000
    mbqi-rung   state=entered budget_ms=2995..2999
    mbqi-shape  exit=quantifier-below-top-level
    skolemized-egraph  budget=8.83 s  elapsed=8.85 s
                       -> e-matching: instantiation time budget exhausted

1. **The retry is cut off by its own slice, not by the root deadline.** Granted
   8.83 s, spends 8.85 s — every millisecond of its share.
2. **Nothing spends the remaining 8.7 s.** The run *ends* at 15.3 s. The ladder
   did not run out of clock; it ran out of **rungs**. The half is reserved for
   `q:uf-fmf-full`, which declines a non-pure-UF query in one cheap scan. **36 %
   of the budget is returned unused.**
3. **`q:egraph` is not the clock holder here.** Back out the arithmetic: rung 4
   is handed 1/8 = 3.0 s, so ~24 s remained above it; the retry is handed half of
   what is left = 8.83 s, so 17.7 s remained at its entry. Everything between
   them — `q:egraph` included — is **~3.3 s**. [ADR-1970]'s title is a true
   sentence about a **different** family.

`mbqi-shape exit=quantifier-below-top-level` closes the chain: on this family the
whole of `q:mbqi` **is** the e-matching route, so the retry is the only thing
rung 6 does.

### Why [ADR-1970]'s ceiling was not one-way for the e-graph family

[ADR-1970] sized a reserve on rung 5 by its `share = 1` ceiling — which hands
rungs 6–7 essentially the whole budget — and concluded that a file it did not
decide is "out of reach of every reserve". **Rung 6 hands half of whatever it
gets straight back to the same loop.** That arm therefore re-proportioned the two
e-graph passes' budgets rather than funding the non-e-graph rungs. Its null is
real, and it is a null about *where inside the e-graph family the clock sits*.

## 4. The lever, and its genuinely one-way ceiling

`AXEYUM_QINST_EGRAPH_RETRY_SHARE` — **ships OFF**. `off`, `0`, an empty value,
anything unparseable and an absent variable all resolve to the shipped `2`, so a
typo degrades to today's behaviour rather than selecting an arm nobody chose.
`whole` or `1` is the measured **ceiling** arm: the retry takes the whole
remaining root clock. Nothing on that rung can grant the loop more, and unlike
ADR-1970's it does not route the clock back through the thing it took it from.

PLACEHOLDER — sections 5 onward (the A/B, controls, noise floor, re-checks, the
non-monotonicity finding and the decision) are filled when the sweeps finish.

[ADR-1970]: ../../docs/research/09-decisions/adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md
[ADR-1975]: ../../docs/research/09-decisions/adr-1975-valid-universal-elimination-spends-24-seconds-to-prevent-a-107-millisecond-refutation.md
