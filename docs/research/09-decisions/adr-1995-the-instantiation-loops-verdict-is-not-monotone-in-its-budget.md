# ADR-1995: the e-graph retry is cut off by its own half-slice, and the loop's verdict is not monotone in its budget

Status: accepted
Index-summary: PLACEHOLDER — filled at the end of the lane.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1970]'s own handoff named what was left on `UFNIA`/`UFLIA`: *"the 32-row
family that stops with a third of the clock unspent — whose remedy is a rung
that does not exist, not a budget"*. This ADR takes that family, and finds that
half of that sentence is right and the half that matters is not: there **is** a
budget the loop is denied, the denial is measurable to the millisecond, and
handing it back is still worth nothing — for a reason that is a capability
statement about the loop rather than a scheduling one.

## The budget architecture, which had not been written down

One root deadline, and *sibling slices cut out of what is left of it*. The two
give-up strings in the `UFNIA`/`UFLIA` census are not two clocks:

- `quantified solve time budget exhausted after <stage>` is
  `quantified_timeout()` (`auto.rs:309`): the **root** deadline passing.
- `e-matching: instantiation time budget exhausted` is `egraph_timeout()`
  (`qinst_egraph.rs:2698`): a rung's **own slice** expiring strictly inside the
  root deadline.

A row whose final give-up is the second string therefore still had root clock
when it stopped, and the census data says how much: median `24,000 − wall` is
**+8,675 ms** on `UFNIA` and **+2,822 ms** on `UFLIA`.

## The second string does not belong to `q:egraph`

`run_egraph_quantified_fallback` (`auto.rs:345`) **declines** its `Unknown`
rather than returning it, so the rung that emits that string as a final verdict
cannot be `q:egraph`. It is `q:mbqi`:

    prove_unsat_by_mbqi_inner            auto.rs:9582
      -> shape guard (5 sites: 9613, 9620, 9630, 9638, 9654)
      -> prove_unsat_by_ematching        auto.rs:9976
        -> skolemized_egraph_retry       auto.rs:10126
          -> prove_quantified_unsat_via_egraph   <- the SAME loop as q:egraph,
                                                    on the SKOLEMIZED assertions
          under QINST_EGRAPH_RETRY_SLICE = fraction(1/2)

So **the e-graph instantiation loop runs twice** on any quantified query that
reaches `q:mbqi`. The census's own `bound_by` column said this and was not read:
it is `q:mbqi` on **27 of the 37** `UFNIA` rows in the family, not `q:egraph`.

## The starvation question, answered by measurement

The census `qtrace` reads `egraph@24.017:declined;(+23 segments of other stages
dropped)`. That `(+N dropped)` is a **rendering** limit on the trace string. It
cannot distinguish "those stages ran for microseconds", "ran fully and declined"
and "never started", and no conclusion was drawn from it here.
`AXEYUM_QPROBE=1` prints the lines that do distinguish them. On four files of the
family (base arm, 24 s / 8 GiB, one pinned core;
`bench-results/qbudget-20260913/qprobe/`):

    wall 15,316 / 15,222 / 15,320 / 15,217 ms  of 24,000
    mbqi-rung   state=entered budget_ms=2995..2999
    mbqi-shape  exit=quantifier-below-top-level
    skolemized-egraph  budget=8.83 s  elapsed=8.85 s
                       -> e-matching: instantiation time budget exhausted

Three things follow, none of which the census could have produced.

1. **The retry is cut off by its own slice, not by the root deadline.** Granted
   8.83 s, spends 8.85 s.
2. **Nothing spends the remaining 8.7 s.** The run ENDS at 15.3 s. The ladder did
   not run out of clock; it ran out of **rungs**. The half-slice is reserved for
   `q:uf-fmf-full`, which declines a non-pure-UF query in one cheap scan.
3. **`q:egraph` is not the clock holder on this family.** Backing out the
   arithmetic — the first-refusal rung is handed 1/8 (3.0 s), so ~24 s remained
   above it; the retry is handed half of what is left (8.83 s), so 17.7 s
   remained at its entry — puts everything in between, `q:egraph` included, at
   **~3.3 s**. [ADR-1970]'s title is a true sentence about a **different**
   family.

`mbqi-shape exit=quantifier-below-top-level` closes the chain: on this family the
whole of `q:mbqi` **is** the e-matching route.

## Why [ADR-1970]'s ceiling was not one-way for the e-graph family

[ADR-1970] sized a reserve on `q:egraph` by its `share = 1` ceiling, which hands
the rungs below essentially the whole budget, and called a file it did not decide
"out of reach of every reserve". The rung immediately below is `q:mbqi` — which
hands **half of whatever it gets straight back to the same loop**. That arm
therefore re-proportioned the two e-graph passes' budgets; it did not fund the
non-e-graph rungs. Its null stands as a null about **where inside the e-graph
family the clock sits**.

## The lever, and its genuinely one-way ceiling

`AXEYUM_QINST_EGRAPH_RETRY_SHARE` (**ships OFF**; `off`/`0`/empty/unparseable and
absent all resolve to the shipped `2`). The measured arm is `1`: the retry takes
the whole remaining root clock. Nothing on that rung can grant the loop more than
the root deadline it sits inside, and unlike ADR-1970's it does not route the
clock back through the thing it took it from.

## The measurement

PLACEHOLDER — the A/B table, controls, noise floor and re-checks are filled at
the end of the lane.

## The finding that outlives the null

PLACEHOLDER — the non-monotonicity argument, with its code citation and its
measured instance.

## Decision

PLACEHOLDER.

[ADR-1970]: adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md
