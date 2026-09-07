# Lane: int-divmod-witness — the second ADR-1721 slice: `eliminate_int_divmod`'s missing artifact

<!-- plan-section: lane-status -->

**Lane block (`WIP`, int-divmod-witness, 2026-09-07).** ADR-1721 §4 named
`eliminate_int_divmod` the sharpest remaining preprocessing gap and left the
*direction* of its `MAX_CONGRUENCE_GROUPS = 48` mode change open. It is now
established from the semantics rather than from the source comment
(ADR-1730):

**The cap is a RELAXATION.** The congruence lemmas are added conjuncts, so
dropping them above 48 zero-divisor groups only enlarges the model set.
Therefore `unsat` transfers soundly at every group count — the cap can never
produce a wrong `unsat` — and the direction that silently degrades is **`sat`**:
above the cap the `_/0` relaxation is no longer congruence-closed, so a
satisfying assignment need not induce a total `div(·, 0)` function and need not
be a model of the original. The source comment's claim about `unsat` is correct;
what it does not say is that the *other* direction is the one at stake, and no
caller could see which mode it got.

That matters because `dispatch_int_linear_refuters` is not only a refuter: it
runs `check_with_lia_simplex_within` and `check_with_lia_dpll` on the eliminated
form and returns their verdict — `Sat(model)` included — as the answer for the
original query. So the degraded direction is a direction this pass's consumer
actually reports.

Deliverables 2–4 in progress; see the landed rows.

<!-- plan-section: landed-changes -->

| 2026-09-07 | int-divmod-witness | ADR-1730: the `MAX_CONGRUENCE_GROUPS` cap is a relaxation, so the direction it silently changes is `sat`, not `unsat` |
