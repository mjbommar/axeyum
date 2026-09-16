# Lane: nia-order-lemmas — the two nonlinear lemma classes ADR-2112 measured absent, built and measured on OUR portfolio

<!-- plan-section: lane-status -->

**Lane nia-order-lemmas (`WIP`, nia-order-lemmas, 2026-09-16).** [ADR-2112](../../research/09-decisions/adr-2112-qf-nia-what-the-clause-estimate-counts.md)
Part E measured **order lemmas** (`nla_order_lemmas.cpp`) and **monotonicity
lemmas** (`nla_monotone_lemmas.cpp`) absent from `nia_linearize.rs`, and its
Part D ablation measured that neither is load-bearing for **z3** on more than 3
of the 75 files z3 decides — because z3 runs a redundant portfolio of seven and
66 of 75 files survive every single-class removal. That is a statement about
z3's portfolio, not ours: we have four classes, and the one that couples
magnitudes (`mccormick_lemmas`) fires only for factors with bounds the
relaxation entails. This lane measures what the two absent classes are worth
**to us**, behind one dated lever shipped DISARMED
([ADR-2136](../../research/09-decisions/adr-2136-order-and-monotonicity-lemmas-for-nia.md), artifacts in
[`bench-results/nia-order-lemmas-20260916/`](../../../bench-results/nia-order-lemmas-20260916/README.md)).

**Sizing, landed first because the design depends on it.** All 116 undecided
`QF_NIA` T1 rows, 0 errored: the order lemma's step is available on **111**,
monotonicity's on **115**. The candidate set is enormous — median **2,249**
shared-factor product pairs per file, max **9,407,886** — which rules out
static enumeration and forces the model-driven, per-round-capped shape z3 uses.
And `unbounded_products` equals `products` at every quantile: **no product on
this population has both factors two-sidedly bounded**, so the entailed-bound
passes produce nothing and `RefinementSetup::refine` is false — the refinement
loop runs ONE round on exactly the files this lane is aimed at. Arming
therefore has to widen that predicate too, which is stated in [ADR-2136](../../research/09-decisions/adr-2136-order-and-monotonicity-lemmas-for-nia.md) §C
rather than buried.

**DONE.** The A/B ran to full coverage on all four populations, 200/200 each:
`QF_NIA` pinned 82 → 80, `QF_NRA` control 124 → 124 with 0 movers, **`UFNIA`
54 → 61**, held-out `QF_NIA` 85 → 85. **Disagreements 0 of 800.** 15 raw movers
re-checked 3x per arm: **10 STABLE-GAIN, 3 STABLE-LOSS, 2 UNSTABLE**, seven of
the gains in `UFNIA` alone.

**The lever stays DISARMED and ADR-2136 is `proposed`.** The criterion was 0
stable losses on pinned AND held-out; there are 2 and 1. All three are
`unsat → unknown` — budget starvation of a later ladder route, a SCHEDULING
cost and not a lemma defect. What the lane does establish against ADR-2112's
decision 4: the two classes are worth **10 stable gains across 800 files with
zero flips**, so they are not worthless to us; the loop that hosts them costs
more than they pay on `QF_NIA`.

**Handed forward.** (a) Separate "emit these lemmas" from "grant the loop a
larger budget slice" — a one-line experiment the three named losing files score
directly. (b) The ceiling is the relaxation: the pass is reached on 59 of 116
undecided rows and the other 67 never produce a spurious model at all. (c) The
six `z3` NIA differential fuzzes were NOT RUN and must be, with a nonzero count
in both arms, before anyone arms this lever.

<!-- plan-section: landed-changes -->

| 2026-09-16 | `5c46365f6` | `measure(nia)`: the sizing census — order lemmas apply to 111 of 116 undecided `QF_NIA` rows, monotonicity to 115; 8 fixture controls plus an independent cross-check against the engine's own cross-product count (89 of 89 nonzero, ratio median 1.00). |
| 2026-09-16 | `52255968b` | `measure(nia)`: the `QF_NRA` control — 200/200, 124 decided in both arms, 0 movers, 0 disagreements. |
