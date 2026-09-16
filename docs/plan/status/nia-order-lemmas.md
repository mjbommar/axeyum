# Lane: nia-order-lemmas — the two nonlinear lemma classes ADR-2112 measured absent, built and measured on OUR portfolio

<!-- plan-section: lane-status -->

**Lane nia-order-lemmas (`WIP`, nia-order-lemmas, 2026-09-16).** [ADR-2112]
Part E measured **order lemmas** (`nla_order_lemmas.cpp`) and **monotonicity
lemmas** (`nla_monotone_lemmas.cpp`) absent from `nia_linearize.rs`, and its
Part D ablation measured that neither is load-bearing for **z3** on more than 3
of the 75 files z3 decides — because z3 runs a redundant portfolio of seven and
66 of 75 files survive every single-class removal. That is a statement about
z3's portfolio, not ours: we have four classes, and the one that couples
magnitudes (`mccormick_lemmas`) fires only for factors with bounds the
relaxation entails. This lane measures what the two absent classes are worth
**to us**, behind one dated lever shipped DISARMED
([ADR-2136], artifacts in
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
therefore has to widen that predicate too, which is stated in [ADR-2136] §C
rather than buried.

**Next:** the interleaved A/B (one binary, two env values) on `QF_NIA`,
`QF_NRA` (control) and `UFNIA`, 200 files each at 24 s / 8 GiB on s6 cores 5
and 6, movers re-checked 3x, then the held-out 200-file `QF_NIA` draw. Ships ON
only with 0 stable losses and 0 flips on both.

<!-- plan-section: landed-changes -->

| 2026-09-16 | `5c46365f6` | `measure(nia)`: the sizing census — order lemmas apply to 111 of 116 undecided `QF_NIA` rows, monotonicity to 115; 8 fixture controls plus an independent cross-check against the engine's own cross-product count (89 of 89 nonzero, ratio median 1.00). |

[ADR-2112]: ../../research/09-decisions/adr-2112-qf-nia-what-the-clause-estimate-counts.md
[ADR-2136]: ../../research/09-decisions/adr-2136-order-and-monotonicity-lemmas-for-nia.md
