# Lane: bench-boolean-core — Boolean-core benchmarks and the per-conflict throughput gap

<!-- plan-section: lane-status -->

**`WIP`, bench-boolean-core, 2026-09-07.** The native core's per-conflict cost is
now instrumented and decomposed, closing the gap the
[2026-09-05 search-statistics note](../../research/11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md)
named as its own largest limitation (no decision, propagation or restart
counter). Full record, including the hypotheses that were wrong:
[`docs/research/12-performance/bench-boolean-core-2026-09-07.md`](../../research/12-performance/bench-boolean-core-2026-09-07.md).

**What is now known.** `conflicts/s = propagations/s ÷ propagations/conflict`,
and measured on one idle host against Kissat 4.0.4 over eight p4dfa instances,
the two factors point different ways: our **propagation rate is within ~1.4x of
Kissat's**, while we need a **median 2.56x more propagation per conflict** (up
to 7.7x). The deficit is propagation *volume*, not propagation *speed* — so the
data-structure work the gap is usually attributed to (watch width, arena layout,
per-conflict allocation) is aimed at the factor we are already competitive on.
A direct A/B confirms it: removing `analyze`'s per-conflict `vec![false; nvars]`
is trajectory-identical and worth **1.6%**.

**DRAT logging costs under 1% of search time** on real corpus CNF (`vec` +0.2%,
text +0.7%, binary +0.0%, all inside the no-proof arm's own run-to-run spread).
Binary DRAT is **2.3x** smaller than text, not the ~3x the format is usually
described with, and **15x cheaper to write**.

**Next.** The surviving candidate for the propagation-volume gap is
**inprocessing**: `solve_with_drat_proof` runs none of the crate's own `vivify`,
`simplify` or `bve`, and Kissat's `probe` umbrella reduces the formula its
propagation runs over. The restart schedule was the prior candidate and was
tested and refuted (restarting 8.4x more often raises propagations per conflict
and lowers throughput). Not yet run: inprocessing, CaDiCaL on the same host,
certificate cost at corpus scale, and hypotheses H2-H5 (all of which move the
factor that is not the deficit).

<!-- plan-section: landed-changes -->

| 2026-09-07 | `fbae4c16c` | `benches/proof_pipeline.rs` (DRAT check fwd/bwd, LRAT elaborate fwd/bwd, text/binary DRAT write and parse — none had a bench) and `benches/proof_sat_propagate.rs`, whose fixture asserts its own shape against the p4dfa corpus and rejected two candidate fixtures before accepting one. |
| 2026-09-07 | `7fd80725f` | `SearchCounters` + `solve_with_drat_proof_counted`: propagations, decisions, restarts, reductions, watch visits, blocking-literal misses, resolution steps and `analyze`'s per-conflict mark bytes. Opt-in, clock-free, DRAT byte-identical to an uncounted run. |
| 2026-09-07 | `cf7f6ade8` | Lane opened: diary with six pre-registered hypotheses, ranked before any measurement. |
