# Lane: lra-theory-side — the QF_LRA theory side (final-check call count, atom-cap budget)

<!-- plan-section: lane-status -->

**`WIP`, lra-theory-side, 2026-09-07.** QF_LRA is 84 files behind the real
frontier after [ADR-1732](../../research/09-decisions/adr-1732-second-reference-per-division-not-a-replacement.md)
(Yices 181, cvc5 145, ours 97). This lane took the theory side. Full record,
including two hypotheses that were wrong and one plan premise that was false:
[the diary](../../research/12-performance/lra-theory-side-2026-09-07.md) and
[the measurement log](../../research/12-performance/lra-theory-side-2026-09-07-log.md).

**The census is wrong in two places, and both were found by wiring a counter
before changing anything.**

*The 84% figure is not the population.* `final_check` is 93% of wall on
`blending/1` and 71% on the biggest Heizmann file, but **14%** on
`miplib/pp08a-1000`, where **`theory_propagate` is 18.05 s of a 24.03 s budget
(75%) while offering zero literals**. And the whole `clock_synchro` family spends
**0.2–2%** of its budget inside the CDCL(T) driver at all — 51 ms of traced
stages against 24,266 ms of wall. Something outside the search owns those files'
time, and that is a **third census class nobody has looked at**.

*The "23 admission declines" are not admission declines.* Re-run after
[ADR-1752](../../research/09-decisions/adr-1752-the-lra-admission-cap-becomes-a-memory-budget.md),
all 22 no-trace files in the population report `kind=Timeout`; the memory budget
refuses **none** of them. The cap's justifying measurement (an 8 GiB abort,
2026-08-03) predates by three days the bound that caps the very cost it names
(`MAX_LRA_CACHED_COEFFICIENTS`, 2026-08-06) and was never re-taken.

**Landed.** An exact scan filter for `propagate_bounds` (output-equivalence
proved and mutation-checked, not an approximation); a narrowed `u64` GCD; the
atom count replaced by a byte budget with `SolverConfig::memory_limit_mb` as its
override; `smtcomp_cli --memory-limit-mb` and a `; give-up kind=… detail=…`
trace line, because the binary discarded `UnknownReason` entirely and a resource
refusal was indistinguishable from a timeout in every recorded run.

**Measured: 7 → 8 of 33 decided, zero verdict flips**, eight previously-decided
files 0.67–0.87x faster. The one gain is
`spider_benchmarks/no_op_accs.base.smt2` (unknown → unsat, 19.9 s).

**For the QF_NRA lane**, whose 62 losses sit behind the same cap: the shipping
budget is **640 MiB** per online-LRA construction (128 MiB of dense tableau,
512 MiB = 2,396,745 coefficients at 224 B). It refused **0 of 22** files at the
atom counts that class carries. What to watch is not the construction but the
**process** peak: 201 MiB to 8.7 GiB, median 759 MiB, with
`sal/tgc/tgc_io-safe-20.smt2` over 8 GiB — and `sc-11` already at 617 MiB
resident *at backend entry*, before the LRA route runs.

**Next, in order.** (1) The `clock_synchro` third class — 99.8% of a budget
outside the instrumented search, unexplained. (2) `miplib/pp08a-1000`: 30,443
refutations at a 138-literal mean core width over 527 live rows, i.e. lemmas that
each exclude close to one assignment. (3) The 617 MiB-at-backend-entry footprint,
which is upstream of everything this lane touched.

<!-- plan-section: landed-changes -->

| 2026-09-07 | lra-theory-side | `4acb9332f` — ADR-1752: the 1,024-atom cap becomes a byte budget derived into the existing coefficient ceilings, enforced deterministically from the builder's own counters, refusing with "projected N MiB > budget M MiB at K atoms over V variables". Also replaces the previous commit's Stein GCD (measured 1.77x SLOWER) with Euclid narrowed to `u64`, and gives `smtcomp_cli` `--memory-limit-mb` plus a give-up line. |
| 2026-09-07 | lra-theory-side | `aa6847be0` — `propagatable`, an output-equivalent scan filter for `propagate_bounds` (the scan was 75% of a 24 s budget on `miplib/pp08a-1000` for zero literals), mutation-checked in both directions. |
| 2026-09-07 | lra-theory-side | `a56c43639` — five engine counters splitting the `final_check` call count by outcome, core width, widening fallback and live rows, plus the assert-time partial check. No behaviour change; this is what falsified the census. |
