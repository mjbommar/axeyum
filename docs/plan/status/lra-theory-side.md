# Lane: lra-theory-side — the QF_LRA theory side (final-check call count, atom-cap budget)

<!-- plan-section: lane-status -->

**`WIP`, lra-theory-side, 2026-09-07.** QF_LRA is 84 files behind the real
frontier after [ADR-1732](../../research/09-decisions/adr-1732-second-reference-per-division-not-a-replacement.md)
(Yices 181, cvc5 145, ours 97). This lane took the theory side. Full record,
including four hypotheses that were wrong and two plan premises that were false:
[the diary](../../research/12-performance/lra-theory-side-2026-09-07.md) and
[the measurement log](../../research/12-performance/lra-theory-side-2026-09-07-log.md).

**Measured: 97 → 98 of 200 and 7 → 8 of 33, zero losses, zero sat/unsat flips**,
with the commonly-decided files at 0.89x. The gain is
`spider_benchmarks/no_op_accs.base.smt2` (unknown → unsat).

**The census is wrong in two places, and counters found both before any change.**

*The 84% figure is not the population.* `final_check` is 93% of wall on
`blending/1` and 71% on the biggest Heizmann file, but **14%** on
`miplib/pp08a-1000`, where **`theory_propagate` was 18.05 s of a 24.03 s budget
(75%) while offering zero literals**. And the whole `clock_synchro` family spends
**0.2–2%** of its budget inside the CDCL(T) driver at all — 51 ms of traced
stages against 24,266 ms of wall. Something outside the search owns those files'
time: a **third census class nobody has looked at**.

*The "23 admission declines" are not admission declines.* Re-run at a generous
budget, all 22 no-trace files in the population report `kind=Timeout`; the
memory budget refuses none of them. Peak RSS across that class is 201 MiB to
8.7 GiB, median 759 MiB — and it is not the theory's: `sc-11` is at **617 MiB
resident at backend entry**, before the LRA route runs.

**Landed.** An output-equivalent scan filter for `propagate_bounds`
(mutation-checked in both directions); `gcd` narrowed to `u64` plus integer fast
paths; the Fourier–Motzkin fallback bounded in bytes for the first time
([ADR-1752](../../research/09-decisions/adr-1752-the-lra-admission-cap-becomes-budget-relative.md));
the atom count made **budget-relative** and reportable; `smtcomp_cli
--memory-limit-mb` and a `; give-up kind=… detail=…` line, because the binary
discarded `UnknownReason` entirely and a resource refusal was indistinguishable
from a timeout in every recorded run.

**The honest limit of the cap work.** Deleting the count outright was attempted
with three different cost models and the corpus refuted all three — retained
coefficients (7.8 GB abort), the dense tableau (refused a file the fallback
decides in 0.18 s), and Fourier–Motzkin's own allocations bounded in place
(still 7.8 GB on `miplib/danoint-266`). With no `#[global_allocator]` hook
nothing here can attribute an allocation it did not make. So the count survives
as a conservative screen calibrated to reproduce `1_024` **exactly** at the
default budget — the shipped build cannot regress — while now moving with
`SolverConfig::memory_limit_mb`.

**For the QF_NRA lane**, whose 62 losses sit behind the same cap: the knob now
works. `--memory-limit-mb 8192` admits 13,107 atoms where no amount of memory
previously bought one past 1,024, and a refusal names the count, the budget and
the remedy. What to watch is the **process** peak, not the construction: the
numbers above, plus one file over 8 GiB. Do not expect admission alone to decide
files — on this division it decided none.

**Next, in order.** (1) The `clock_synchro` third class — 99.8% of a budget
outside the instrumented search, unexplained. (2) Where `miplib/danoint-266`'s
7.8 GB goes; that answer is what a real cost model needs. (3)
`miplib/pp08a-1000`: 30,443 refutations at a 138-literal mean core width over
527 live rows, i.e. lemmas that each exclude close to one assignment.

<!-- plan-section: landed-changes -->

| 2026-09-07 | lra-theory-side | `ad2b40370` — three cost models, three corpus refutations, recorded with file names and numbers; the atom count returns as a budget-relative screen calibrated to reproduce `1_024` exactly at the default budget, so the shipped build cannot regress. |
| 2026-09-07 | lra-theory-side | `6a37b934d`, `c615e835b` — the Fourier–Motzkin fallback bounded in bytes at its entry and per elimination step, the latter checked BEFORE the loop that clones a length-`n` multiplier vector per row. `MAX_FM_CONSTRAINTS` capped a count whose bytes were unbounded. |
| 2026-09-07 | lra-theory-side | `4acb9332f` — ADR-1752's budget machinery: ceilings derived from bytes, `SolverConfig::memory_limit_mb` as the override, refusals that state their numbers. Also replaces the previous commit's Stein GCD (measured **1.77x slower**) with Euclid narrowed to `u64`, and gives `smtcomp_cli` `--memory-limit-mb` plus a give-up line. |
| 2026-09-07 | lra-theory-side | `aa6847be0` — `propagatable`, an output-equivalent scan filter for `propagate_bounds` (the scan was 75% of a 24 s budget on `miplib/pp08a-1000` for zero literals), mutation-checked in both directions. |
| 2026-09-07 | lra-theory-side | `a56c43639` — five engine counters splitting the `final_check` call count by outcome, core width, widening fallback and live rows, plus the assert-time partial check. No behaviour change; this is what falsified the census. |
