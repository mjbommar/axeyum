# Lane: silent-hang — the bucket with "no route line at all" prints fourteen lines

<!-- plan-section: lane-status -->

**The second-largest unexplained bucket was a grep, not an absence** (`DONE`,
silent-hang, 2026-09-15, [ADR-2075]). [ADR-2040] §8 and [ADR-2050] §4(C) both
named "undecided rows with NO ROUTE LINE AT ALL" and both declined it.
`skeleton-reach`'s `fd-census.sh` greps `^; route `; the watchdog path prints
`; partial route `. The `; partial ` prefix is **deliberate** — `partial_line`
adds it so a consumer grepping COMPLETE lines cannot sweep a mid-search reading
into a total — and the census implemented only that half of the contract. Each
of these rows prints **fourteen** lines including a full route trail with
`bound_by=`, an open-segment line, and a live phase breadcrumb.

**R1 first: 4 of the 13 inherited rows are not in the bucket on current `main`**
(pre-registered P5 said at most 2 — wrong). The population is **9**, all
`UFNIA`. Read with the skipped line they split **four ways** — 3 `in=none`,
2 `euf:fc-pair-scan`, 2 `euf:offline`, 2 `euf:round-incremental-arith` — and the
`enters=` counter splits one label into two regimes nothing else could separate:
`dpll-lia:abstract` entered **163,583** times on one row and **5** on another.

**R6 answered by measurement.** Every profiled row is `R` at every one-second
sample with `utime` climbing ~101 ticks/s, and RSS **flat** (395,524 KB
unchanged across 48 s); population peak **527 MB**, so P3's >4 GB prediction is
wrong and "thrashing" is refuted for all 9. 24 s → 120 s decides **0 of 9**.

**The unifying finding came from a control that failed twice.** The solver's own
soft deadline normally beats the watchdog: **53 of 53 decided control rows
returned gracefully, 9 of 9 bucket rows did not.** This bucket is the inventory
of code paths that poll no deadline — which is also *why* there is no route
line, since a route is recorded on the way out.

Five `perf` profiles name five different answers (one reproduced across two
independently built binaries at 95.98 %/95.98 %), and four bounded sites:
`collect_eq_atoms` walking a DAG as a tree, `refresh_initial_lemmas`'s cap that
bounds its output but not its scan, `args_tuples_equal` missing the fast path
its 30-lines-up twin has, and SipHash in `quantifiers.rs` (checked for the
determinism defect — it does not have it).

**One lever built, ships `Off`, and NOT recommended `On`**: the A/B moved
**0 rows** (27 treatment runs over 3 passes, 53 control rows, 0 gains / 0 losses
/ 0 flips / 0 exit-status moves / 0 unstable). Its two tests were **both vacuous
on the first mutation run** — the fixture put the shared atom where one path
reached it; fixed, the mutation kills **exactly one**.

**The next lane's target is `refresh_initial_lemmas`**, not the lever: it is
95.98 % of a row **z3 refutes in 107 ms**, and its sibling pass sixty lines below
already demonstrates the input-cap-plus-crossing-record pattern to copy.

Gates on this branch: clippy **890/890 targets, 27/27 crates, 0 diagnostics**;
solver lib sweep **1785 passed**; `corpus_regression` 2 passed; all **19**
`dispatch/reason` fixture suites green; `progress_frontier` 12 passed (its five
`bench-results/frontier/*.json` reverted, not committed).

Artifacts: [`bench-results/silent-hang-20260915/`](../../../bench-results/silent-hang-20260915/).

[ADR-2040]: ../../research/09-decisions/adr-2040-the-reach-half-is-worth-two-and-the-whole-remaining-shape-is-the-ground-checker.md
[ADR-2050]: ../../research/09-decisions/adr-2050-the-eleven-are-four-causes-and-the-largest-is-one-refused-atom.md
[ADR-2075]: ../../research/09-decisions/adr-2075-the-silent-hang-is-not-silent-it-is-the-inventory-of-code-that-polls-no-deadline.md
