# Lane: nra-admission-bound — the NRA cross-product admission bound

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS`, nra-admission-bound, 2026-09-07).**

**Task.** The QF_NRA loss census
(`bench-results/parity-losses-20260906/QF_NRA.census.tsv`) attributes 62 of 77
reference-only losses (80.5%) to one cause: `nra.rs`'s deterministic
cross-product admission bound of 2. Establish **what the bound protects**
(time, memory, or soundness) before changing it, then raise or replace it with
a measured budget — or report that the bound is correct and the 62 files need
a different route.

**Non-negotiable outcomes.** Zero disagreements with the reference; zero
verdict regressions on the 110 files QF_NRA currently decides; every new `sat`
replays against the original term, every new `unsat` carries the evidence its
route can produce.

**Where the work is recorded.**
`docs/research/12-performance/nra-admission-bound-2026-09-07.md` — the diary,
carrying the archaeology, the measurement plan fixed before the data, and each
measurement as it lands.

**Step 0 (done).** Archaeology. The bound was introduced by `9a8b09220`
(2026-06-19) as an **OOM guard**, not a soundness or time guard: its commit
message records that ≥3 cross-products drove the DPLL(T)/exact-rational LRA
relaxation to exhaust memory *inside a single solve call*, so the wall-clock
checks never ran. Independently confirmed from the code that admission gates
*reachability* only — the relaxation transfer (`unsat` only) and the replayed
`sat` guard are both independent of the count — so **raising the bound cannot
produce a wrong verdict; it can only cost memory or time**. Three commits
landed since on exactly the mechanism the 2026-06 claim names (deadline
threading `4c2dc2524`/`3d9be6e99`, the generic CDCL(T) spine `487fecea9`, the
exact-polynomial fallback bound `68a3c8551`), so the premise must be
re-measured rather than inherited.

**Next.** Q1: re-run the 3-cross-product shape the bound was built for with
the cap lifted, under `ulimit -v`, and record which of {memory abort, graceful
wall-clock, decides} actually happens.

## Landed changes

| when | what | commit |
|---|---|---|
| 2026-09-07 | Lane opened: archaeology of what the admission bound protects, and the measurement plan fixed before the data | (this commit) |
