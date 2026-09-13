# Lane: qbudget — the quantified ladder's clocks, and the half nobody spends

<!-- plan-section: lane-status -->

**Lane qbudget (`IN PROGRESS`, qbudget, 2026-09-13).** The follow-up
[ADR-1970]'s own handoff named: the `UFNIA`/`UFLIA` family that gives up with a
third of its clock unspent. Three things are established and one is being
measured.

**The budget architecture is one root deadline with sibling slices cut out of
its remainder, not two clocks.** `finish_quantified_solve` threads one
`deadline` through every rung; each rung re-derives *what is left of the root
clock* through `config_with_remaining_timeout`, and some then cut a
`LadderSlice` out of that remainder. So
`quantified solve time budget exhausted after e-matching` is the ROOT deadline
passing, and `e-matching: instantiation time budget exhausted` is a rung's own
slice expiring strictly inside it — which is why the second family's rows stop
with root clock left.

**The second string is not `q:egraph`'s.** That rung *declines* its `Unknown`,
so it cannot be the final give-up. It is `q:mbqi`:
`prove_unsat_by_mbqi_inner`'s shape guard falls through to
`prove_unsat_by_ematching`, which hands the **Skolemized** assertions back to the
**same e-graph loop** under a 1/2 slice. The e-graph instantiation loop therefore
runs **twice** on these queries, and between them they are the clock.

**The starvation question is answered by measurement, not by reading a truncated
trace.** `AXEYUM_QPROBE=1` on four files of the family:

    wall 15,316 / 15,222 / 15,320 / 15,217 ms of 24,000
    skolemized-egraph  budget=8.83 s  elapsed=8.85 s  -> its own slice, not the deadline
    mbqi-shape exit=quantifier-below-top-level

**No rung is starved by a rung that cannot decide. The ladder runs out of RUNGS
with 36 % of the budget unspent** — the half-slice is reserved for
`q:uf-fmf-full`, which declines a non-pure-UF query in one cheap scan and hands
it back to nobody. And backing out the arithmetic puts `q:egraph` at ~3.3 s on
this family, so ADR-1970's "the e-graph rung eats the quantified clock" is a true
sentence about a **different** family — the census's own `bound_by=q:mbqi` on 27
of 37 rows said so.

**`AXEYUM_QINST_EGRAPH_RETRY_SHARE` ships OFF** and its `=1` ceiling arm is the
one-way sizing instrument: no budget policy on that rung can grant the loop more
than the root deadline it sits inside. The A/B is running; the sizing and the
decision rule were pre-registered before any solver ran, and the ADR is
[ADR-1995].

**Also measured, and the best-sized thing this lane touched:** the five `UFNIA`
rows that die in 107 ms on the `distinct` pair-expansion cap are **four files z3
refutes in 111–508 ms** (three of them cvc5 too, all four `:status unsat`). The
encoding is quadratic; we never reach a solver. Designed and handed off, not
implemented — see the artifact.

ADR: [ADR-1995](../../research/09-decisions/adr-1995-the-egraph-retry-is-cut-off-by-its-own-half-slice-and-the-reserve-is-spent-by-nobody.md)
· artifact: [`bench-results/qbudget-20260913/`](../../../bench-results/qbudget-20260913/README.md)

## Compute

s5 and s6, four core pairs each (`1,9` `3,11` `5,13` `6,14`), 8 shards. `s7` left
free apart from short single-core probe runs.

## Branch point

Branched at `c73eb8adf`, merged local `main` at `7276aaa7a`.
`git merge-base main HEAD` is `e542fdc3d`, which **is** `main`'s HEAD, so the
base arm measures the tree that ships. (`origin/main` is `76f4f22c6`; local
`main` is one bench-results commit ahead of it.)

<!-- plan-section: landed-changes -->

| 2026-09-13 | qbudget | The quantified ladder's two give-up strings are **one root deadline and a slice inside it**, not two clocks — and the inner one belongs to `q:mbqi`, not `q:egraph`: `prove_unsat_by_mbqi_inner`'s shape guard falls through to `prove_unsat_by_ematching`, which hands the **Skolemized** assertions back to the **same e-graph loop** under a 1/2 slice, so that loop runs **TWICE** per query. `AXEYUM_QPROBE` on the family: the retry is granted **8.83 s** and spends **8.85 s** — cut off by its own slice with **8.7 s of 24 s left**, which **nothing then spends**, because the reserve is held for `q:uf-fmf-full` and that rung declines a non-pure-UF query in one cheap scan. **The ladder runs out of RUNGS, not clock.** The arithmetic also puts `q:egraph` at ~3.3 s here, so ADR-1970 describes a different family — as its own `bound_by=q:mbqi` on 27 of 37 rows said. Lever `AXEYUM_QINST_EGRAPH_RETRY_SHARE` ships OFF with a one-way ceiling arm; sizing pre-registered before the first solver run. Separately: the five `distinct` pair-expansion refusals are **four files z3 refutes in 111–508 ms** and we never reach a solver — designed, sized and handed off. ADR-1995 |
