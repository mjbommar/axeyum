# Lane: qbudget — the quantified ladder's clocks, and the half nobody spends

<!-- plan-section: lane-status -->

**Lane qbudget (`DONE`, qbudget, 2026-09-13).** The follow-up [ADR-1970]'s own
handoff named: the `UFNIA`/`UFLIA` family that gives up with a third of its clock
unspent. It is measured, and it is a **negative result with a mechanism**.

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

**Hand that clock back and the family is 0 of 87.** `AXEYUM_QINST_EGRAPH_RETRY_SHARE=1`
is a genuine one-way ceiling — the retry takes the whole remaining ROOT deadline,
and nothing on that rung can grant more. Measured at the rung: 8.83 s → 16.17 s,
target-family median wall 15.3 s → 24.1 s. Decided: **0 of 87 rows across four
divisions**, Wilson 95 % `[0 %, 4.2 %]`. Those files are out of reach of every
budget policy on this rung.

| division | n | base | ceiling | net | gain | loss | flips |
|---|---:|---:|---:|---:|---:|---:|---:|
| UFNIA | 200 | 54 | 54 | +0 | 1 | 1 | 0 |
| UFLIA | 200 | 73 | 75 | **+2** | 2 | 0 | 0 |
| UF *(control)* | 200 | 90 | 90 | +0 | 0 | 0 | 0 |
| AUFLIA *(control)* | 200 | 86 | 86 | +0 | 0 | 0 | 0 |

0 disagreements and 0 sat↔unsat flips in 1,600 solves. Neither control is vacuous
(`q:uf-fmf-full` binds 26 of `UF`'s undecided rows, `q:mbqi` 65 of `AUFLIA`'s).
Noise floor, three base-arm runs of `UFNIA`: 54/53/53, **band 1 file** — and the
one churning file is the same one the A/B called a loss and the re-check called
UNSTABLE. After 3×-per-arm re-checks: **+2 confirmed, +1 unconfirmed (ADR-1957),
0 stable losses**.

**Ships OFF.** Every gain came from a *different* family, and the mechanism is
measured **non-monotone**: round admission consults the remaining budget
(`qinst_egraph.rs:2267`) and breaks to a final ground check, so the ceiling arm
admits **391 rounds and 787 ground terms** on `f2_rw120` and still refutes
nothing. **The vein is instance selection, not clock.** Sizing and decision rule
were pre-registered before any solver ran; the realised +2 falls in a gap the
rule did not specify, and both readings are recorded rather than one chosen after
the fact. [ADR-1995].

**Also measured, and the best-sized thing this lane touched:** the five `UFNIA`
rows that die in 107 ms on the `distinct` pair-expansion cap are **four files z3
refutes in 111–508 ms** (three of them cvc5 too, all four `:status unsat`). The
encoding is quadratic; we never reach a solver. Designed and handed off, not
implemented — see the artifact.

ADR: [ADR-1995](../../research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md)
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

| 2026-09-13 | qbudget | The quantified ladder's two give-up strings are **one root deadline and a slice inside it**, not two clocks — and the inner one is **`q:mbqi`'s, not `q:egraph`'s**: `prove_unsat_by_mbqi_inner`'s shape guard falls through to `prove_unsat_by_ematching`, which hands the **SKOLEMIZED** assertions back to the **SAME e-graph loop** under a 1/2 slice, so that loop runs **TWICE** per query. `AXEYUM_QPROBE` settles the starvation question by measurement rather than from a `(+N segments dropped)` rendering limit: the retry is **granted 8.83 s and spends 8.85 s**, cut off by its own slice with **8.7 s of 24 s left that nothing then spends** — the ladder runs out of **RUNGS**, not clock. Hand that clock back through a genuine one-way ceiling and the family is **0 of 87 across FOUR divisions** (Wilson 95 % `[0 %, 4.2 %]`), so those files are out of reach of **every** budget policy on this rung. A/B: `UFNIA` +0, `UFLIA` **+2**, `UF` and `AUFLIA` controls **0/0** with the route binding 26 and 65 of their undecided rows; **0 disagreements, 0 sat↔unsat flips in 1,600 solves**; noise band **1 file** (54/53/53) and the one churning file is the same one the A/B called a loss. **Ships OFF** — every gain came from a *different* family and the mechanism is measured **non-monotone** (the ceiling arm admits **391 rounds / 787 ground terms** on `f2_rw120` and refutes nothing). The vein is **instance selection, not clock**. Also: the five `distinct` pair-expansion refusals are **four files z3 refutes in 111–508 ms** that we never hand to a solver — designed, sized, handed off. And `cargo build --target wasm32-unknown-unknown` is **RED on main** in `axeyum-cnf` (a `std::time::Instant` vs `web_time::Instant` mismatch at `interrupt.rs:65`), not from this lane. ADR-1995 |
