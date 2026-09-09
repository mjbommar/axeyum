# Ladder budget discipline, 2026-09-08

Artifacts for
[`docs/research/12-performance/ladder-budget-discipline-2026-09-08.md`](../../docs/research/12-performance/ladder-budget-discipline-2026-09-08.md).

## The `QF_ABV` A/B

Three arms over the whole committed 200-file `QF_ABV` division list, run
**concurrently on s6** from ONE pinned binary
(`sha256 83d0e50b43fb139843d558db761357bcb7f68d4e89114201752b6c8e125f2909`),
24 s and 8 GiB per file. Every TSV records the binary digest, the policy and the
load average it started under, because a sweep that reads `target/release/…`
while a build is writing it changes solver mid-run and nothing in the file would
say so.

| file | arm |
|---|---|
| `off-a-QF_ABV200.tsv` | `AXEYUM_ABV_ONLINE_RESERVE=off` — the historical behaviour |
| `off-b-QF_ABV200.tsv` | the same arm again: the same-binary control |
| `on-QF_ABV200.tsv` | the shipped default (a quarter reserved for the array ladder) |

```sh
python3 analyze.py off-a-QF_ABV200.tsv off-b-QF_ABV200.tsv on-QF_ABV200.tsv
python3 overrun.py off-a-QF_ABV200.tsv off-b-QF_ABV200.tsv on-QF_ABV200.tsv
```

Result: **+0 / −0, zero disagreements, 186 decided in every arm**, and
**14 files that were decided only past the 24 s budget are now decided inside
it**. Runs exceeding the budget: 24 → 10, and all ten remaining are `unknown`.

## The tableau-cell measurement

`cells-QF_LRA200.tsv` is the committed 200-file `QF_LRA` list run on **s7** with
an instrumented binary (`lra-cells.patch`, applied to `lra::simplex_fallback`,
`AXEYUM_LRA_CELLS=1`) that prints the size of every tableau `simplex::feasible`
builds. It answers what a cell bound in `feasible` would refuse, before changing
default admission.

```sh
python3 cells.py cells-QF_LRA200.tsv
```

Result: 36 of 200 files reach the fallback (3,129 calls); **7 build a tableau
over `MAX_TABLEAU_CELLS`, and all 7 end `unknown`**; the largest is 8,797,712
cells (282 MB), not the 360 million the earlier reading found, because
`lra::simplex_admission` now prices the allocation first. The bound was NOT
added — see §5 of the note.

## The guards, against their own removal

`mutate.sh reserve|handroll|inversion` applies one mutation in an isolated
worktree with a restoring trap, asserts its own anchor is present first, and runs
the whole `--lib --features full` suite. Baseline: 1,609 tests, all green.

The `inversion` arm is the one worth reading: on the first version of this
lane's code it killed **nothing**, which is how both the registry FINDING's
overstated reach and a wider inversion introduced by the fix were found.
