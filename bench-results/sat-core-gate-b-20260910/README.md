# Gate (b), re-run on a quiet box, 2026-09-10

Lane `E8-core-position`. This directory is the measurement behind
[ADR-1914](../../docs/research/09-decisions/adr-1914-phase-ds-entry-condition-is-not-met-and-the-phase-closes-unentered.md)
and
[the re-run note](../../docs/research/03-measurements/gate-b-rerun-and-phase-d-entry-2026-09-10.md).
It re-runs the [2026-09-05 gate (b) artifact](../sat-core-gate-b-20260905/)
that [ADR-1703](../../docs/research/09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
rests on, under the conditions that artifact says it did **not** have.

The 2026-09-05 artifact is a recorded measurement and is not edited. This one
sits beside it.

## What changed since 2026-09-05, and why a re-run was worth doing

| | 2026-09-05 | 2026-09-10 (here) |
|---|---|---|
| host load | `load average` 12-33 typical, one spike to 111 | see `load-*.log`; single-digit throughout, one pinned solver at a time |
| BatSat arm | present | **removed** (ADR-1910); the harness lost that arm and its `required-features` gate |
| external engines | built ad hoc in that lane | `cadical` 3.0.1 / `kissat` 4.0.4 from `scripts/provision-external-sat-referee.sh` |
| external driver | a Python script kept in that lane's scratchpad, never committed | `external_sweep.py`, committed here |

## Method

Deliberately the same shape as 2026-09-05 so the two tables are comparable.

1. **Corpora and DIMACS.** `crates/axeyum-bench/examples/dump_dimacs.rs`
   (unmodified) over the same two families, with the same seeded 100-file
   Noetzli sample (`noetzli-sample-seed20260905.txt` in the 2026-09-05
   directory). **213 of 213 files dumped, 0 failures.**
2. **Three engines, identical DIMACS, 20 s per instance, `taskset -c 0-7`, one
   engine at a time.** Native is `solve_with_drat_proof_within` through
   `gate_b_sweep sweep`; CaDiCaL and Kissat are external binaries through
   `external_sweep.py`.
3. **Every `sat` verdict is model-checked** by evaluating the model against the
   DIMACS formula with `CnfFormula::evaluate` — the native arm inside
   `gate_b_sweep sweep`, the external arms through `gate_b_sweep verify`, i.e.
   the same trusted code path in every case.
4. **`uptime` before and after every engine/family pair**, in
   `load-<engine>-<family>.log`.

## Files

- `external_sweep.py` — the external-engine driver (the 2026-09-05 equivalent
  was never committed).
- `analyze.py` — decided/PAR-2 aggregation, cross-engine disagreement scan, and
  the budget-boundary decomposition.
- `native-<family>.tsv`, `cadical-<family>.tsv`, `kissat-<family>.tsv` — raw
  per-engine sweep output.
- `load-<engine>-<family>.log` — `uptime` around each sweep.
- `summary.txt` — `analyze.py`'s output on this directory.
