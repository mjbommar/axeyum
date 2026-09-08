# Farkas certificate reuse in the lazy-SMT loop — 2026-09-08

Four sweeps of the same 22 `QF_LRA` files
(`../watchdog-blind-files-20260908/qf_lra_blind22/files.txt`), 24 s budget,
serial, `taskset -c 0-7`, on **s5** (idle, 16 cores). Read with
`scripts/trace-sweep-report.py <dir> "<label>"`.

| dir | binary | why it is here |
|---|---|---|
| `base_a` | `95c5ed7fa` | the baseline |
| `base_b` | `95c5ed7fa` | **the same-binary control.** Without it the A/B is a claim about the machine, not the change. 0.02% apart from `base_a` on wall, 2.0% on rounds, stage shares identical to 0.1 pp |
| `head` | `13ac968e4` | the fix |
| `head2` | `4b22a9629` | the fix after a behaviour-neutral extraction — the shipped code, and a second reading of the HEAD side's own noise (±10% on rounds) |

Headline: the Farkas re-derivation stage falls from 235,978 ms (48.6% of
accounted time) to 86 ms (0.0%), and the loop completes 1.63x the refinement
rounds in the same wall clock. Verdicts are identical in all four runs
(3 `unsat`, 19 `unknown`).

Full analysis, including the mutation control and the reason `verify()` alone
cannot gate reuse:
[`docs/research/12-performance/lra-farkas-reuse-2026-09-08.md`](../../docs/research/12-performance/lra-farkas-reuse-2026-09-08.md).
