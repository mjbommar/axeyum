# Parity completion criteria — `are_we_done`

`are_we_done` prints `yes` only when ALL of the following hold, each verified by
a named command whose exit status depends on the finding.

1. **Formula simplification is ON by default in the shipping SMT path.**
   `InprocessOptions::default()` is not `OFF`, and the QF_BV route reaches it.
   Today: default is `OFF`; the SMT path calls `solve_with_drat_proof_within`,
   which skips inprocessing entirely.

2. **It pays for itself inside the competition budget (24s), not at 5x it.**
   Measured on the pinned parity corpus, net solved count strictly improves at
   the 24s limit. A win that needs 120s is not a win.

3. **The proof path survives it.** Every UNSAT with inprocessing enabled still
   emits a checkable proof; zero disagreements against the reference oracles.

4. **The gap closes on measured divisions.** Baseline 2026-09-08: we solve
   1,565 of the 1,892 our references solve across 12 divisions (gap 327).

5. **Every new algorithm carries instrumentation.** Counters are opt-in and
   clock-free, and the route attribution names the pass that consumed the
   budget -- not merely the last one that ran.

Criteria are falsifiable and each is checked by a command, not by inspection.
