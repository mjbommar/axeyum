# LEMMA-INPUT — pre-registration

Written **before** any measurement on this lane and before the lane's first
binary finished compiling. Branch base: `git merge-base main HEAD` is
`05410406886866fe7897c168f77c052b036a1353`, which **is** local `main`'s HEAD.

Target, handed over by [ADR-2075] §7(B) and §12.4: `refresh_initial_lemmas` is
**95.98 %** of `UFNIA/vcc-havoc/havoc-bench_sum.1.bar.smt2`, a row `z3` refutes
in **107 ms**. `MAX_INITIAL_BOUND_MUTEX_LEMMAS = 8_192` caps the lemmas FOUND,
checked inside the loop; its sibling sixty lines below caps its INPUT at 512
atoms with a `note_crossed` record.

## Rules

| id | rule |
|---|---|
| R1 | The population is DERIVED by script from a committed census plus this lane's own instrument; never typed. The derivation carries a positive control (the complement must be non-empty). |
| R2 | The instrumented build is an **attribution binary only**. No verdict, no A/B wall time, and no decision comes from it. Freshness by `find -newer`, not by exit status. |
| R3 | Every bucket is reported with its denominator. NOT-MEASURED is a separate row from zero. |
| R4 | Decision RULES are fixed below before the numbers exist. No conversion rate is pre-registered as a target. |
| R5 | **Exit status is its own channel**, reported separately from verdicts, on both arms. |
| R6 | A/B is **interleaved per file**: same file, same pinned core, arms back to back, order alternating per row, **one binary two env values**. Polarity is stated in the runner's own header. |
| R7 | Every moved row is re-run **3x per arm**. A **noise floor** is published from one whole division, same arm, repeated. The band is assumed non-zero until measured. |
| R8 | A control that must not move, shown **NON-VACUOUS** by naming the route binding its rows and verifying it executes there. If non-vacuity cannot be established, that is reported, not papered over. |
| R9 | New verdicts checked against independent authorities. `z3 -T:` is SECONDS, `cvc5 --tlimit` is MILLISECONDS. No-opinion counted separately; the **comparable denominator** is printed beside any zero. |
| R10 | Wilson 95 % on every proportion. |
| R11 | The A/B measures **this branch**. The post-merge value is predicted explicitly. |
| R12 | Any change claimed **output-preserving** must be proved so by a differential test that runs both implementations over generated inputs and compares the full output SEQUENCE, and the test must be shown to **die** under a mutation of the new path. Exactly one test dies. |
| R13 | No waiter greps for a process by a pattern its own command line contains. Waiters watch artifacts. |
| R14 | Any check not finished is reported as **"did not run"**. An intention is never written as an observation. |
| R15 | Analysis scripts run under `MEM_LIMIT_GB=16 scripts/mem-run.sh`; peak RSS per row is recorded. |
| R16 | If any route behaviour is selectable, all `dispatch/reason` fixture suites run, the list parsed out of `hooks/pre-push` so it cannot drift, every count nonzero. |
| R17 | **A cap on INPUT is a capability change**, not an optimisation: it is proposed only with the measured distribution of that input published first, and with its cost on currently-DECIDING rows measured ([ADR-2055]: an enforced cell cap cost 18 clean exits and turned one `sat` into an abort). |

## Decision rules

- **D1 — SHIP ON** only if the treatment arm **DECIDES** at least one row the
  base arm leaves undecided, with **3/3 passes agreeing**, **0 losses** (no row
  decided under base becomes undecided under arm), **0 verdict flips**, and
  **0 exit-status moves** on treatment and control.
- **D2 — gains = 0 ships OFF.** Faster-but-still-`unknown` is not a gain. A
  speed-only result is reported as a finding and the lever ships `Off`,
  whatever the ratio. ([ADR-2075] §8 is the precedent and it was right.)
- **D3 — an input cap is proposed only** if the measured input distribution
  shows the pass's input crossing the proposed number on at least one row of
  the treatment population, **and** the cap's cost on currently-deciding rows
  is measured. If an **output-preserving** change removes the cost instead, no
  cap is proposed and the reason is stated.
- **D4 — population membership** is: the instrumented binary attributes
  **>= 50 %** of the row's wall budget to the initial-bound-lemma pass
  (`initial_int_bound_mutex_lemmas` + `initial_int_bound_implication_lemmas`,
  measured together as `refresh_initial_lemmas`). The denominator is the set
  actually instrumented, stated every time.
- **D5 — "one row" is a complete lane.** If D4 selects exactly one row across
  the measured population, that is reported as the finding and no lever is
  built.

## Predictions

| id | prediction |
|---|---|
| P1 | D4 selects **>= 2** rows out of the 9-row [ADR-2075] bucket. |
| P2 | The binding input is the **CALL COUNT**, not the atom count: on `havoc-bench_sum` the max `ctx.atoms.len()` seen by the mutex pass is **below 512**, so a cap in the sibling's shape would **not fire at all** on the very row that motivates it. |
| P3 | Bucketing the pair loop by `expr` (which `conflicting_bounds` already requires to match) cuts the pair-loop iteration count by **>= 100x** on `havoc-bench_sum`. |
| P4 | With the pass made cheap, `havoc-bench_sum` still does **not** decide within 24 s — the 96 % is a symptom, not the whole cause. |
| P5 | At least one row **outside** the [ADR-2075] 9 is also refresh-dominated under D4. |
| P6 | An input cap of 512 atoms, if enforced on the mutex pass, costs **>= 1** currently-decided control row. |

[ADR-2055]: ../../docs/research/09-decisions/adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
[ADR-2075]: ../../docs/research/09-decisions/adr-2075-the-silent-hang-is-not-silent-it-is-the-inventory-of-code-that-polls-no-deadline.md
