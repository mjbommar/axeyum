# Lane: s1b-cdclt-heap-minimize — a VSIDS order heap and recursive learned-clause minimization for `CdclT`

<!-- plan-section: lane-status -->

**The QF_LIA −2 is not S1's. It is slice S2's `arith_dpll_admission_preflight`,
and it is a route-admission decline, not a boundary and not a trajectory
change** (`WIP`, s1b-cdclt-heap-minimize, 2026-09-06, plan slice S1b).

The two files QF_LIA lost between `9914a1c0e` (114/200) and `b32377dc52`
(112/200) are, both declared `unsat`:

- `QF_LIA/bofill-scheduling/SMT_real_LIA/ex3000_2400_100.smt2`
- `QF_LIA/bofill-scheduling/SMT_real_LIA/ex4320_2400_100.smt2`

Named by running the pre-S1 binary over all **29** reference-only rows of the
post-S1 `bench-results/parity-details/QF_LIA.tsv` (the pre-S1 sidecar no longer
exists on s5 — the parity queue script deletes `parity-details/*.tsv` before
each sweep and only the four divisions in `~/parity-out` were copied out). Two
of the 29 are decided by the BEFORE binary; 27 are `unknown` in both arms. That
is the whole loss, with no third file hiding behind a timing boundary.

Measured on an idle s5 (load 0.32, 16 cores, `taskset -c 0-7`,
`MEM_LIMIT_GB=8 timeout 29 … --timeout-ms 24000 --trace`), arms interleaved,
three repeats each — the numbers are stable to ±1 ms:

| file | arm | verdict | wall | trace line |
|---|---|---|---:|---|
| `ex3000_2400_100` | before | **unsat** | 8,115 / 8,116 / 8,115 ms | `boolean_propagate_ms≈8,045 theory_assert_ms≈8,019 theory_conflicts=1 decisions=0` |
| `ex3000_2400_100` | after | **unknown** | 109 / 108 / 107 ms | *(none — the theory layer never ran)* |
| `ex4320_2400_100` | before | **unsat** | 8,216 / 8,216 / 8,115 ms | `boolean_propagate_ms≈8,076 theory_assert_ms≈8,050 theory_conflicts=1 decisions=0` |
| `ex4320_2400_100` | after | **unknown** | 109 / 108 / 109 ms | *(none)* |

**109 ms is not a search and 8.1 s of a 24 s budget is not a boundary.** The
BEFORE arm refutes both files inside the *root* propagation fixpoint —
`decisions=0`, one theory conflict at decision level 0 — so no decision
heuristic and no clause minimization is on the path either way. Nothing S1
changed can turn that into a 109 ms decline, and the absent `--trace` line
proves `CdclT` was never entered in the AFTER arm.

`explain_corpus --json --timed-trace` on both trees names the cause in its own
words. AFTER:

```
"route":"lia-dpll","outcome":"declined","reason":"budget","detail":
"lazy linear arithmetic pre-SAT skeleton exceeds the joint resource boundary
 (atoms=2850, cnf_vars=6533, base_trigger=>1024/>4096,
  moderate_envelope<=1280/<=8192, initial_clauses=282, blocking_lemmas=0);
 declining before the online CDCL(T) probe
 (dispatch-overrun fix: admission evaluated before the reserve was spent)"
```

BEFORE, same counts, different stage: `"declining before the first SAT round"`.

So `exceeds_pre_sat_skeleton_boundary(2850, 6533)` was already true before S2;
what changed is **when** it is evaluated. `check_with_arith_dpll` used to run
`lia_theory::check_qf_lia_online_cdclt` *first*, and that probe — which, as
S2's own doc comment states, "has no size gate of its own" — refuted both
files in 8 s. S2's `arith_dpll_admission_preflight`
(`crates/axeyum-solver/src/dpll_lia.rs:1267`) now returns
`Unknown(ResourceLimit)` before the probe is ever launched, so the capability
the probe had on these two files is gone.

**Consequence for this lane and for S2.** This is a real, reproducible
capability loss of exactly two files, correctly attributed away from S1. It is
**outside S1b's reach**: the heap and the minimizer live inside `CdclT`, and on
these files `CdclT` is not reached at all. It belongs to the S2 lane, and the
shape of the fix is visible in the trace: the preflight should not decline a
query the online probe can still refute — e.g. gate the preflight on the online
probe having *also* declined, or bound the probe by a small reserve and decline
only after it. S2's own before/after measured six QF_IDL files and reported
"zero verdict changes"; the QF_LIA parity list was not in that population,
which is where the two files were spent.

<!-- plan-section: landed-changes -->

| 2026-09-06 | `pending` | Named the two QF_LIA files lost between `9914a1c0e` and `b32377dc52` by sweeping the pre-S1 binary over all 29 reference-only rows, and attributed the loss to slice S2's `arith_dpll_admission_preflight` rather than S1's watched literals: BEFORE decides both `unsat` in 8.1 s inside the root propagation fixpoint (`decisions=0`), AFTER declines in 109 ms with no theory-layer trace line at all, and `explain_corpus` prints the `lia-dpll` decline naming the dispatch-overrun fix by name. |
