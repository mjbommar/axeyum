# QF linear A5 IDL monotonicity v1 preregistration — 2026-08-11

## Stop condition

The fresh V2 QF_IDL capture from exact clean pushed source
`d0e0d6ceac779b5cc3e2c1b5f3096c77780aecf9` completed 200/200 rows with exit
0 and zero stderr, but its strict join found two historical decisions missing.
`BubbleSort_safe_blmc016.smt2` moved from UNSAT to a construction-deadline
`unknown`; `rand_15_75_1235849326_0_k=3_v=7_e=30_sat.gph.smt2` moved from SAT
to a pre-SAT resource `unknown`. Two unrelated UNSAT gains hid the losses in the
unchanged aggregate 68/200 count. The named `lpsat-goal-18` control retained
UNSAT. QF_RDL and complete derivation are forbidden.

The two lost cases are exactly the gains retained by the 2026-08-06 adaptive
difference-logic probe/fallback repair. The BubbleSort trace spends its DL probe
budget, then times out while building a 1,812-atom Boolean abstraction. The
GraphPartitioning trace spends its probe budget, then declines at 2,199 atoms
and 14,670 CNF variables under the later pre-SAT safety boundary. That is enough
to identify two candidate boundaries, but not enough to change either one.

The raw stream, capture metadata, and failure summary are retained as
[`V2-QF_IDL-monotonicity-attempt-001.axeyum.jsonl`](evidence/qf-linear-a5/failures/V2-QF_IDL-monotonicity-attempt-001.axeyum.jsonl),
[`capture metadata`](evidence/qf-linear-a5/failures/V2-QF_IDL-monotonicity-attempt-001.capture.json),
and [`failure metadata`](evidence/qf-linear-a5/failures/V2-QF_IDL-monotonicity-attempt-001.failure.json).
They and the incomplete V2 sequence remain non-credited.

## Frozen observation matrix

Run three sequential isolated observations of each of four exact files with the
same release binary, shipped configuration, 24,000 ms query timeout, inherited
8 GiB address-space limit, 24-core host, and one-minute group-start load at most
12:

1. both lost controls above;
2. `maze-generation-width=16-height=16-density=0.01-run=1.smt2`, the new UNSAT
   gain; and
3. `lpsat-goal-18.smt2`, the established UNSAT probe/fallback control.

Each observation must run in a fresh worker, exit 0, emit one identity-matching
JSON record and zero stderr, and retain wall time and peak RSS outside the
product stream. No source, binary, timeout, cap, route order, or environment
change is permitted in this stage.

## Interpretation and next boundary

- A lost case that decides correctly in all 3/3 isolated observations is
  classified as aggregate wall-clock instability. Do not change solver code;
  preregister whether a fresh full QF_IDL restart is justified.
- A loss reproduced as `unknown` in all 3/3 observations is deterministic enough
  for a separate mechanism-specific preregistration. BubbleSort may then test
  probe/fallback allocation; GraphPartitioning may test a bounded first-round
  path that cannot cross the existing allocation-abort boundary unchecked.
- Mixed outcomes stop without a solver change and require a stability-focused
  follow-up.
- Any wrong verdict, process failure, stderr, malformed output, or named-control
  loss stops immediately.

No diagnostic result authorizes production retention, a 200-row restart, QF_RDL,
or a breadth claim. Any behavior-changing experiment invalidates the current
captures and requires all three divisions to restart from QF_LRA after its own
preregistration, focused controls, exact push, and complete release gate.
