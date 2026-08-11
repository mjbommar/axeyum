# QF linear A5 IDL extended DL slice v1 preregistration — 2026-08-11

## Decision boundary

The [G1 result](qf-linear-a5-idl-loss-mechanism-v1-result-2026-08-11.md) and
[D2 result](qf-linear-a5-idl-bubble-d2-result-2026-08-11.md) show the unchanged
DL route deciding both lost QF_IDL cases under the 32,000 ms diagnostic:
GraphPartitioning SAT in 18.82--19.19 seconds and BubbleSort UNSAT in
17.42--20.52 seconds. The shipped 24,000 ms policy caps ordinary DL work at 18
seconds. B1 failed, so fallback atom admission is not a supported repair.

This note authorizes one structural 21/3 maximum-slice candidate. It does not
authorize benchmark-name routing, a pre-SAT boundary change, an aggregate
census, QF_RDL measurement, or credit.

## Candidate mechanism

Preserve the current standard probe budget exactly:
`timeout - min(timeout / 4, 6 seconds)`. Add a separately computed extended
budget of `timeout - min(timeout / 8, 3 seconds)`. After the existing complete
DL scan, select:

1. the existing equality-heavy shortening when there are at least 128 numeric
   equality gates and at most 1,024 difference atoms; its 24-second allocation
   must remain exactly 12 seconds;
2. the extended budget only when there are more than 1,024 difference atoms
   and fewer than 128 numeric equality gates; or
3. the standard budget for every other admitted shape.

At the production setting this gives only the selected large, non-equality-
heavy shape 21 seconds and retains at least three seconds before fallback.
Selection is a stable predicate over the existing scan, not a filename, logic
label, verdict, host state, or elapsed-time observation. Do not change scan
semantics, route order, model replay, checked negative-cycle conflicts,
deadlines, pre-SAT caps, or public APIs.

Focused tests must cover zero, short, 24-second, and unbounded configurations;
the two structural thresholds; unchanged 12-second equality behavior; and
unchanged standard behavior on compact gate-free and large equality shapes.

## Target and immediate controls

Build one fresh release candidate from the exact clean topic. At group-start
load at most 12, run fresh isolated 24,000 ms / 8 GiB observations with exact
JSON identity and zero stderr:

| Role | File | Required outcome |
|---|---|---|
| lost target | `BubbleSort_safe_blmc016.smt2` | UNSAT through `dl-online` in 3/3 |
| lost target | `rand_15_75_1235849326_0_k=3_v=7_e=30_sat.gph.smt2` | replay-checked SAT through `dl-online` in 3/3 |
| fallback control | `lpsat-goal-18.smt2` | UNSAT in 3/3, no route requirement |
| retained gain | `maze-generation-width=16-height=16-density=0.01-run=1.smt2` | UNSAT in 3/3, no route requirement |

Stop on the first target miss, control loss, wrong verdict, stderr, malformed
record, identity mismatch, process failure, or 8 GiB breach. Gains cannot offset
losses. Retain exact source/binary identity, trace, timing, RSS, exit status,
stderr size, and output digest.

## Complete retention gate

If and only if the immediate matrix passes, derive exact lists from the
committed historical authorities and compare the candidate against the
unchanged `d0e0d6cea` binary on all currently retained decisions: 68 QF_IDL and
105 QF_RDL rows. Every historical SAT/UNSAT verdict must remain identical;
every candidate SAT must replay; zero stderr and process failures are allowed.
Also rerun the original `pursuit`, `tgc`, and 31,944-variable Maze pre-SAT
allocation controls, which must remain typed pre-SAT declines with zero SAT
rounds.

Then require format, strict all-feature solver Clippy, the complete solver
library, deep-input tests, online arithmetic/CDCL(T) integrations, and both
QF_IDL/QF_RDL-relevant differential suites. Amend ADR-0375 only after all
candidate evidence passes. A complete uninterrupted external-frontier
`just check` on the exact pushed candidate is required before any V2 restart.

Failure removes the candidate and records a negative result. Success still
does not credit the old captures: restart QF_LRA row 1, strict-join it, then
QF_IDL, strict-join it, and only then run QF_RDL and derive the divisions.
