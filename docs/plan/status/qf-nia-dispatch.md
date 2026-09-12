# Lane: qf-nia-dispatch — QF_NIA's largest gap, re-censused and closed by one side-constraint

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, qf-nia-dispatch, 2026-09-12).**

**Task.** QF_NIA was the largest single-division gap on the 2026-09-11/12 board:
41 of 200 against z3's 144, **110 winnable**, gap **+103**. Two leads were
already closed by measurement (width escalation, ADR-1921; CNF clause budget,
note 118). The remaining largest class was `preprocessed dispatch timeout after
reduced solve` at 41 of 110 — and ADR-1925 had just proved that sentence is a
**relabel** that in QF_NRA concealed the CAD wall on 13 of 18 files. So the
census had to be re-run before anything was built.

## What the re-census found (all 110, not a sample) — `ab0c11110`

[`bench-results/qf-nia-dispatch-20260912/`](../../../bench-results/qf-nia-dispatch-20260912/README.md).
0 of 110 hit the 180 s wall, 0 reasonless rows, and 103 of 110 ran the full
19-rung dispatch (`attempts=` against the ladder length), so no early rung's
refusal became a file's answer.

| honest cause | files |
|---|---:|
| `integer bit-blast width ladder: wall-clock timeout reached` | **41** |
| `estimated N CNF clauses before lowering exceeds budget N` | 31 |
| `bounded integer model overflowed at width 32` | 25 |
| watchdog / scalar-backend clock / constant-width / ingest / in-range unsat | 13 |

**The QF_NRA finding did not repeat.** All 44 carrier rows decompose into the
same bit-blast route the census already named. The relabel cost QF_NIA its
precision, not its diagnosis — a null worth recording, since a general rule held
in one division and not the next.

## Two measured negatives and one measured positive

- **More budget for the ladder: no.** The 41 ladder-clock files at **150 s**
  (6.25x) decide **1 of 41**.
- **ADR-1921's standing hypothesis: RIGHT.** `blast_integers` pinned `int_mul`
  against overflow and **nothing else**, so the surviving replay failures were
  ADDITIVE wraparound — which is why widening could never fix them.
- The fix is one side-constraint on `int_add`/`int_sub`/`int_neg`
  ([ADR-1937](../../research/09-decisions/adr-1937-the-blaster-pins-products-and-nothing-else-and-the-wraparound-is-additive.md)),
  and it **ships on**.

Interleaved per-file A/B, one binary, arms alternating, whole 200-file division:
**39 decided → 78**, 40 gains, **0 real losses**, 0 verdict flips, wall
**−10.2 %** (faster — the constraint removes wrapping models the replay was going
to reject anyway). Against the board's own 41, on equal footing, **41 → 80 of
200**, closing **39 of the 103-file gap**.

Cost on 298 already-decided files across nine integer-bearing divisions: 0 real
losses, 0 flips, **+1.9 %** wall. All four single-pairing surprises were re-run
serially and **every one was a load flake**; raw and re-checked numbers are both
in the README. Soundness: **78 verdicts, 0 disagreements** against `:status`, z3
and cvc5, with the checker verified able to fail (78 under a flip control).

## What is next for QF_NIA

Not the width family — ADR-1921 closed widening and ADR-1937 closed what it was
standing in for. The two classes left are the **CNF clause budget** (31, already
a measured negative on lifting the gate) and **`nia-linearize` consuming a budget
it then cannot use**: it is `bound_by` on 49 of 110 files while 30 of those end
in an *instantaneous* pre-lowering size refusal. That is a scheduling question,
not a capability one, and it is the next lead.

<!-- plan-section: landed-changes -->

| 2026-09-12 | `ab0c11110` | QF_NIA: re-census of all 110 winnable files after the ADR-1925 relabel fix — the carrier decomposes and hid nothing; ladder wall-clock 41, CNF budget 31, width-32 replay overflow 25. |
