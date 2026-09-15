# TIMEOUT-DIAGNOSIS — pre-registered decision rules (ADR-2060)

Written and committed **before** the binaries were built and before a single
file was run. Nothing below is revised after the fact; anything that had to
change is added as a dated amendment with its reason.

Lane: `timeout-diagnosis`. Branch base: `git merge-base main HEAD` is
`91c721f8eda678e40124e089d6761ce3d3d02f94`, which **is** local `main`'s HEAD.

## What the change is, and therefore what is being tested

`Decision::TimedOut` was a unit variant rendered as one fixed sentence about the
Fourier–Motzkin elimination for all six of its producers. It is now
`Decision::GaveUp(GaveUp)` with a reason per gate, and the one producer that was
an `i128` overflow (`ctx.overflow`) is `Decision::Incomplete` instead. Three
cause-erasing chokepoints below it (`eliminate`, `simplex_fallback`,
`collect_constraints`) now return typed causes instead of a bare `None`.

**Every routing decision is unchanged by construction.** The watchdog keeps its
precedence over clock/size/overflow bails in `solve`; the collection decline
keeps the deadline-outranks-watchdog precedence the caller's re-read gave it;
`Feasibility::Declined` still hands the cube to the simplex exactly where
`Feasibility::TimedOut` did. So the registered prediction is:

> **Verdict-neutral: 0 gains, 0 losses, 0 flips, and no exit-status move.**

This is a diagnosis fix. **No capability lever is attached to it**, and the lane
is not measured in files decided.

## R1 — arms and polarity

- **BASE** = `smtcomp_cli`, `--release`, built from `main` @ `91c721f8e`.
- **ARM** = `smtcomp_cli`, `--release`, built from this lane's branch HEAD.
- A **GAIN** is "the ARM decided (`sat`/`unsat`) a file the BASE did not"; a
  **LOSS** is the reverse. The ARM is the one carrying the split variant.

**Two binaries, not one binary under two env values.** The standing rule prefers
one binary because a second build confounds the arm with everything else that
changed between them; here there is nothing else — the two snapshots differ only
by this lane's commits — and the change is unconditional code with no knob to
flip, so a one-binary A/B is not available. Both are built `--release` from
`scripts/lane-snapshot.sh` extractions (which `--touch`, so the stale-mtime trap
cannot make a build silently reuse the other arm's objects), and each binary's
identity is checked by `sha256sum` before launch — two arms that hash the same
would make the whole comparison vacuous and the runner refuses.

Both arms run with `--trace`, so the give-up channel is captured for both and
the verdict comparison is between two runs that are identical in every respect
but the binary. ADR-2045 measured on this exact board, budget and commit that
`--trace` perturbs **0 of 200 rows**.

## R2 — channels, and which must move

Three channels are recorded per file per arm. The point of naming them in
advance is that ADR-2045's lever read `losses=0` on the verdict channel while
creating **five new aborts** on files that had terminated cleanly.

| channel | rule |
|---|---|
| **verdict** (`sat`/`unsat`/`unknown`/`none`) | **MUST NOT MOVE.** Any move is a finding and is reported per file, never netted. |
| **exit status** (`0`, `124` wall kill, `134` abort, other) | **MUST NOT MOVE.** A file that exits 0 in one arm and aborts in the other is a regression even at net 0 verdicts. |
| **give-up detail** (`; give-up …`) | **MUST MOVE.** This is the change. If it moves on **zero** rows, the two binaries are the same binary and the A/B is vacuous — the run is discarded and re-taken, not reported. |

The third row is the **non-vacuity demonstration**, and it is a mechanism proof
rather than a statistical one: the ARM's own new sentences are what appears.

## R3 — soundness

Any file where the two arms return **opposite verdicts** (`sat` vs `unsat`), or
where either arm disagrees with the benchmark's `(set-info :status …)`, is
reported as a soundness finding regardless of count, at the top of the result,
with its denominator.

## R4 — denominators printed beside every zero

Every zero is printed with what it is a zero *out of*:

- rows where **both** arms emitted a parseable verdict line;
- rows where **both** arms exited `0`;
- rows carrying a `:status` annotation, for the soundness check;
- the count of decided rows in each arm separately.

A zero over a denominator of zero is not a null result and will be labelled as
"nothing comparable" rather than as agreement.

## R5 — small-n intervals

Any rate reported below n = 100 carries a **Wilson 95 % interval**. A net of 0
gains out of *n* comparable rows is reported as `0/n, Wilson 95 % [0, u]` and
the upper bound is quoted, because "0 of 50" and "0 of 200" are different
claims.

## R6 — noise floor

The row-level noise floor for this board, this budget and this harness was
measured by ADR-2045 one day earlier at the merge-base commit: **0 of 200 rows
differ over two identical passes**. It is cited rather than re-measured, and
that citation is stated wherever the floor is used. If this run shows any
verdict move at all, the floor is re-measured before the move is attributed to
the change.

## R7 — compute

At most **4 pinned pairs**, named: `s5 0,8`, `s5 1,9`, `s6 0,8`, `s7 0,8`. Two
shards on s5 and one each on s6/s7, because the undecided rows on this division
reach ~7.8 GiB against 26–27 GiB hosts. The 200-file board is round-robined into
4 shards so no shard gets a whole benchmark family. Arms alternate order per
file (`base` first on odd rows, `arm` first on even), so ambient load cancels in
the difference.

## R8 — what would make me report a failure

- Any verdict move in either direction → reported per file with its detail
  strings from both arms, and the ADR's claim of verdict-neutrality withdrawn.
- Any exit-status move → reported per file, same consequence.
- A give-up-detail channel that does not move → the run is vacuous and is
  discarded, not reported as "no regression".
- A shard that does not complete → reported as **"did not run"** for its files,
  and its files excluded from every denominator, which is then printed smaller.

## R9 — what this lane will NOT do

It will not attach a capability lever to make the number look better, and it
will not report a decided-file count as an outcome. The deliverable is a
correct, pinned diagnosis with verdict-neutrality **measured**.
