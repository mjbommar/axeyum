# Protocol

What was measured, how, and which parts of it differ from the board this one
copies. The results are in [`README.md`](README.md); this file is the method, so
that a reader checking a number knows exactly what produced it.

Matches `bench-results/six-divisions-headtohead-20260912` (lane BOARD-SIX,
ADR-1950) and `bench-results/fpbv-divisions-headtohead-20260912` (lane
BOARD-FPBV, ADR-1941), with three deliberate differences recorded at the end.

## Population

Seven divisions, **200 files each**, sampled **FULL-SPAN** over index `0 .. N-1`
inclusive — 200 points evenly spaced, not the plain `N // 200` integer stride,
which stops at `199 * (N // 200)` and never reaches the tail.

| division | files on disk | pinned list |
|---|---:|---|
| AUFLIRA | 20,011 | `../parity-lists/AUFLIRA.txt` |
| UFNIA | 13,464 | `../parity-lists/UFNIA.txt` |
| ABV | 4,975 | `../parity-lists/ABV.txt` |
| ALIA | 3,098 | `../parity-lists/ALIA.txt` |
| AUFNIRA | 1,480 | `../parity-lists/AUFNIRA.txt` |
| AUFBV | 1,523 | `../parity-lists/AUFBV.txt` |
| FP | 2,669 | `../parity-lists/FP-fullspan.txt` |

Corpus root
`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/<DIVISION>`.

**The lists were committed at `3320c7136`, before anything was measured.** That
commit ordering is what makes the rows non-cherry-picked, and
`python3 mklist.py --dry-run` re-derives every list and reports whether the
committed file still matches the construction — so a reader can check it rather
than take the ordering on trust.

**FP's list has a different name on purpose.** `../parity-lists/FP.txt` already
existed and IS the plain integer stride — asserted in `mklist.py`, not assumed.
Other lanes' committed artifacts name that file, so overwriting it would
retroactively change what those boards say they measured. The protocol-conformant
list is `FP-fullspan.txt` and the stride list is left alone.

Full-span is not ceremony on this corpus. `mklist.py --dry-run` prints the family
coverage of both constructions; the stride would have reached **1 of ALIA's 2
families, 3 of AUFNIRA's 4 and 2 of AUFBV's 3**. Three of seven divisions would
have lost a whole family. The table is in [`findings/README.md`](findings/README.md).

## The measurement

- **24 s wall, 8 GiB address space** (`ulimit -v`), per run.
- **Three solvers interleaved per file**: all three finish file N before any
  starts N+1, on the same pinned physical core, so ambient drift cancels in the
  *difference*.
- **The first mover rotates** per file, so nobody systematically benefits from a
  cold or warm page cache.
- **Units differ and mixing them silently corrupts a board**:
  `z3 -T:24` is **SECONDS**, `cvc5 --tlimit=24000` is **MILLISECONDS**.
- **Wrapper timeout is 24 + 16 s**, and every run records its own outcome in a
  per-solver `*_k` column — `ok`, `wrapper-killed`, `rc134` (the 8 GiB cap), or
  `sigkill`. A previous census used +8 s under load, killed 17 processes, and
  manufactured 17 false "no reason" rows.
- **The row key is the PATH relative to the corpus root, not the basename.**
  Basenames collide across directories in these corpora.
- Solvers: axeyum built from this branch, z3 4.13.3, cvc5 1.3.4.
- Boxes s5 / s6 / s7, Ryzen 7 7840HS: **8 physical cores, SMT siblings at +8**,
  26 GB.

## The binary

`build.sh` builds from scratch into an empty target dir on this branch and
**refuses to publish a binary that is not newer than every `crates/**/*.rs`** —
the check is inside the build, not a thing to remember, because cargo decides
freshness by mtime and a stale prebuilt binary reported a false ABSENT four
times in this repository on 2026-09-12.

**No solver code changed in this lane.** It is a measurement lane; a board row
and a behaviour change in one branch cannot be told apart afterwards.

## The live probe

`probe.sh` runs on **every** host before any measurement and requires each of
the three solvers to decide at least one file across the seven divisions, with
the exact binaries and flags the board will use. A missing binary and a hard
division produce the identical TSV — BOARD-FPBV records z3 absent on a host once
and 800 files scoring a silent 0/200 that read exactly like a result. All three
hosts returned `PROBE-OK`, with identical verdicts.

## Placement, and the two collisions this lane caused

The board launched on BOARD-SIX's pins `0,8` and `2,10`. `loadframe.sh` reported
**3–4 foreign taskset pins within two minutes** and `ps -eo args` named them: a
concurrent `quant-rounds` lane on logical 0 and 2, and a `nested-array-ir` lane
on logical 4. **Logical 0 and 2 are the same PHYSICAL cores as `0,8` and
`2,10`**, so both shards were sharing a core with another lane's solver. The run
was stopped, its output deleted, and the board relaunched on cores 5 and 6.

Later, one shard's `CENSUS-DONE` was read as "the census is finished" and the FP
board was started on cores the other census shard still held. Caught when a
merge came up one row short; FP's single contaminated row was deleted and FP
relaunched.

Both are why `check-core-collisions.sh` exists, why `launch-shard.sh` and
`census-launch.sh` refuse to write into a non-empty output file, and why
`finish-division.sh` does the three post-completion steps in one place.

**Seven divisions over three boxes does not divide**, and the divisions are not
equally fast — AUFLIRA finished 200 files in nine minutes where UFNIA ran at
roughly 80 s per file. Rather than leave one box with a permanent overhang, slow
divisions were re-split across free cores with `reshard.sh` and placed with
`launch-shard.sh`. `merge-division.py` **discovers** however many shards exist
and **ABORTS** unless they cover the pinned 200 exactly, so re-sharding cannot
quietly shrink a denominator.

## The reference frame, derived rather than asserted

BOARD-SIX could write "foreign pinned jobs were ZERO in every one of 363
samples". **This lane cannot**: two other lanes ran pinned work on the same
boxes throughout. So the claim is narrower, and `frame-summary.py` derives it
from `loadframe.tsv` instead of asserting it:

> no job outside this lane ever held a **physical core** this board was using.

The `overlap` column alone is not sufficient after the re-balance — it tests the
*original* two pins, and this lane ended up holding eight cores, so its own
shards appear in `foreign_cores`. `frame-summary.py` subtracts the specs this
lane launched and examines the residue. Its `FRAME VIOLATED` branch is
unreachable on any run that gets published, so `controls/frame-control.sh`
forces it with fixtures whose answers are known, including a violation through
an SMT sibling and one through a range spec.

## The census

`census-run.sh` re-runs **axeyum only**, with `--trace`, over the **whole
winnable set** — every file where we returned `unknown` and at least one
reference decided — at the same 24 s / 8 GiB / pinned-core envelope, so a census
row is comparable to the board row it came from. Not a sample of the winnable
set: all of it. `census-merge.py` ABORTS unless the shards cover it exactly.

Three ADRs govern how it may be read:

- **ADR-1936** — a row whose dispatch did not reach the end of the ladder is
  UNCLASSIFIED and is never reported by its give-up reason.
- **ADR-1941** — `attempts=` alone cannot make that call; the discriminator is
  the **`route-open` segment**. Both readings are printed on every division.
- **ADR-1950** — a ranked "budget exhausted" reason carries `min/median/max` of
  budget REMAINING, and a `kind` (CLOCK / ROUND / SHAPE) that its own `ms_left`
  column can falsify.

This lane adds a fourth kind, **PARSE**, and a split BOARD-SIX did not need: a
front-door parse refusal arrives as `give-up kind=Error`, the same shape as an
internal error. BOARD-SIX excluded all of those from ranking, which is right for
a backend failure and wrong for a refusal of legal SMT-LIB — that is a
capability statement about the IR, and on these divisions it is the headline.
`is_internal_error` separates them and a mutant reverting the split is in the
table.

## Soundness

Every verdict **we** produce is checked three ways: the benchmark's declared
`:status`, z3, and cvc5. Per **ADR-1957** (written by this lane), the comparable
denominator is published per division, and when it is zero the line says so:

    DISAGREEMENTS: 0  <-- VACUOUS: nothing checked any verdict we produced

Any verdict nothing checked at the board budget is re-run against both
references at **600 s** — 25× — by `confirm-unchecked.sh`, into its own
artifact, and **that script's exit status depends on the finding**.

## The checkers can fail

`controls/` holds five suites and a mutation table. Every guard is paired with a
mutation of the thing it names and must die from it; every label has a fixture
in which it must appear and one in which it must not.

    controls/run-controls.sh              the three derivation scripts
    controls/loadframe-overlap-control.sh the OVERLAP column
    controls/core-collision-control.sh    the core-collision check
    controls/frame-control.sh             the reference-frame claim
    controls/integrity-control.sh         board / winnable / census agreement
    controls/mutants.py                   23 mutants, 23 kills

Three of these found real defects in their own subjects on the first run, and
none of the three was findable by running the subject over real data — the
details are in [`findings/README.md`](findings/README.md).

## Differences from BOARD-SIX, deliberate

1. **PARSE is a ranked census kind.** BOARD-SIX had no parse refusals in its six
   divisions and filed every `kind=Error` as an unrankable internal error. Here
   that would bury the headline.
2. **The vacuity marker (ADR-1957).** BOARD-SIX printed comparable counts on a
   separate line; all six of its divisions had dense ground truth, so the case
   never arose.
3. **Dynamic placement.** BOARD-SIX ran two fixed shards per box on hermetic
   boxes. This lane had neighbours and an odd number of divisions, so shards are
   placed by hand onto verified-free cores and the frame is derived afterwards.
