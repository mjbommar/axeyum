# The LRA atom screen: does raising it decide any of ADR-2111's 32, now that the tableau is sparse?

Status: **MEASURED** on QF_LRA, QF_UFLRA, QF_LIA, QF_RDL; QF_IDL in progress
(see `docs/plan/status/lra-atom-screen.md` for the live checklist). The
verdict below (§ Ship decision) is already decisive from QF_LRA alone; the
remaining division is an exposure check, not load-bearing for it.

## The question

ADR-2111's census found `QF_LRA`'s largest ADDRESSABLE undecided bucket is 32
rows that die inside `lra.rs`'s offline Fourier–Motzkin fallback (86–91%
addressable against reference solvers), not the dense tableau that lane fixed.
Those 32 rows get there because the online CDCL(T) engine's own admission
screen (`AXEYUM_LRA_ATOM_SCREEN`, `crates/axeyum-solver/src/lra_theory.rs`)
refuses some of them for having too many atoms, and the route policy falls
through to the much weaker offline loop. The screen's own doc names why
raising it is a trap and not just an opportunity: three replacement cost
models were built and falsified by the corpus, the last of which bounded
Fourier–Motzkin's own allocations correctly and still let `danoint-266.smt2`
reach 7.8 GB with no simplex involved. ADR-2125 and ADR-2132 have since made
the tableau sparse (measured fill-in up to 21x). So: **does raising the
screen decide any of the 32 now, and what does it cost in memory and time?**

**Answer: no rows decide at any tested level, and raising the screen to 16x
or above introduces new allocation aborts that do not exist today.** Full
numbers below.

## Method

See `run-ladder.sh`, `find_candidates.py` and `derive_ladder.py` for the full
reasoning; short version here.

`AXEYUM_LRA_ATOM_SCREEN` is a multiplier on `admitted_atoms` in exactly one
comparison, `atom_terms.len() > admitted_atoms`, inside
`check_qf_lra_online_cdclt`. Nothing downstream reads the multiplier or
`admitted_atoms` again — `CdcltLraTheory::new` is built from the real atom
list and `budget_bytes`, not the allowance. So for a FIXED file, raising the
multiplier is a **step function**: refused (bit-identical to the shipped
binary) below the file's own threshold `ceil(atoms / admitted_at_1)`,
bit-identical to one measured "admitted" run at or above it. This was
checked live, not just read from source (§ below), before committing to the
full sweep.

That means the full 2x/4x/16x/off ladder does not need five brute-force
sweeps. This lane runs exactly **two** passes per population:

1. `shipped` (multiplier 1) over every file. This is the loss control AND
   the source of every refused file's exact atom count — read from the
   `; lazy-smt reading=... atoms=N online_probe=admission-screen` diagnostic
   line in its capture (the admission screen's own refusal STRING is never
   surfaced in the route trail itself: QF_LRA dispatches under the `nra`
   route's umbrella, and what lands in that attempt's decline detail is
   whatever the OFFLINE fallback declined with, not the online screen's
   message — confirmed empirically, zero of the early captures contain the
   literal string "admission screen").
2. `open` (multiplier 65536, safely above every threshold measured in every
   division below) on exactly the files `shipped` refused via
   `online_probe=admission-screen`, plus a spot-check subset of files it did
   not refuse (control on the step-function claim), interleaved per file
   against a fresh `shipped` re-run.

Every ladder level's table is then DERIVED: a file is "admitted" at level L
iff `L >= threshold`, and its result at that level is read from whichever of
the two passes actually executed it on the correct side of that threshold.
Nothing is extrapolated across code that did not run — a file admitted at
16x and a file admitted at 65536 by the SAME open-arm run are, provably,
the same execution.

Envelope: 24 s budget, 8 GiB `ulimit -v` (soft), pinned core (s5, physical
core 1; core 3 for the cross-division sweeps), `--trace`, peak RSS captured
via `/usr/bin/time -v` (`rss-wrap.sh`). Binary:
`target/release/examples/smtcomp_cli`,
sha256 `6261a505ea6767af32873bfc897ae64f8879b6388e5ea1074d27a6d3e12218e3`.

Population: the 93 undecided + 107 decided (loss control) `QF_LRA` rows from
`bench-results/board-ab-20260915/QF_LRA.tsv` — confirmed to match
`bench-results/lra-trace-20260915/{undecided-93,decided-107}.txt` exactly
(union of the two lists, sorted, diffs clean against the board's 200).

## The mechanism, confirmed live before the sweep

On `QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_standard_init5_ground.i_3_2_2.bpl_7.smt2`
(one of the 32): at the shipped multiplier the online CDCL(T) probe is
refused by the admission screen (`online_probe=admission-screen`, 1,839
atoms against a 1,024 allowance) and the query falls through to the offline
loop, which burns the whole budget on Fourier–Motzkin and returns `unknown`.
At multiplier 65536 the SAME file now enters the online engine directly
(`lazy-smt reading=not-reached`, the offline loop never runs; `theory-layer`
populated: 428,277 decisions, `simplex_rows=1839`) — and comes back
`unknown` again, this time via `online_probe=model-did-not-replay`. This is
the wall ADR-2111 and ADR-2045 already named (opening the screen without
fixing model reconstruction repeats ADR-2045's "0 newly decided, 19 dying at
model-did-not-replay" result), confirmed live before the full sweep was run.

## The loss control: reproducing the board

The `shipped` pass reproduces the board's split at 199/200:
`QF_LRA/sc/sc-5.base.cvc.smt2` flipped decided→undecided
(`online_probe=model-did-not-replay`, unrelated to this lever —
`sc-5`'s threshold is 1, i.e. it was already admitted at the shipped
multiplier). One flip over 200 single-shot runs is inside the harness's own
documented 1–1.5% ambient reference-frame noise, not a regression; recorded
so a reader does not mistake it for one. 106/200 decided in this
reproduction, 107/200 on the original board.

## The 70 rows the admission screen actually refuses (of 200)

`find_candidates.py` over the `shipped` captures: **70 of 200** QF_LRA rows
hit `online_probe=admission-screen` (thresholds 2–239, i.e. 1,025–244,736
atoms); **16** reach the offline loop for some OTHER reason (mostly
`model-did-not-replay` — already admitted, this lever cannot touch them);
**114** never reach the lazy-SMT offline loop at all (decided outright, or
routed elsewhere).

(One bug found and fixed while building this: a watchdog-killed capture
prefixes every diagnostic line with `; partial ` instead of `; `, e.g.
`; partial lazy-smt reading=...`. The first version of `find_candidates.py`'s
anchored regex missed that prefix and undercounted QF_UFLRA's admission-screen
hits 4-of-8 instead of 8-of-8 — found by comparing against a plain `grep -l`.
Fixed in the committed version.)

## The ladder table (QF_LRA, 200 rows: 93 undecided + 107 decided)

| level | admitted (of 200) | decided | Δ decided vs shipped | new aborts vs shipped |
|---|---:|---:|---:|---:|
| shipped (1x) | 130 | 106 | — | — |
| 2x | 134 | 106 | **+0** | 0 |
| 4x | 142 | 106 | **+0** | 0 |
| 16x | 162 | 106 | **+0** | **6** |
| off (65536x, max observed threshold 239) | 200 | 106 | **+0** | **8** |

Per-file diff between `shipped` and the `open` (65536x) arm, over all 70
admission-screen-refused files: **0 gains, 0 losses, 0 soundness flips, 78
"SAME"** (70 candidates + 8 spot-check non-candidates, all identical —
empirically confirms the step-function claim, not just the source reading).
**8 new aborts** (`exit=134`, `Command terminated by signal 6` — the same
allocator-abort shape ADR-2111's own doc names): every one of them was a
clean `unknown` at the shipped multiplier and a SIGABRT at 65536x. Their
thresholds are 11, 11, 11, 13, 15, 16, 17, 18 — so **6 of the 8 already
abort at 16x**, and none abort at 2x or 4x (all thresholds ≥ 11).

Because decided count is identical at every level and the aborting files
were never decided at any level (shipped or open), **0 stable movers exist**
— the 3x mover recheck (`recheck-movers.sh`) has a comparable denominator of
0, same shape ADR-2111's own atom-screen section anticipated ("0 movers, so
the 3x recheck has a comparable denominator of 0"). Nothing to recheck.

## The memory curve

| level | median RSS | p90 RSS | max RSS |
|---|---:|---:|---:|
| 2x | 28.2 MiB | 368.2 MiB | 1.09 GiB |
| 4x | 28.2 MiB | 460.6 MiB | 1.12 GiB |
| 16x | 28.2 MiB | 737.3 MiB | **7.40 GiB** |
| off | 28.2 MiB | 838.0 MiB | **7.40 GiB** |

(median/p90 wall time: unchanged across every level, 4.71 s / 24.8 s — the
files that don't abort still spend the same time whether admitted or
refused, since either route burns the budget or returns promptly on the
same shape of input.)

Worked example — `QF_LRA/LassoRanker/CooperatingT2/p-43.t2.c_Iteration4_Loop_4-pieceTemplate.smt2`:
120.6 MiB peak RSS at the shipped multiplier (refused in microseconds,
falls through, offline loop finishes fine) → **7.38 GiB** at 65536x, killed
by SIGABRT after 7.87 s (`Command terminated by signal 6`), right at the
8 GiB `ulimit -v` ceiling. This is the exact failure mode ADR-2111's own doc
predicted for a lane that raises this screen: "the screen is not protecting
one named mechanism — it is a conservative stand-in for an allocation nobody
has found." The sparse tableau (ADR-2125/2132) did not remove it: these
files show `theory-layer` fields when admitted (real simplex activity,
unlike `danoint-266`'s `simplex_rows=n/a` case from the falsified cost-model
history), so this is memory the warm/sparse machinery itself is now
consuming at scale, not a dead pre-simplex allocator.

## The 32's enter/refuse/fail split

Of ADR-2111's original 32 `lra.rs`-bucket rows:

- **10** were already admitted at the shipped multiplier (refused for
  `model-did-not-replay`, not atom count) — this lever cannot touch them at
  any level, by construction (threshold = 1).
- **22** are refused by the admission screen at the shipped multiplier
  (thresholds 2–13, so **all 22 are admitted by 16x**, same population as
  "off" for this specific subset). At 16x/off:
  - **18** now ENTER the online engine and still return `unknown` (mostly
    `model-did-not-replay` again — the SAME wall the 10 above are already
    stuck behind, just reached from the other side of the screen).
  - **4** now ENTER and ABORT: `joey_false-termination...`,
    `NoriSharma-2013FSE-Fig8...`, `OpposedDisjuncts.bpl...`,
    `SyntaxSupportBooleans5.bpl...` — new failures introduced by opening the
    screen, none of which existed at the shipped multiplier.
  - **0** newly decided.

So even restricted to the population this whole census was about, the
result is unchanged: 0 gains, and opening the screen converts roughly a
fifth of this specific 32-row bucket from "clean unknown" to "allocator
abort" while deciding nothing.

## Cross-division check

| division | unique rows checked | admission-screen hits | open-arm run | gains | losses | new aborts | max open-arm RSS |
|---|---:|---:|---|---:|---:|---:|---:|
| QF_UFLRA | 200 | 8 (thresholds 3–60) | yes (8 candidates + 8 spot-check) | 0 | 0 | 0 | (not the binding constraint here) |
| QF_LIA | **140** (see note) | 0 | not needed (0 candidates) | — | — | — | — |
| QF_RDL | 200 | 36 (thresholds 3–25) | yes (36 candidates + 9 spot-check) | 0 | 0 | 0 | 1.27 GiB |
| QF_IDL | pending | pending | pending | | | | |

**QF_LIA note**: `bench-results/board-ab-20260915/QF_LIA.tsv` has 200 data
rows but only **140 distinct corpus-relative paths** (60 rows are exact
duplicates of another row in the same file) — the other three cross-division
boards (QF_UFLRA, QF_RDL, QF_IDL) are clean 200-of-200 unique. Not something
this lane fixes; recorded because "checked all 200" would have been false.
Every one of the 140 unique QF_LIA files reached `reading=not-reached` — the
lazy-SMT offline loop this screen guards entry to is never invoked for
QF_LIA at all on this population, so the lever provably cannot affect it
(0 candidates is a clean structural negative, not a sample that missed the
population).

QF_UFLRA: 8 files hit the admission screen (thresholds 3, 3, 3, 3, 3, 3, 46,
60); the `open` arm (65536x, admits all 8) reproduces `unknown` on every one
of them, `unknown` on every spot-check non-candidate, and **introduces no
aborts** — unlike QF_LRA's own 8 (different corpus shape: these files'
absolute atom counts are smaller in aggregate, and none evidently trip
whatever unnamed allocation the QF_LRA aborts hit).

QF_RDL: 36 files hit the admission screen (thresholds 3–25 — the
`sal/fischer*-mutex-*` and `scheduling/{abz7,swv1[1-4]}_*` families,
threshold clustering by family since these are parametrised benchmark
sets with near-identical atom counts within a family). The `open` arm
reproduces `unknown`/`sat`/`unsat` identically on every one of the 36 plus
9 spot-checks (0 gains, 0 losses, 0 flips), and peak RSS across the whole
open-arm run tops out at **1.27 GiB** — nowhere near the 8 GiB ceiling, so
this division shows the "raising the screen is free but useless" half of
the space rather than QF_LRA's "free below 16x, costly above it" shape.

## Ship decision

**Does not ship. No default moves; no ADR-2137; no Rust change.**

Criterion from the brief: 0 stable losses, 0 aborts introduced, ≥1 stable
gain, on the pinned list, before even reaching the held-out 200-file draw.

| criterion | 2x | 4x | 16x | off |
|---|---|---|---|---|
| 0 stable losses | pass (0) | pass (0) | pass (0) | pass (0) |
| 0 aborts introduced | pass (0) | pass (0) | **FAIL (6)** | **FAIL (8)** |
| ≥1 stable gain | **FAIL (0)** | **FAIL (0)** | **FAIL (0)** | **FAIL (0)** |

Every tested level fails on "≥1 stable gain" alone — raising the atom screen
buys **zero** newly decided `QF_LRA` rows at any multiplier up to and
including fully open, over the full 200-row population, the 70-row refused
subset, and the specific 32-row bucket this whole investigation was about.
16x and off additionally fail on "0 aborts introduced": 6 and 8 new
allocator aborts respectively, on files that run cleanly today. 2x and 4x
introduce no aborts but still buy nothing.

**Why, precisely** (this is the finding, not just the number): the 32-row
bucket's true wall is not atom count, it is "online CDCL(T) LRA model did
not replay" — 10 of the 32 are stuck behind it already at the shipped
multiplier, and raising the screen only walks another 18 of the 22
screen-refused rows into the SAME wall from the other side (plus turns 4 of
them into allocator aborts along the way). This matches ADR-2111 §6 item 2
almost exactly ("model did not replay" is item 2 of the unaddressed work,
separate from and prior to the atom screen in that list) and reproduces
ADR-2045's own finding under a different lever. The sparse tableau
(ADR-2125/2132) changed what the ONLINE engine's memory scales like once
admitted, but it did not change WHETHER admission helps, because admission
was never the bottleneck for this population — model reconstruction is. A
future lane raising this screen again owes a fix to `check_qf_lra_online_cdclt`'s
model-replay path first (ADR-2055's 16-of-23 "model WAS built and does not
satisfy the original assertions" bucket), not a bigger allowance.

No config_registry entry changes, no ADR-2137, no Rust touched — the brief's
own conditional ("if a level ships... if none does, stop at the README with
the numbers") resolves to the second branch.
