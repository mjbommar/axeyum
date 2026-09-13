# The two QF_UFBV caps, A/B'd — 84 blocked, 49 reachable, and one cap worth nothing alone

**2026-09-12/13, lane `qf-ufbv-caps`.** The [QF_UFBV blocker
census](../fpbv-divisions-headtohead-20260912/README.md) attributed **84 of 87
winnable files** to two literals on adjacent lines of
`crates/axeyum-solver/src/ufbv_online.rs`:

    const MAX_INPUT_DAG_NODES: u64 = 16_384;   // 31 files, 1.00x-14.04x over
    const MAX_THEORY_ATOMS: usize = 1_024;     // 53 files, 1.04x- 5.33x over

That lane refused to raise them and gave the reason: **a cap turns a slow
`unknown` into a fast `unknown`.** Removing it does not make a query decidable;
it makes us spend the budget finding that out. This lane ran the A/B:
**9,793 axeyum runs** over seven populations, plus 98 reference runs.
`count-runs.py` derives both from the artifacts rather than from arithmetic on
what the sweeps were supposed to have done.

## The answer in one table

| | atom cap | node cap |
|---|---|---|
| files the census attributed to it | 53 | 31 |
| files it decides **alone** | **+44** at 4_096 | **+0** at 2x, 4x and 16x |
| files it decides on top of the other | +45 at 8_192 | +4 |
| cost on 800 already-decided control files | **−2** | **−2**, deterministic |
| shipped | **raised to 4_096, scalar path only** | **held at 16_384** |

## The sweep: 200 files x 9 cap settings

**The baseline arm decides 89 of 200 — the board row exactly.** A sweep whose
control arm does not reproduce the number it is compared against is measuring
something else.

| cap raised | value | decided of 200 | gain | loss | wall |
|---|---|---:|---:|---:|---:|
| — (baseline) | 1_024 / 16_384 | **89** | — | — | 472.6 s |
| atoms | 2_048 | 120 | +31 | 0 | 776.3 s (1.64x) |
| atoms | 4_096 | 133 | **+44** | 0 | 1070.3 s (2.26x) |
| atoms | 8_192 | 134 | +45 | 0 | 1190.5 s (2.52x) |
| nodes | 32_768 | 89 | **+0** | 0 | 519.9 s (1.10x) |
| nodes | 65_536 | 89 | **+0** | 0 | 520.6 s (1.10x) |
| nodes | 262_144 | 89 | **+0** | 0 | 519.6 s (1.10x) |
| both | 4_096 / 65_536 | 137 | +48 | 0 | 1167.4 s (2.47x) |
| both | 8_192 / 262_144 | 138 | +49 | 0 | 1650.6 s (3.49x) |

**49 of the 87 winnable files decide. 35 do not.** `winnable-split.py` splits
the best arm's 49 gains into **46 inside the census's winnable 87** and 3
outside it — files no reference decided either. It aborts if any of the 87 is
decided by the baseline, which is what would tell you the list had gone stale
against this binary; none is.

### The node cap is worth zero because the two caps are SEQUENTIAL GATES

Not "a small gain" — not one file, at any value, on the 31 files the census
attributed to it. `admit_input` rejects an over-budget DAG before
`build_theory_atoms` ever runs, so a file over the node cap **has never had its
atom count measured**. Raising the node cap does not decide it; it hands it to
the atom cap. Over the 111 files the baseline leaves undecided:

    arm        node-blocked   atom-blocked
    base                 39             64
    n32768               17             84
    n65536                9             92
    n262144               1            100

Every file the node raise admits reappears, undecided, one gate later.

On top of `atoms = 4_096` the node raise finally buys **4 files** — three of
them over the cap by **1.00x-1.07x** (16,437 / 16,588 / 17,509 against 16,384).
The 14x tail the census measured, the number that made the node cap look like
the bigger problem, bought nothing.

### What the other 35 run into

At `8_192 / 262_144`, over the same 111:

     49  DECIDED
     21  Timeout: preprocessed dispatch timeout after reduced solve
     17  ResourceLimit: online UFBV has N semantic atoms, exceeding the cap of 8192
     12  Timeout: online UFBV canonical CdclT search exhausted its budget
      5  Watchdog / 3 Boolean-variable cap / 2 interface cap / 1 node / 1 ingest

**33 of the 35 non-gainers are now clock-bound**, where the census found 2 of 87
were — the previous lane's prediction, measured. And **17 files still exceed
8_192 atoms**: the census measured 1.04x-5.33x over 1_024 (max 5,458), but it
could only measure files that *reached* the atom check. Once the node cap admits
the 39 node-blocked files, they bring atom counts past 8,192. A census's
over-cap magnitudes are a **lower bound on the population**, not a description
of it, whenever an earlier gate hides part of that population.

## Cost on already-decided work: 800 control files, and every arm loses

`ufbv_online` is not QF_UFBV's alone — `admit_input` is also the admission gate
for `abv-online-cdclt`, the first route every array query tries. So the control
is **800 files we already decide**: QF_BV, QF_UFLIA, QF_ABVFP and QF_ABV, from
the same pinned parity lists.

| arm | decided of 800 | gain | loss |
|---|---:|---:|---:|
| base | **711** | — | — |
| atoms 4_096 | 709 | 0 | **2** |
| nodes 65_536 | 709 | 0 | **2** |
| nodes 262_144 | 709 | 0 | **2** |
| both 4_096 / 65_536 | 707 | 0 | **4** |
| both 8_192 / 262_144 | 708 | 0 | **3** |

### The control is not vacuous, and that had to be checked separately

A control population that never reaches the cap being raised cannot lose, and
its zero would mean nothing. `decided_by`/`bound_by` cannot answer this — a
route that declines in 1 ms is neither, and the final give-up line belongs to
whatever ran last. `--trace`'s `route-trail` JSON names **every** attempted
route, and `exposure-probe.sh` reads it:

    division      files  ufbv_online ran  a cap fired
    QF_ABV          200              161           32
    QF_ABVFP        200              183            3
    QF_BV           200                0            0
    QF_UFLIA        200                0            0
    TOTAL           800              344           35

**QF_BV and QF_UFLIA never enter this route at all**, so their halves of the
control are a statement about blast radius, not about robustness. The 400 array
files are the real control, and **35 of them actually hit one of the two caps**.
`exposure-summary.py` refuses to report unless the probe answered both ways on
the population — an all-yes or all-no answer from a detector nobody has seen
discriminate is indistinguishable from a broken detector. It answered 344 yes /
456 no.

### Every loss re-run nine times on an idle box

Four losses, at 15-24 s against a 24 s budget or better — exactly the shape that
flipped a false convert in this repository the day before. `replicate.sh` re-ran
each 9 times per arm, interleaved, on one pinned core of an idle s5:

| file | base | atoms 4_096 | nodes 65_536 | both |
|---|---|---|---|---|
| `QF_ABV/…/try3_sameret…hold_file` | 9/9 @ 4.5 s | **6/9 @ 22.5 s** | 9/9 @ 4.5 s | 5/9 @ 22.5 s |
| `QF_ABV/…/try5_small_noof…` | 9/9 @ 5.3 s | **5/9 @ 23.3 s** | 9/9 @ 5.3 s | 5/9 @ 23.3 s |
| `QF_ABVFP/…/query.435` | 9/9 @ 0.6 s | 9/9 @ 0.6 s | **0/9 @ 25.0 s** | 0/9 @ 25.0 s |
| `QF_ABVFP/…/query.708` | 9/9 @ 0.4 s | 9/9 @ 0.4 s | **0/9 @ 25.0 s** | 0/9 @ 25.0 s |

The separation is total, and it is what decided the shape of the change:

- **The atom raise costs the two QF_ABV files 18 seconds** — 4.5 s to 22.5 s on
  an idle box. The verdict survives 5-6 times in 9 there and is lost on a shared
  box. The cost is deterministic even where the loss is not.
- **The node raise costs the two QF_ABVFP files everything**: a 0.4-0.6 s
  `array-fast-path` verdict becomes a 25 s `Watchdog`, **0 of 9**, in every
  node-raising arm. Not noise, and not a budget edge — a 40x blow-up into
  `abv-online-cdclt`, which the QF_ABVFP census already measured completing
  **zero CEGAR rounds at a 600 s budget**. On the array path this cap is a guard
  in front of an open bug, not a tuning knob.
- **Each cap's damage stays in its own pair.** The atom raise does not touch the
  ABVFP pair; the node raise does not touch the ABV pair.

All four losses are on the **array** path. That is why the shipped change is
path-specific.

## What shipped, measured as shipped

`MAX_SCALAR_THEORY_ATOMS = 4_096` on the scalar path (`admit_arrays == false`,
i.e. `check_qf_ufbv_online_cdclt` and nothing else); `MAX_THEORY_ATOMS` stays
1_024 for arrays and `MAX_INPUT_DAG_NODES` stays 16_384 everywhere.

Re-measured on the built binary, `shipped` (nothing set) against `preadr`
(`AXEYUM_UFBV_MAX_SCALAR_THEORY_ATOMS=1024`, which restores the old value) — one
binary, so this is a diff of the decision rather than of two builds:

| division | files | pre-ADR | shipped | gain | loss | pre-ADR wall | shipped wall |
|---|---:|---:|---:|---:|---:|---:|---:|
| QF_UFBV | 200 | 89 | **129** | **+40** | **0** | 570.8 s | 1275.7 s |
| QF_ABV | 200 | 186 | 186 | 0 | 0 | 622.1 s | 615.8 s |
| QF_ABVFP | 200 | 179 | 179 | 0 | 0 | 551.8 s | 552.5 s |

**0 of the 400 array files differ in verdict between the two arms**, and their
wall totals move by less than 1 %. That is the blast-radius claim, measured
rather than argued from the diff: the array path's constant did not move, so the
array path did not either. `shipped-summary.py` prints that line for QF_ABV and
QF_ABVFP unconditionally, so it cannot pass by being omitted.

`QF_ABVFP` at 179 of 200 reproduces its board row exactly, which is the frame
check on the control side.

**The division goes from 89 to 129 of 200 against z3's 174** — the gap closes
from 85 files to 45. The 2.23x wall on QF_UFBV is the price, and it is the
"slow `unknown`" the census lane warned about, now paid for 40 decisions.

## The gains survive a hostile frame, at a smaller size

**12 of the 49 gains land at 15-24 s of a 24 s budget**, so the sweep was re-run
on a deliberately **loaded** box (s4 at load ~11, two shards on two P-cores)
rather than the lightly loaded s5/s6/s7:

| arm | quiet frame | loaded frame |
|---|---:|---:|
| baseline decided | 89 | 88 |
| atoms 4_096 | +44 | **+33** |
| atoms 4_096 / nodes 32_768 | not run | +41 |
| both 4_096 / 65_536 | +48 | +39 |
| both 8_192 / 262_144 | +49 | +38 (and 1 loss) |

**Both numbers are the result.** The gain is real in every frame and its size is
frame-dependent; quoting +44 without +33 would overstate it, and quoting +33
alone would understate it. A single number for a budget-edge population is the
thing this repository's own protocol note warns against.

`monotone.py` gives the same answer from the other side without a second run:
along every cap ladder, **exactly 1 file of 200** is decided at a lower value
and not at a higher one — `hanoi.2` at 23.1 s versus 24.1 s. Everything else is
perfectly monotone, which is what a mechanism looks like and what noise does
not.

## Verification of every newly decided file

All 49, re-run against z3 4.13.3, cvc5 1.3.4 and the declared `:status`, using
the **shipped** binary. `verify-summary.py` exits non-zero on any disagreement.

    49 newly decided files re-run; we decide 43 of them here
      vs status  43/43 agree (0 not comparable)
      vs z3      40/40 agree (3 not comparable: the reference returned no verdict)
      vs cvc5    40/40 agree (3 not comparable)

    we decide 3 file(s) NEITHER reference does:
      unsat  QF_UFBV/20210312-Bouvier/vlsat3_d10.smt2   (:status unsat)
      unsat  QF_UFBV/20210312-Bouvier/vlsat3_d18.smt2   (:status unsat)
      unsat  QF_UFBV/20210312-Bouvier/vlsat3_d79.smt2   (:status unsat)

    0 disagreements against :status, z3 and cvc5.

The 6 of 49 still unknown at the shipped setting are the node-cap gains the
shipped default deliberately does not deliver (`rether.3`, `rether.4`,
`lifts.2`, `telephony.5`) plus `gear.1` and `vlsat3_j01`. **0 of our own runs
were wrapper-killed**; cvc5 hit the protocol's 8 GiB cap on 3 rows (`rc134`), as
it does 38 times on the board — which is why **z3 is the reference to name when
quoting this division's gap**, not cvc5.

## Soundness

**0 disagreements, across every population.** `summarize.py` aborts if two arms
return `sat` and `unsat` for one file: none do, across 1,800 runs on 200 files
at nine settings, 4,800 runs on 800 control files at six, 1,000 on the loaded
frame and 1,200 on the shipped comparison.

## Protocol

Matches the board and census this answers
(`bench-results/fpbv-divisions-headtohead-20260912`), so a row here is
comparable to the row it came from.

- **The pinned 200**, `bench-results/parity-lists/QF_UFBV.txt`, committed at
  `04e0df4ac` before any of this was measured. Control and shipped populations
  come from the same pinned lists.
- **24 s wall, 8 GiB address space, `--trace`**, wrapper timeout 24+16 s.
- **Every arm runs on one file back to back on the same pinned physical core
  before any arm starts the next file, and the arm ORDER ROTATES with the file
  index.** Ambient load then cancels in the difference between arms on one file,
  which is the only comparison made. Wall totals are reported as ratios within a
  sweep, never across sweeps.
- Two shards per box on distinct physical cores (`0,8` and `2,10`); the 8 GiB
  cap is per run and these are 26 GB boxes, so three shards can reach 24 GiB.
  Boxes s5 / s6 / s7 (Ryzen 7 7840HS); the loaded-frame run is s4 (i5-12600K,
  pins `0,1` and `2,3` — two distinct P-cores, E-cores avoided).
- **Binaries built from this branch**, verified newer than every
  `crates/**/*.rs` before use (`find crates -name '*.rs' -newer <binary>`
  returned nothing). The shipped comparison uses one binary whose `md5sum` was
  checked against the build tree after staging. A stale prebuilt binary reported
  a false ABSENT three separate times in this repository on 2026-09-12.
- **A live probe before any row is written**: `ab-run.sh` aborts unless the
  binary *decides* a trivial query first. A missing binary otherwise scores a
  silent all-`unknown` that reads exactly like a result.
- **The lever refuses a malformed value by panicking, and the CLI turns a worker
  panic into `unknown`** — which reads exactly like "the raised cap did not
  help". Every row records whether the refusal text reached stderr, and every
  summarizer **aborts** if any row has it. 0 rows do.
- **One in-flight sweep was killed and discarded** when a lint fix changed the
  binary mid-run. A sweep whose binary is not the one being reported is not a
  cheaper version of the measurement.

## The checkers can fail

`controls/fixture.py`: nine fixtures, one per abort path plus a clean one that
must produce a report and **not** abort. **9 of 9 pass**, each written by
breaking the thing it guards:

    a clean fixture reports and does not abort
    a refused lever aborts
    a missing matrix cell aborts
    a sat/unsat disagreement between arms aborts
    a duplicate row aborts
    a wrong file count aborts
    a missing arm aborts
    an empty directory aborts
    a fixture with NO baseline arm aborts

The clean case is not filler: a checker that flags everything has a zero that
means as little as one that flags nothing.

**One of these scripts was wrong and the data caught it.** `control-vacuity.py`
originally concluded, when the route ran but no cap fired, that "raising them
cannot change this population's verdicts". The very next arm lost two files
through the other mechanism — a file the raise *admits*, which then spends
budget the later routes needed. The script now reports the two counts and
refuses to draw that inference.

## Files

| path | what |
|---|---|
| `out/main200/` | 1,800 runs: 200 files x 9 cap settings |
| `out/control800/` | 4,800 runs: 800 already-decided files x 6 settings |
| `out/confirm-s4/` | 1,000 runs: the loaded-frame replication |
| `out/replicate/` | 144 runs: every loss, 9 reps per arm, idle box |
| `out/exposure/` | the route-trail probe over all 800 control files |
| `out/verify/` | all 49 gains vs z3, cvc5 and `:status` |
| `out/shipped600/` | 1,200 runs: the shipped default vs the pre-ADR value |
| `*-report.txt` | the summarizers' output, from which every number here is read |
| `lists/` | the pinned populations, so every denominator is re-derivable |
| `ab-run.sh` `launch.sh` `verify.sh` `replicate.sh` `exposure-probe.sh` | the runners |
| `summarize.py` `attribute.py` `winnable-split.py` `monotone.py` `control-vacuity.py` `exposure-summary.py` `replicate-summary.py` `verify-summary.py` `shipped-summary.py` `gains-list.py` | the derivations |
| `peek.py` | partial read of an in-flight sweep; prints its own denominator |
| `controls/fixture.py` | the summarizer's own controls |
