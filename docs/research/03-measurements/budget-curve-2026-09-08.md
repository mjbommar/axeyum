# Budget curve: is the remaining gap engineering, or capability?

**Status: COMPLETE.** The protocol section below was committed before any
number was read, so it could not be chosen after the data was visible.

**The answer is capability, not engineering.** Across the four divisions we lose
135 files to the reference at 24 s. **Twelve** of them decide with 2.5x the
clock. The other **123 — 91 % — do not.**

## The question

Almost everything fixed on 2026-09-08 was a constant factor: a route consuming
24.009 s of a 24 s budget; 97 % of a budget spent on a method with a 0 % success
rate; fourteen files finishing at 24.2 s that now finish at 18.2 s. Constant
factors are exactly what a longer budget buys. So the open question is whether
what remains is more of the same — engineering — or something a clock cannot
reach — capability.

A budget curve separates them, but **only if the reference is on the same
curve.** If our solved count climbs steeply from 24 s to 60 s and the
reference's does not, the remainder is engineering. If both flatten together, we
are missing capability and more time will not close it.

## THE 24 s ROW IS THE HEADLINE. THE 60 s ROW IS NOT A PARITY NUMBER.

`scripts/parity-run.sh`'s own header lists the ways this repository has
historically made a gap look smaller, and one of them is *"a 2-second budget,
where both solvers time out and distance collapses."* **A long budget flatters
from the other end.** If the reference saturates — decides everything it is ever
going to decide — and we keep picking up easy files, the ratio rises while
nothing about the solver got better. The 60 s ratio is diagnostic; it is not a
score.

So, stated in advance and not retrospectively:

- **24 s is the only externally comparable number**, because that is what
  SMT-COMP publishes. Every headline claim in this repository stays on the 24 s
  row.
- The 6 s and 12 s rows exist to show the SHAPE of the left half of the curve,
  not to be quoted either.
- The 60 s row answers one question and one only: *does the count still move?*
- **If a later reader quotes the 60 s figure as our parity number, that reading
  is refused here, in advance, by the lane that produced it.**

## Protocol

Fixed before the run; nothing below was selected after data was visible.

| knob | value |
|---|---|
| harness | `scripts/parity-run.sh` (the committed protocol harness; no second harness was written) |
| budgets | 6 s, 12 s, 24 s, 60 s — `PARITY_BUDGET_S` |
| memory | 8 GiB per file at **every** budget — `PARITY_MEM_GB=8`, unchanged across the curve |
| population | the committed pinned lists, `bench-results/parity-lists/{QF_UFLIA,QF_LRA,QF_LIA,QF_ABV}.txt`, 200 files each, whole list as denominator |
| divisions | the four that moved on 2026-09-08 |
| reference | **run at every budget too** — cvc5 1.3.4 for QF_UFLIA / QF_LRA / QF_LIA, bitwuzla 0.9.1 for QF_ABV, exactly as the harness's own division table selects. No portfolio flags. |
| solver commit | `e99d08848` |
| binary | one `target/release/examples/smtcomp_cli`, built once and copied to every host, so no arm is confounded by a different build |
| budget order | **24 s first**, then 6, 12, 60 — so an interrupted sweep still yields the externally comparable row |

The reference running at every budget is the point of the exercise. A curve of
only our own numbers is unreadable: our count rises with budget for any solver
that is not already saturated, so the rise means nothing on its own. **The
quantity that matters is the ratio at each budget**, and the shape of the
reference's own curve beside ours.

## Machine reality — recorded, not assumed

`s5`, `s6` and `s7` were **not idle** at dispatch. They were measured at
dispatch and again at the end, and both numbers appear in every ledger entry
(`parity-run.sh` stamps them). Each host has 16 cores.

At dispatch, 2026-09-09T02:46:42Z:

| host | load (1/5/15 min) | division | other work on the box |
|---|---|---|---|
| `s5` | 3.04 / 3.08 / 3.00 | QF_LIA | the `parallel-portfolio` lane's `route_solo` per-route oracle sweep — 3 processes at ~100 % CPU |
| `s6` | 3.23 / 3.29 / 3.49 | QF_LRA | same `route_solo` sweep — 3 processes at ~100 % CPU |
| `s7` | 4.09 / 4.14 / 4.06 | QF_UFLIA **and** QF_ABV (separate worktrees) | `route_solo` + `smtcomp_cli --trace` from the same lane, 4 processes at ~100 % CPU, plus a long-running Minecraft `java` server at ~13 % |
| `s4` | 10.88 / 9.80 / 7.80 | **nothing scored** | several lanes building and testing; deliberately not used to measure, its load was too high and too variable |

Two consequences, both stated before the data:

- **Decided counts survive contention far better than wall times do**, which is
  why this measurement is worth taking on a shared box at all. Contention only
  ever LOSES files; it cannot produce a wrong verdict.
- **It does not follow that the RATIO is a floor.** `parity-run.sh`'s own header
  records the 2026-08-21 case where load cost the reference ten QF_LRA files and
  cost us none, so a loaded run reported a ratio six points HIGHER than the
  quiet one. A high-load row is a floor on our own count and **nothing at all**
  on the ratio.
- **Files near a budget boundary flip.** A file deciding at 23.8 s under load 4
  misses at load 8. Any row whose start and end loads differ materially is
  marked NOT COMPARABLE below rather than quietly averaged.


## Addendum, pinned at 04:40 UTC — a repeated 24 s pass, and why

Between dispatch and the start of the 60 s passes the boxes got **quieter**: the
`parallel-portfolio` lane's `route_solo` sweep wound down, and the loads that
were 3.0–4.1 at dispatch read 1.29 (`s5`), 2.00 (`s6`) and 2.01 (`s7`) at
04:39 UTC.

That is a confound pointing in the **dangerous** direction. The 60 s pass runs
last, so it runs on the quietest machine; some of its gain would be the quiet
box rather than the longer clock, and every file it recovers that way would be
scored TIME-BOUND — which is the answer that says "keep optimising."

So a **second 24 s pass is queued behind each 60 s pass**, decided here before
any 60 s number was read. It does two things:

1. It is a load-matched partner for the 60 s row, so the 24→60 increment is not
   read across two different machines.
2. **24 s versus 24 s-repeat, same list, same binary, same day, is the
   contention noise floor** for this whole exercise — a number we have been
   guessing at rather than measuring.

Where the two 24 s passes disagree, the classification below uses the
**repeat** (load-matched to 60 s), and the difference between them is reported
as noise rather than absorbed.

---

# Results

Twenty ledger entries, all `SOUND`, **zero disagreements** in every one — four
divisions x five passes (6 s, 12 s, 24 s, 60 s, and the load-matched 24 s
repeat), both solvers at every budget. Entries appended to
[`bench-results/PARITY.md`](../../../bench-results/PARITY.md); per-file
verdicts and the classification in
[`bench-results/budget-curve-20260908/`](../../../bench-results/budget-curve-20260908/).

### Table 1 — solved count versus budget, both solvers

| division | budget | axeyum | reference | ratio | both / axeyum-only / reference-only |
|---|---|---:|---:|---:|---|
| QF_UFLIA | 6 s | 113/200 | 178/200 | 63.5% | 113 / 0 / 65 |
| QF_UFLIA | 12 s | 121/200 | 179/200 | 67.6% | 121 / 0 / 58 |
| QF_UFLIA | 24 s | 127/200 | 180/200 | 70.6% | 127 / 0 / 53 |
| QF_UFLIA | 24 s (repeat) | 128/200 | 180/200 | 71.1% | 128 / 0 / 52 |
| QF_UFLIA | 60 s | 136/200 | 181/200 | 75.1% | 136 / 0 / 45 |
| QF_LRA | 6 s | 96/200 | 118/200 | 81.4% | 93 / 3 / 25 |
| QF_LRA | 12 s | 97/200 | 125/200 | 77.6% | 95 / 2 / 30 |
| QF_LRA | 24 s | 97/200 | 134/200 | 72.4% | 96 / 1 / 38 |
| QF_LRA | 24 s (repeat) | 97/200 | 145/200 | 66.9% | 96 / 1 / 49 |
| QF_LRA | 60 s | 99/200 | 158/200 | 62.7% | 99 / 0 / 59 |
| QF_LIA | 6 s | 110/200 | 134/200 | 82.1% | 108 / 2 / 26 |
| QF_LIA | 12 s | 115/200 | 138/200 | 83.3% | 113 / 2 / 25 |
| QF_LIA | 24 s | 119/200 | 139/200 | 85.6% | 117 / 2 / 22 |
| QF_LIA | 24 s (repeat) | 119/200 | 139/200 | 85.6% | 117 / 2 / 22 |
| QF_LIA | 60 s | 121/200 | 145/200 | 83.4% | 119 / 2 / 26 |
| QF_ABV | 6 s | 185/200 | 192/200 | 96.4% | 184 / 1 / 8 |
| QF_ABV | 12 s | 186/200 | 193/200 | 96.4% | 185 / 1 / 8 |
| QF_ABV | 24 s | 186/200 | 197/200 | 94.4% | 185 / 1 / 12 |
| QF_ABV | 24 s (repeat) | 186/200 | 197/200 | 94.4% | 185 / 1 / 12 |
| QF_ABV | 60 s | 186/200 | 198/200 | 93.9% | 185 / 1 / 13 |

### Table 2 — increments: where each curve flattens

| division | solver | 6→12 | 12→24 | 24→60 | 24(repeat)→60 |
|---|---|---:|---:|---:|---:|
| QF_UFLIA | axeyum | +8 | +6 | +9 | +8 |
| QF_UFLIA | reference | +1 | +1 | +1 | +1 |
| QF_LRA | axeyum | +1 | +0 | +2 | +2 |
| QF_LRA | reference | +7 | +9 | +24 | +13 |
| QF_LIA | axeyum | +5 | +4 | +2 | +2 |
| QF_LIA | reference | +4 | +1 | +6 | +6 |
| QF_ABV | axeyum | +1 | +0 | +0 | +0 |
| QF_ABV | reference | +1 | +4 | +1 | +1 |

### Table 3 — the contention noise floor: 24 s versus 24 s repeat

Same list, same binary, same host, same day; only the neighbours differ.
`moved` counts files whose verdict changed in EITHER direction.

| division | solver | 24 s | 24 s repeat | delta | files that moved |
|---|---|---:|---:|---:|---:|
| QF_UFLIA | axeyum | 127 | 128 | +1 | 1 |
| QF_UFLIA | reference | 180 | 180 | +0 | 0 |
| QF_LRA | axeyum | 97 | 97 | +0 | 0 |
| QF_LRA | reference | 134 | 145 | +11 | 11 |
| QF_LIA | axeyum | 119 | 119 | +0 | 0 |
| QF_LIA | reference | 139 | 139 | +0 | 0 |
| QF_ABV | axeyum | 186 | 186 | +0 | 0 |
| QF_ABV | reference | 197 | 197 | +0 | 0 |

### Table 4 — time-bound versus capability-bound losses

A LOSS is a file the reference decides and we do not, at the 24 s
baseline. The baseline is the 24 s REPEAT where one exists, because it
is load-matched to the 60 s pass.

| division | baseline used | losses | time-bound (we decide it at 60 s) | capability-bound (we still miss at 60 s) |
|---|---|---:|---:|---:|
| QF_UFLIA | 24 s (repeat) | 52 | 8 | 44 |
| QF_LRA | 24 s (repeat) | 49 | 2 | 47 |
| QF_LIA | 24 s (repeat) | 22 | 2 | 20 |
| QF_ABV | 24 s (repeat) | 12 | 0 | 12 |

### Table 5 — flips: decided at a shorter budget, lost at a longer one

| division | solver | 24 s → 60 s |
|---|---|---:|
| QF_UFLIA | axeyum | 0 |
| QF_UFLIA | reference | 0 |
| QF_LRA | axeyum | 0 |
| QF_LRA | reference | 0 |
| QF_LIA | axeyum | 0 |
| QF_LIA | reference | 0 |
| QF_ABV | axeyum | 0 |
| QF_ABV | reference | 0 |

### Table 6 — capability-bound losses by benchmark family

**QF_UFLIA — 44 files**

| family | files |
|---|---:|
| `Hash` | 30 |
| `20230314-Jaroslav-Bendik-Certora` | 6 |
| `medium` | 5 |
| `hard` | 2 |
| `wisas` | 1 |

**QF_LRA — 47 files**

| family | files |
|---|---:|
| `sc` | 13 |
| `CooperatingT2` | 7 |
| `2017-Heizmann-UltimateInvariantSynthesis` | 4 |
| `Ultimate` | 4 |
| `miplib` | 3 |
| `SCC_Strong` | 2 |
| `SV-COMP` | 2 |
| `clock_synchro` | 2 |
| `gasburner` | 2 |
| `pursuit` | 2 |
| `tgc` | 2 |
| `travellingSalesperson` | 1 |
| `TM` | 1 |
| `carpark` | 1 |
| `spider_benchmarks` | 1 |

**QF_LIA — 20 files**

| family | files |
|---|---:|
| `SMT_random_LIA` | 3 |
| `ReachSafety-Loops` | 2 |
| `checkpass_pwd` | 2 |
| `30-vars` | 1 |
| `incrementalScheduling` | 1 |
| `FamilyReunion-PT-L00400M0040C020P020G001` | 1 |
| `RwMutex-PT-r0010w0500` | 1 |
| `RwMutex-PT-r0010w2000` | 1 |
| `RwMutex-PT-r1000w0010` | 1 |
| `size-100` | 1 |
| `35-vars` | 1 |
| `SMT_real_LIA` | 1 |
| `convert` | 1 |
| `mathsat` | 1 |
| `print_file` | 1 |
| `rings` | 1 |

**QF_ABV — 12 files**

| family | files |
|---|---:|
| `cu-no-caches` | 4 |
| `dwp_formulas` | 3 |
| `brummayerbiere` | 2 |
| `2018-Mann` | 1 |
| `bmc-arrays` | 1 |
| `no_init_simple_delete` | 1 |


---

# Reading the curves

## The answer, plainly: capability, not engineering

Across the four divisions, at the load-matched 24 s baseline, the reference
decides **135 files we do not**. Give us **2.5x the clock and the same 8 GiB**
and we recover **twelve of them**. The other **123 — 91 % — do not move.**

That is the deliverable, and it redirects the work. The last day's wins were
constant factors and they were real, but constant factors are precisely what a
longer budget buys, and a longer budget buys us almost nothing. What is left is
not slow; it is *absent*.

## Where each curve flattens

| division | our curve | the reference's curve | what that means |
|---|---|---|---|
| **QF_LRA** | **flat at ~97** — 96 → 97 → 97 → 99 across a 10x budget | **steepest on the board** — 118 → 125 → 145 → 158, still climbing at 60 s | We hit a wall the reference is nowhere near. Purely capability. |
| **QF_ABV** | **flat from 12 s** — 185 → 186 → 186 → 186 | still gaining — 192 → 193 → 197 → 198 | Same shape, smaller absolute gap. Capability. |
| **QF_LIA** | rising — 110 → 115 → 119 → 121 | rising at the same rate — 134 → 138 → 139 → 145 | **Both curves climb together.** Neither is saturated; our relative position is unchanged. Time helps both equally, so it decides nothing. |
| **QF_UFLIA** | **steepest of ours** — 113 → 121 → 128 → 136 | **flat** — 178 → 179 → 180 → 181 | The one division where time buys us files and not the reference. Read the caveat below before calling it engineering. |

Two of the four curves — QF_LRA and QF_ABV — are the textbook capability
signature: **ours flat, theirs climbing.** A tenfold budget moves QF_LRA by
three files while it moves cvc5 by forty.

## QF_UFLIA is the "long budget flatters" case, exactly as warned

QF_UFLIA's ratio rises 63.5 % → 71.1 % → 75.1 % across the curve, and that rise
is **the artefact this note refused in advance**, not progress:

- **cvc5 is saturated in QF_UFLIA by 6 seconds.** It decides 178 files at 6 s
  and 181 at 60 s — it has 98 % of its final count before the SMT-COMP clock
  even starts. A saturated denominator is what makes a ratio rise for free.
- **Our `axeyum-only` column is `0` at every single budget** — 6, 12, 24, 24
  repeat, and 60. cvc5 decides a **strict superset** of what we decide, at every
  point on the curve. There is no budget at which we know something it does not.
- **44 of our 52 losses are still lost at 60 s**, and **30 of those 44 are one
  family** (`mathsat/Hash`). The +8 files are the tail of a distribution, not a
  front advancing.
- If the observed rate held — about +8 files per 2.5x budget — closing the
  remaining 45-file gap would take on the order of 100x the budget, roughly
  forty minutes per benchmark. And it will not hold: Table 6 says what is left
  is concentrated, not spread.

So QF_UFLIA is where *optimising still pays*, and it is still not where the gap
closes. The honest sentence is: **the gap is capability everywhere; QF_UFLIA is
the one division where engineering has not finished paying.**

## THE 24 s ROW IS THE HEADLINE — and here it is

| division | axeyum | reference | ratio at 24 s |
|---|---:|---:|---:|
| QF_ABV | 186/200 | 197/200 (bitwuzla 0.9.1) | **94.4 %** |
| QF_LIA | 119/200 | 139/200 (cvc5 1.3.4) | **85.6 %** |
| QF_UFLIA | 128/200 | 180/200 (cvc5 1.3.4) | **71.1 %** |
| QF_LRA | 97/200 | 145/200 (cvc5 1.3.4) | **66.9 %** |

Those four numbers are the parity claim. The 60 s ratios — 93.9 %, 83.4 %,
75.1 %, 62.7 % — are **not** parity numbers and must never be quoted as such:
two of them are *worse* than the 24 s figure and the other two rise only because
the reference stopped moving. **Anyone quoting the QF_UFLIA 75.1 % as "we are at
75 % of cvc5" is quoting a number produced by cvc5 saturating, not by us
improving.** That reading is refused here.

## The contention noise floor, measured rather than assumed

Two 24 s passes on the same list, same binary, same host, hours apart, under
loads of ~3–5 and then ~1: **axeyum moved 1 file out of 800** (one QF_UFLIA
file). Contention was not driving these numbers, and a curve taken on a busy box
is trustworthy for decided counts.

**But the noise is not symmetric, and that is the finding.** On QF_LRA, cvc5
moved **11 files** — 134 under load, 145 quiet — while we moved zero. This is an
independent reproduction of the 2026-08-21 asymmetry `parity-run.sh`'s own header
records, on a different day and a different host, and it lands on the same
division. It is also the exact size of the error it causes: the loaded QF_LRA
24 s pass reads **72.4 %** and the quiet one reads **66.9 %** — a 5.5-point
inflation *in our favour*, produced entirely by the reference losing files.

Two rules follow, and they are not optional:

- **A parity ratio measured under load is not a floor.** Our own count is; the
  quotient is not. The quiet number is the one that goes on the board — 66.9 %
  here, which is exactly what the idle-host sweep recorded on 2026-09-08.
- **QF_LRA is the division where this bites.** cvc5's QF_LRA work is
  timing-sensitive in a way ours is not, because ours has already stopped
  before the clock matters.

Zero flips in the other direction, in any division, for either solver: no file
decided at 24 s was lost at 60 s. The curve is monotone.

---

# The deliverable: which losses are time-bound and which are capability-bound

Per-file classification, machine readable, is
[`bench-results/budget-curve-20260908/classification.tsv`](../../../bench-results/budget-curve-20260908/classification.tsv)
(135 rows). The baseline is the load-matched 24 s repeat; a loss is
capability-bound when 2.5x the clock at the same 8 GiB does not recover it.

## Time-bound — 12 files. Keep optimising here, and only here.

| division | files |
|---|---:|
| QF_UFLIA | 8 |
| QF_LRA | 2 (`sal/clock_synchro/clocksynchro_4clocks.main_invar.base`, `sal/tgc/tgc_io-nosafe-4`) |
| QF_LIA | 2 |
| QF_ABV | 0 |

Twelve files is the entire measured return on making the current routes faster,
across 800 benchmarks. It is not nothing — the QF_UFLIA eight are real and they
came from a route that is still improving — but it is the size of the prize, and
nobody should scope a week against it without knowing that.

## Capability-bound — 123 files. More time will not touch these.

| division | files | largest family |
|---|---:|---|
| QF_UFLIA | 44 | `mathsat/Hash` — **30 of 44** |
| QF_LRA | 47 | `sc` — **13 of 47** |
| QF_LIA | 20 | scattered; no family above 3 |
| QF_ABV | 12 | `cu-no-caches` — 4 |

Two of these classes were already diagnosed by lanes on 2026-09-08, from the
route traces rather than from a budget curve. **This measurement is an
independent confirmation that neither is a clock problem**, and the two should
not be re-derived:

- **QF_LRA, the `sc` family — the model that does not replay.** The online
  CDCL(T) engine parses these files, searches them, reaches a satisfying Boolean
  assignment, and then `LraTheory::real_model()`'s reconstruction fails to replay
  against the original assertions, so it declines a decision it already had. The
  lane that named it (`online_probe=model-did-not-replay`) counted thirteen
  losing files; **this sweep finds exactly thirteen `sc` files
  (`sc-5` … `sc-29`, odd) capability-bound, plus `pursuit` 2, `tgc` 2 and
  `carpark` 1** — the same population. At 60 s, not one of them moves. That
  lane's write-up is
  `docs/research/12-performance/lra-route-and-cube-order-2026-09-08.md`, which is
  **on an unmerged lane branch, not on `main`** — see the version skew note
  below before citing it as landed.
- **QF_UFLIA, the `Hash` family — the interface branch that cannot be
  separated.** The combined CDCL(T) search runs to a leaf and reports
  `interface distinct branch inconclusive`: it is a capability gap in the
  interface search and the LIA sub-solve under it, not a bound being hit. The
  lane that named it counted fourteen such files **on its own tree**;
  this sweep, on `main`, finds **30 capability-bound `mathsat/Hash` files** —
  which is what you would expect, since that lane's fix is not in the binary
  measured here. Its write-up is
  `docs/research/12-performance/uflia-interface-caps-2026-09-08.md`, likewise on
  an unmerged branch.

## Version skew — read this before comparing to any lane's numbers

This curve measures **`e99d08848`, the tip of `origin/main`**. Two lanes have
landed QF_UFLIA and QF_LRA improvements **on their own branches that are not in
this binary**, including one claiming QF_UFLIA 130 → 151 of 200. So:

- The QF_UFLIA capability-bound list here (44 files, 30 of them `Hash`) is the
  state of **`main`**, not the state of the best branch in flight.
- **The curve must be re-run after those merges.** The shape question — does our
  count still move with budget — has to be re-asked of the merged solver, and
  the `Hash` family is exactly where a merged fix would show up.
- What re-running will **not** change is QF_LRA's and QF_ABV's shape. Those
  curves are flat because the routes stop, not because they run out of clock,
  and no merge in flight touches that.

---

# What this says to the next lanes

**Stop scoping parity work as optimisation.** The measured return on making the
current routes faster, across all four divisions and 800 benchmarks, is twelve
files. A lane that halves a route's constant factor is competing for a share of
those twelve.

Concretely:

1. **QF_LRA is the highest-value target on the board and it is not a
   performance problem.** 47 capability-bound losses, our curve flat at 97–99
   across a 10x budget while cvc5 goes 118 → 158. The single largest sub-class —
   13 `sc` files — is a solver that *has the answer and throws it away* because
   model reconstruction will not replay. That is a bug-shaped capability gap, and
   it is worth more than any timing work in this division.
2. **QF_UFLIA is the one place where optimising still pays**, and it pays eight
   files. Its 44 capability-bound losses are 68 % one family, and the class is
   already named (interface-branch separation). Fix the class, not the clock.
3. **QF_ABV needs nothing from the budget.** We are flat from 12 s at 186 and
   bitwuzla is at 198. Twelve files, all capability-bound, in six families — a
   small, well-defined list, and no reason to look at timing.
4. **QF_LIA is the ambiguous one and should be left alone for now.** Both curves
   climb at the same rate, so the budget experiment does not separate the causes
   there; its 20 capability-bound losses are scattered across sixteen families
   with none above three, which is the signature of *no single missing
   capability* rather than of a hidden one.
5. **Re-run this curve after the two in-flight lanes merge** — the method is
   `bench-results/budget-curve-20260908/driver.sh` plus `repeat24.sh`, both
   committed, and the whole sweep is about 5.5 hours per division sharded across
   three hosts.

## Method notes, for a re-run

- The load-matched 24 s repeat is not optional. Without it the QF_LRA 24 s row
  reads 72.4 % instead of 66.9 %, and the 24 → 60 increment would have been read
  across two different machines.
- Run the divisions on separate hosts and the budgets sequentially per host. Do
  not run two budgets of one division at once: `parity-run.sh` locks its sidecar
  per worktree, but two sweeps would still contend for the same cores and both
  numbers would be depressed.
- Build the binary once and copy it to every host. Building per host would
  confound every arm with a different compilation.
- Total wall clock for this run: 02:47 UTC to 08:09 UTC, four divisions, twenty
  passes, 8,000 scored solver invocations (200 files x 2 solvers x 20 passes)
  plus 100 reference smoke probes.
