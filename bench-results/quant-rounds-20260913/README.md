# The 177-file "round budget" family is not bound by a round budget — 0 of 177

**2026-09-13, lane `quant-rounds`.** ADR-1950 ranked
`e-matching instantiation did not refute within the round budget` as the
largest actionable blocker on lane `board-six`'s six-division board: **177 of
390 winnable files, 45 %, across four divisions**, giving up with a median
**23,994 ms of a 24,000 ms budget unspent**. It classified the family `ROUND`
and said only an A/B could decide whether to raise the cap.

That classification was read off the string. **Three different loop exits
emitted that one string**, and only one of them is a round budget.
`qinst_egraph.rs`'s own dump label for the point already said so — it was
spelled `"fixpoint-or-break"`.

    exit                       remedy                       what it said
    ------------------------   --------------------------   -------------------------
    fixpoint  (nothing left)   instance selection/triggers  "…round budget"
    growth headroom (clock)    more time                    "…round budget"
    round ceiling (512)        a bigger number              "…round budget"

With the exits split and all 177 re-run under the same envelope:

| population | n | SHAPE (fixpoint) | CLOCK | **ROUND** | other | max rounds entered |
|---|---:|---:|---:|---:|---:|---:|
| LRA | 117 | 117 | 0 | **0** | 0 | 7 |
| AUFLIA | 48 | 40 | 4 | **0** | 4 | 99 |
| BV + NRA + UFLIA | 12 | 10 | 1 | **0** | 1 | 65 |
| **TOTAL** | **177** | **167** | **5** | **0** | **5** | **99** |

**The ceiling is 512 and the deepest row in the whole family entered 99. The
LRA majority entered ONE.** The sizing bracket is **177 blocked → 0 reachable**.

### The unambiguous form, and it is stronger

The table above classifies by the FIRST give-up line, which is the convention
`board-six`'s census used — and several ladder rungs run the instantiation loop
(`q:mbqi-quick`, `q:egraph`, `q:mbqi`, `q:uf-fmf-full`), so the first line can
belong to a rung that timed out before the loop started. That is what the five
`other` rows are, and it makes "the first give-up was not ROUND" weaker than it
looks.

Scanning the WHOLE trace instead (`roundprobe.sh`, `summarize.py roundprobe`):

    rows                                177
      round budget string ANYWHERE      0     <- the bracket
      fixpoint string anywhere          171
      growth-headroom string anywhere    32
      UNMEASURED (no give-up line)        0

**The round-ceiling give-up does not appear anywhere in any of the 177 runs**,
and the zero is not a grep that missed its subject: every row carries a give-up
line, and 171 carry the fixpoint string this same scan looks for.

Every row that did not come back `SHAPE` was re-run three more times
(`summarize.py recheck`) — at a 24 s budget roughly 1–1.5 % of files flip on
ambient load alone, so a single pairing is not a finding:

    recheck-1  n=10  CLOCK=4  OTHER=5  SHAPE=1
    recheck-2  n=10  CLOCK=5  OTHER=4  SHAPE=1
    recheck-3  n=10  CLOCK=6  OTHER=3  SHAPE=1
    ROUND across 30 re-run solves: 0

The CLOCK/OTHER split wobbles — both are clock-family reasons and which one
prints first depends on load — and `ROUND` is 0 in all three.

The decision, the alternatives and the correction to ADR-1950's `kind` column
are in
[ADR-1956](../../docs/research/09-decisions/adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md).

## The value sweep: flat at zero from the first step

Four arms — shipped 512, 2x, 4x, 8x — **back to back on the same pinned core
for one file before any arm sees the next**, arm order rotating per file.

| population | n | arm | decided | gained | lost | median ms | total s |
|---|---:|---|---:|---:|---:|---:|---:|
| LRA | 117 | shipped | 0 | — | — | 106 | 50.9 |
| | | 1024 (2x) | 0 | **0** | 0 | 106 | 49.7 |
| | | 2048 (4x) | 0 | **0** | 0 | 106 | 49.7 |
| | | 4096 (8x) | 0 | **0** | 0 | 106 | 51.4 |
| AUFLIA | 48 | shipped | 0 | — | — | 10014 | 499.8 |
| | | 1024 (2x) | 0 | **0** | 0 | 10315 | 500.0 |
| | | 2048 (4x) | 0 | **0** | 0 | 10115 | 502.9 |
| | | 4096 (8x) | 0 | **0** | 0 | 10017 | 500.8 |
| BV+NRA+UFLIA | 12 | shipped | 0 | — | — | 2109 | 74.3 |
| | | 1024 (2x) | 0 | **0** | 0 | 2011 | 77.1 |
| | | 2048 (4x) | 0 | **0** | 0 | 2210 | 74.0 |
| | | 4096 (8x) | 0 | **0** | 0 | 2210 | 73.4 |

**All 177 rows, all four arms: gained 0, lost 0, `conflicting decided verdicts
across arms: 0`, and the totals do not move.**

ADR-1945's QF_UFBV sweep read +31/+44/+45 at 2x/4x/8x and used the SHAPE of
that curve to decide what shipped. This one is flat at zero from the first
step, which is what a non-binding constraint looks like and is a different
finding from "8x was not enough". `conflicting decided verdicts across arms: 0`
on every population.

Regenerate: `python3 summarize.py sweep`.

## The cost on work we already decide

A round cap turns a slow `unknown` into a fast one. Raising it runs the reverse,
and ADR-1945 measured exactly that failure — 33 of 35 non-gainers became
clock-bound and two QF_ABVFP files went from a 0.5 s verdict to a 25 s watchdog,
a 40x blow-up. So the control is the **692 files the board says we already
decide** in the same six quantified divisions, at the most aggressive arm.

**All 692 rows, arm B = `AXEYUM_QINST_ROUNDS=4096` (8x), interleaved per file:**

    same-decided      684        GAINED   0
    same-undecided      8        LOST     0
                                 DISAGREE 0
    median ms     shipped 109    8x 109
    total s       shipped 722.2  8x 722.4
    rows over 20 s  shipped 8    8x 8

**0 lost, 0 gained, 0 sat/unsat disagreement, and the wall clock does not
move** — 722.2 s against 722.4 s over 692 files, with the same 8 rows above 20 s
on both arms. There is no 40x blow-up here because there is nothing to blow up:
a loop that stops for a reason unrelated to the ceiling does the same work
whatever the ceiling says.

The 8 `same-undecided` rows are files the board recorded as decided that come
back `unknown` on BOTH arms in this run — a board-vs-today difference at the
1.2 % level, not an arm effect. Regenerate: `python3 summarize.py cost`.

## The control the brief named was three-quarters vacuous, and here is the number

This lane's brief named QF_UFLIA, QF_UFLRA, NRA and QF_DT as the control.
**Three of those four are quantifier-FREE**, so the e-matching instantiation
loop cannot run on them at all. Measured from the route trail rather than
assumed (`route-hit.sh`) — `q:egraph` is ATTEMPTED on:

| division | n | `q:egraph` attempted | e-matching give-up |
|---|---:|---:|---:|
| QF_DT | 200 | **0** | 0 |
| QF_UFLIA | 200 | **0** | 0 |
| QF_UFLRA | 200 | **0** | 0 |
| NRA | 200 | 9 | 3 |

That is ADR-1945's own hole reproduced — its lane found `ufbv_online` fires on
0 of 400 of its control files, so half its control could not have detected
anything. `summarize.py control` prints this table; a division at 0 cannot
detect any change to the route under test.

## What the 167 fixpoint rows actually look like — the next lane's lever

`AXEYUM_QPROBE=1` on all 117 LRA rows (`fixpoint-shape.sh`):

    ground-set size at fixpoint:  0 -> 103 rows     12 -> 14 rows
    EMPTY e-graph (ground=0):     103 of 117  (88.0 %)
    >= 1 triggerless universal:    63 of 117  (53.8 %)

**88 % of the LRA family fixpoints with an EMPTY e-graph.** 98 of the 117 are
`LRA/2010-Monniaux-QE`, whose files are a ten-deep alternating `∀∃∀∃…` prefix
over the reals **with no free constant anywhere** — there is not one ground term
for a trigger to match. The other 19 are `scholl-smt08`, the same shape. Both
are quantifier-ELIMINATION corpora.

No round count and no ground-term ceiling expresses a fix for a query with
nothing to instantiate over. `q:fourier-motzkin` does not appear in these files'
route trails at all.

**The BV and AUFLIA remainders are a different finding and must not inherit
this one**: BV's 10 rows fixpoint with non-trivial ground sets at up to 65
rounds, and AUFLIA's 48 split 40 SHAPE / 4 CLOCK / 4 other.

## The levers

Three `cap_lever!` accessors over the three round constants. **Unset is the
shipped value byte for byte**; a malformed value panics naming the variable
rather than silently measuring the default arm; each is a registered
`env_override` in `config_registry`, so `--trace`'s `; config` line shows a
variable that was actually read (a misspelled NAME is the one failure a lever
cannot see).

| variable | constant | shipped | what it bounds |
|---|---|---:|---|
| `AXEYUM_QINST_ROUNDS` | `MAX_EXTENDED_INSTANTIATION_ROUNDS` | 512 | the loop's round ceiling |
| `AXEYUM_QINST_CADENCE` | `MAX_INSTANTIATION_ROUNDS` | 8 | where interleaved ground checks start |
| `AXEYUM_QINST_ROUND_HEADROOM` | `ROUND_GROWTH_HEADROOM` | 8 | the clock multiple a new round needs |

`RoundCeilingGuard` is a thread-local override on top of the process arm — the
same split `GroundBudgetGuard` already uses, because `cap_lever!` caches in a
`OnceLock` and a lever whose arms cannot be compared inside one process has an
untestable promise.

## The guards can fail

`python3 scripts/tests/mutation_controls.py qinst-round-exit` removes one guard
at a time. **Baseline green at 113 tests; 7 mutations, 7 killed:**

    a FIXPOINT exit does not claim a round budget          killed 1
    the fixpoint break records which exit fired            killed 1
    the loop reads the ceiling ACCESSOR, not the constant  killed 1
    the round-ceiling guard restores on drop               killed 1
    the ceiling lever defaults to the SHIPPED constant     killed 1
    a fixpoint's census kind is SHAPE, not ROUND           killed 1
    an unrefuted ground set gives UP, not unsat            killed 11

Six kill **exactly one** test. The seventh is the soundness mutation and kills
the whole "never refutes a satisfiable query" family,
`no_round_ceiling_arm_refutes_a_satisfiable_query` included — which is what
makes that test a soundness-negative rather than a shape assertion.

The first mutation killed **two** in an earlier run, and the fix is worth
recording: the end-to-end test spelled the expected wording as a literal, so it
died for the wording defect as well as for its own. It now DERIVES the
expectation from `InstantiationLoopExit` itself, which the wording mutation
moves on both sides — so each test dies for one defect.

One fixture choice is itself a measurement. The truncation test first used this
module's predecessor-recurrence fixture and **failed**: a 2-round ceiling still
returned `Unsat`, because `predecessor_recurrence_sign_refutation` decides it on
an arithmetic fast path BEFORE the loop. A test built on it would have pinned
the fast path while claiming to pin the ceiling. The shipped fixture is an
uninterpreted six-link successor chain, where round count and chain length are
the same number.

## Protocol

- Population **re-derived, never transcribed**: `mkpop.py` reads lane
  `board-six`'s committed `census/*.tsv` and selects rows by the ranked
  give-up string. It prints 117/48/10/1/1/0 = **177**, which is ADR-1950's
  number, and says so loudly if it ever stops being.
- Cost control likewise: `mkcontrol.py` reads the board TSVs and takes every
  row where `axeyum` decided — 56/84/148/193/71/140 = **692**.
- **24 s wall, 8 GiB address space, one pinned physical core per shard**, the
  same envelope as the board these rows came from, so a row here is comparable
  to the row it came from. Wrapper timeout 24 + 16 s.
- Arms **interleaved per file** on the same core with the order rotating, so
  ambient load cancels in the difference rather than landing on one arm. Every
  arm runs under `env -u` on all four levers this lane can set, so the shipped
  arm is the shipped binary even if the caller's shell exports one — the failure
  where an "A/B" measures arm B twice.
- Boxes s5/s6/s7 (Ryzen 7 7840HS, 26 GB), **load 0.02 / 0.13 / 0.13 at launch**.
  Live probe on s5 before any measurement, with the exact binary and flags.
- Binary built from scratch on this branch in a dedicated target dir and
  **verified newer than every `crates/**/*.rs`** before use.
- **No solver behaviour changed in this lane.** The reported REASON changed for
  two of three exits; no verdict did — 117 pinned LRA rows, 117 `unknown`
  before and 117 after, and 0 conflicting decided verdicts across all four
  sweep arms.

## Files

| path | what |
|---|---|
| `mkpop.py` `mkcontrol.py` | the populations, derived from `board-six`'s committed TSVs |
| `exit-census.sh` | which of the three exits fired, per file |
| `sweep-run.sh` | the four-arm rotating sweep |
| `ab-run.sh` | the two-arm interleaved A/B (the cost control) |
| `roundprobe.sh` | does the ROUND give-up appear anywhere in a run |
| `mkrecheck.py` `merge-sweep.py` | the re-check population; the shard merge, which aborts on an incomplete set |
| `route-hit.sh` | does the route under test RUN on a population |
| `fixpoint-shape.sh` | what the e-graph looks like when it fixpoints |
| `summarize.py` | `exit` / `roundprobe` / `recheck` / `sweep` / `cost` / `control` / `shape` — every number above |
| `out/` | the rows |
| `pop/` | the pinned populations |
