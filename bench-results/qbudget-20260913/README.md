# The quantified ladder's clocks: which budget, whose rung, and what more of it buys

**2026-09-13, lane `QBUDGET`.** [ADR-1970]'s handoff named what was left on
`UFNIA`/`UFLIA`: *"the 32-row family that stops with a third of the clock
unspent — whose remedy is a rung that does not exist, not a budget"*. This lane
takes that family.

Half of that sentence is right. The half that matters is not: there **is** a
budget the loop is denied, the denial is measurable to the millisecond, and
handing it back is worth nothing — for a reason that turns out to be a
capability statement about the instantiation loop rather than a scheduling one.

Every number below is re-derivable from the committed TSVs by `ab-summarize.py`
and `confirm-summarize.py`. Nothing here is transcribed.

## 1. The budget architecture — ONE deadline, sibling slices inside it

The two give-up strings in the census are **not two clocks**. There is one root
deadline (the caller's `SolverConfig::timeout`, 24 s on the boards), turned into
a single `deadline: Option<Instant>` that `finish_quantified_solve`
(`auto.rs:405`) threads through every rung. Each rung calls
`config_with_remaining_timeout` (`auto.rs:210`) to re-derive *what is left of the
root clock*, and some then cut a `LadderSlice` out of that remainder. So the
clocks are **nested** — every slice lies inside the root deadline — and one
rung's slice is a **sibling** of the next rung's.

| # | rung | slice of what is left | constant |
|---|---|---|---|
| 0 | valid-universal elimination | **all but 1/4** | `quant_valid_universal_budget` (ADR-1975, ships ON) |
| 1 | `q:forall-exists-witness` | all | — |
| 2 | `q:finite-expansion` | all | — |
| 3 | `q:uf-fmf-probe` | `uf_fmf_probe_budget` | — |
| 4 | `q:mbqi-quick` | **1/8** | `MBQI_FIRST_REFUSAL_SLICE` |
| 5 | `q:egraph` | all | `quant_egraph_budget` (ADR-1970, ships OFF) |
| 6 | `q:mbqi` | all | — |
| 6a | └ the Skolemized e-graph **retry**, inside rung 6 | **1/2** | `QINST_EGRAPH_RETRY_SLICE` |
| 7 | `q:uf-fmf-full` | all | — |

- **`quantified solve time budget exhausted after <stage>`** is
  `quantified_timeout()` (`auto.rs:309`) — the **root** deadline passing.
- **`e-matching: instantiation time budget exhausted`** is `egraph_timeout()`
  (`qinst_egraph.rs:2698`) — a rung's **own slice** expiring strictly inside the
  root deadline.

A row carrying the second string as its final give-up therefore still had root
clock when it stopped. Measured, on merged `main`: median `24,000 − wall` is
**+8,675 ms** (`UFNIA`, 37 rows) and **+2,822 ms** (`UFLIA`).

## 2. The second string is `q:mbqi`'s, not `q:egraph`'s

`run_egraph_quantified_fallback` (`auto.rs:345`) **declines** its `Unknown`
rather than returning it, so rung 5 cannot be what emits that string as a
verdict. Rung 6 is:

    prove_unsat_by_mbqi_inner            auto.rs:9582
      -> shape guard (5 sites: 9613, 9620, 9630, 9638, 9654)
      -> prove_unsat_by_ematching        auto.rs:9976
        -> skolemized_egraph_retry       auto.rs:10126
          -> prove_quantified_unsat_via_egraph   <- the SAME loop as rung 5,
                                                    on the SKOLEMIZED assertions
          under QINST_EGRAPH_RETRY_SLICE = fraction(1/2)

**The e-graph instantiation loop runs TWICE** on any quantified query reaching
`q:mbqi`. The census's own `bound_by` column already said so and was not read: it
is **`q:mbqi` on 27 of the 37** `UFNIA` rows in this family.

## 3. The starvation question, answered by measurement

The census `qtrace` reads `egraph@24.017:declined;(+23 segments of other stages
dropped)`. **That `(+N dropped)` is a rendering limit on the trace string**, and
nothing here is inferred from it: it cannot distinguish "those stages ran for
microseconds" from "ran fully and declined" from "never started".

`AXEYUM_QPROBE=1` prints the lines that can. On four files of the family
(`qprobe/UFNIA.family.base.tsv`, base arm, board envelope, one pinned core):

    wall 15,316 / 15,222 / 15,320 / 15,217 ms   of 24,000
    mbqi-rung   state=entered budget_ms=2995..2999
    mbqi-shape  exit=quantifier-below-top-level
    skolemized-egraph  budget=8.83 s  elapsed=8.85 s
                       -> e-matching: instantiation time budget exhausted

1. **The retry is cut off by its own slice, not by the root deadline.** Granted
   8.83 s, spends 8.85 s — every millisecond of its share.
2. **Nothing spends the remaining 8.7 s.** The run *ends* at 15.3 s. The ladder
   did not run out of clock; it ran out of **rungs**. The half is reserved for
   `q:uf-fmf-full`, which declines a non-pure-UF query in one cheap scan. **36 %
   of the budget is returned unused.**
3. **`q:egraph` is not the clock holder here.** Back out the arithmetic: rung 4
   is handed 1/8 = 3.0 s, so ~24 s remained above it; the retry is handed half of
   what is left = 8.83 s, so 17.7 s remained at its entry. Everything between
   them — `q:egraph` included — is **~3.3 s**. [ADR-1970]'s title is a true
   sentence about a **different** family.

`mbqi-shape exit=quantifier-below-top-level` closes the chain: on this family the
whole of `q:mbqi` **is** the e-matching route, so the retry is the only thing
rung 6 does.

### Why [ADR-1970]'s ceiling was not one-way for the e-graph family

[ADR-1970] sized a reserve on rung 5 by its `share = 1` ceiling — which hands
rungs 6–7 essentially the whole budget — and concluded that a file it did not
decide is "out of reach of every reserve". **Rung 6 hands half of whatever it
gets straight back to the same loop.** That arm therefore re-proportioned the two
e-graph passes' budgets rather than funding the non-e-graph rungs. Its null is
real, and it is a null about *where inside the e-graph family the clock sits*.

## 4. The lever, and its genuinely one-way ceiling

`AXEYUM_QINST_EGRAPH_RETRY_SHARE` — **ships OFF**. `off`, `0`, an empty value,
anything unparseable and an absent variable all resolve to the shipped `2`, so a
typo degrades to today's behaviour rather than selecting an arm nobody chose.
`whole` or `1` is the measured **ceiling** arm: the retry takes the whole
remaining root clock. Nothing on that rung can grant the loop more, and unlike
ADR-1970's it does not route the clock back through the thing it took it from.

## 5. The A/B

Interleaved per-file, **one binary and two env values**, arms back to back on the
same file on the same pinned physical core with the order alternating, 24 s wall
/ 8 GiB `ulimit -v`, 8 shards on s5 and s6.

| division | n | base | ceiling arm | net | gain | loss | sat↔unsat flips |
|---|---:|---:|---:|---:|---:|---:|---:|
| `UFNIA` | 200 | 54 | 54 | **+0** | 1 | 1 | 0 |
| `UFLIA` | 200 | 73 | 75 | **+2** | 2 | 0 | 0 |
| `UF` *(control)* | 200 | 90 | 90 | **+0** | 0 | 0 | 0 |
| `AUFLIA` *(control)* | 200 | 86 | 86 | **+0** | 0 | 0 | 0 |

**Soundness, with the comparable denominator on the same line ([ADR-1957]):**

    UFNIA  :status 15/15 base 14/14 arm | UFLIA 73/73 and 75/75
    UF     :status 88/88 base 88/88 arm | AUFLIA 86/86 and 86/86
    DISAGREEMENTS: 0.   sat<->unsat flips: 0 in 1,600 solves.

### The arm does what it is designed to do

Measured at the rung and on the clock, so "the lever is live" is not assumed:

| | base | ceiling arm |
|---|---:|---:|
| retry budget, read at the dispatch site | 8.83 s | **16.17 s** |
| `UFNIA` target-family median wall | 15,325 ms | **24,135 ms** |
| `UFLIA` target-family median wall | 21,279 ms | **24,231 ms** |

### And it decides zero of the family it was built for

| division | target-family rows | median ms unspent | decided by the ceiling arm |
|---|---:|---:|---:|
| `UFNIA` | 37 | 8,675 | **0** |
| `UFLIA` | 24 | 2,721 | **0** |
| `AUFLIA` *(control)* | 21 | 8,975 | **0** |
| `UF` *(control)* | 5 | 3,071 | **0** |
| **total** | **87** | | **0** |

Wilson 95 % on 0/87 is **`[0 %, 4.23 %]`** — at most 3.7 files, point estimate
zero. Because `share = 1` is a genuine one-way ceiling on this rung, **these 87
files are out of reach of every budget policy on it at this wall budget.**

The controls were not expected to carry this family at all; `AUFLIA` supplying 21
more rows of it is a finding the lane did not go looking for.

Every row that *did* move came from a **different** family:

| file | direction | base give-up family |
|---|---|---|
| `UFNIA t3_rw1159` | gain | quantified solve time budget (ROOT deadline) |
| `UFNIA z3.885941` | apparent loss | — (base `unsat`) |
| `UFLIA javafe…TagConstants.001` | gain | quantified solve time budget (ROOT deadline) |
| `UFLIA smtlib.993567` | gain | query has quantifiers instantiation does not reach |

## 6. Controls, and why neither is vacuous

`UF` is the control that could actually **lose**: it is the pure-UF division where
`q:uf-fmf-full` — the rung whose reserve this arm spends — is the one that
decides. `AUFLIA` is [ADR-1970]'s quantified control. The hit rates are published
beside the nulls:

- **`UF`**: `q:uf-fmf-full` binds **26** of its 110 undecided rows,
  `q:uf-fmf-probe` another **29**. The reserve protects something live here.
  Movement: **0 gains, 0 losses.**
- **`AUFLIA`**: `q:mbqi` — where the retry lives — binds **65** of 114.
  Movement: **0 gains, 0 losses.**

`UF`'s own largest family is **69 rows** of `e-matching instantiation reached
fixpoint` with a median 10,476 ms unspent — the exit whose own documentation says
*"more rounds, and more clock, are both worth exactly zero. The gap is instance
selection or trigger coverage."*

## 7. Noise floor — measured, one whole division, three times

    UFNIA base-arm totals:  54 / 53 / 53        BAND: 1 file
    files that disagree with themselves:  1     (z3.885941)
    sat<->unsat between runs of the SAME arm: 0

The single churning file is `z3.885941` — the same file the A/B recorded as the
one `UFNIA` loss, and the same file the re-check called UNSTABLE. Three
instruments that share no mechanism agree it is the machine.

## 8. Every moved row, three runs per arm, against three authorities

    rows re-checked: 4   GAIN 3   LOSS 0   UNSTABLE 1   CONTRADICTED 0
    NO INDEPENDENT CHECK AT ANY BUDGET (ADR-1957): 1 of 4  <-- VACUOUS for that row

| row | base ×3 | arm ×3 | verdict |
|---|---|---|---|
| `UFNIA z3.885941` | unknown, unknown, unsat | unknown, unknown, unsat | **UNSTABLE** |
| `UFLIA javafe…001` | unknown ×3 | unsat ×3 | **GAIN**, all three authorities `unsat` |
| `UFLIA smtlib.993567` | unknown ×3 | unsat ×3 | **GAIN**, all three authorities `unsat` |
| `UFNIA t3_rw1159` | unknown ×3 | unsat ×3 | **GAIN, UNCONFIRMED** — nothing decides it at 24 s or 600 s |

Re-checked effect over the 400 primary files: **+2 confirmed, +1 unconfirmed, 0
stable losses.**

## 9. The finding that outlives the null: the verdict is not monotone in the budget

Round admission asks whether another round fits **with growth headroom** against
the *remaining budget* (`qinst_egraph.rs:2267-2269`), then breaks to a **final
ground check** over everything accumulated — whose own code records the hazard:
*"the full-set final check over a near-cap conjunction is itself a wall (measured
26.7 s-then-unknown over 8192 conjuncts)"* (`qinst_egraph.rs:4081`).

So the share changes the **number of rounds admitted**, hence the **size of the
ground set the final check is handed**. Measured on `f2_rw120`
(`qprobe/loop-exit.tsv`):

| arm | wall | verdict | `n_exits` | loop exit | rounds | ground |
|---|---:|---|---:|---|---:|---:|
| base | 15,217 ms | unknown | 1 | `Fixpoint` | 37 | 14 |
| ceiling | 24,222 ms | unknown | 2 | `GrowthHeadroom` | **391** | **787** |

**Ten times the rounds, fifty times the ground set, the same verdict.**

`n_exits` is load-bearing, and its absence was a defect in the first version of
this probe: the loop runs twice, and an invocation killed at a **round head**
returns before the exit line is printed (`qinst_egraph.rs:2256-2258`). So the
base row's `Fixpoint / 37 / 14` is the `q:egraph` **rung's** exit, not the
retry's. Reading it as the retry's was the first error the column was added to
prevent.

## 10. The decision

**Ship the lever OFF**, registered and gated so the next lane can re-ask with one
environment variable. The reasoning, the pre-registered rule the realised +2 falls
between, and the one narrow follow-up question are in
[ADR-1995](../../docs/research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md).

**Do not reach for a clock on this rung.** The ceiling is one-way and worth zero
on the family that looks clock-bound. The vein is instance *selection*.

## 11. Method

- **Population.** The pinned lists `../parity-lists/{UFNIA,UFLIA,UF,AUFLIA}.txt`,
  committed before any board was measured. Not re-sampled, never read as a prefix.
- **Envelope.** 24 s wall, 8 GiB `ulimit -v`, one pinned **physical** core
  (`c,c+8`), wrapper timeout 24 + 16 s — identical to the pinned boards, so a row
  here is comparable to the board row it came from.
- **Binary.** `build.sh` refuses to publish a binary that is not newer than every
  `crates/**/*.rs`. **One binary for every arm and every run**, built at
  `7276aaa7a`. The only source change after it is a comment (`eeb39c57f`) plus a
  hook and documents; no measured behaviour moved.
- **Branch.** `git merge-base main HEAD` is `main`'s HEAD (`e542fdc3d`), so the
  base arm measures the tree that ships. `origin/main` is `76f4f22c6`; local
  `main` is one bench-results commit ahead.
- **Polarity.** The lever **ships OFF**; base is `env -u`, the measured arm is
  `=1`. `ab-run.sh`'s header says so in a block of its own.
- **Placement.** One division at a time per host, because `launch-ab.sh` restarts
  shard numbering per division. s5 and s6, four core pairs each; s7 only for
  single-core probes.
- **Merging.** `merge-division.py` ABORTS unless the shards cover the pinned list
  exactly. `ab-summarize.py`, `confirm-summarize.py` and `noise-summarize.py` all
  carry finding-dependent exit statuses.

## 12. Files

| path | what |
|---|---|
| `PREREGISTRATION.md` | the sizing, committed before this lane ran the solver once |
| `PREREGISTRATION-ADDENDUM.md` | what merging `main` (ADR-1975/1980) does to it, still before the first run |
| `ab/*.tsv` | the interleaved A/B, per file, both arms, with `bound_by` and the give-up string on each |
| `noise/*.tsv` | three base-arm readings of `UFNIA` |
| `moved/confirm.raw.tsv` | every moved row, 3 runs per arm plus both references |
| `qprobe/*.tsv` | the rung budgets, and the round/ground counts per arm |
| `distinct/references.tsv` | z3 and cvc5 on the five `distinct`-capped files |
| `DISTINCT-ENCODING.md` | that handoff: the design, the polarity trap, and the measured sizing |
| `*.sh` `*.py` | the measurement and every derivation |

[ADR-1970]: ../../docs/research/09-decisions/adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md
[ADR-1975]: ../../docs/research/09-decisions/adr-1975-valid-universal-elimination-spends-24-seconds-to-prevent-a-107-millisecond-refutation.md
