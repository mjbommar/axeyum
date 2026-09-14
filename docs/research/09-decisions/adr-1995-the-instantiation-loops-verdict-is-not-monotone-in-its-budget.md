# ADR-1995: the e-graph retry is cut off by its own half-slice, the reserve is spent by nobody, and handing it back decides zero of sixty-one

Status: accepted
Index-summary: The quantified ladder's two give-up strings are **one root deadline and a slice inside it**, not two clocks — and the inner one is **`q:mbqi`'s, not `q:egraph`'s**: `prove_unsat_by_mbqi_inner`'s shape guard falls through to `prove_unsat_by_ematching`, which hands the **SKOLEMIZED** assertions back to the **SAME e-graph loop** under a 1/2 slice, so that loop runs **TWICE** per query. `AXEYUM_QPROBE` on the family settles the starvation question by measurement rather than from a `(+N segments dropped)` rendering limit: the retry is **granted 8.83 s and spends 8.85 s** — cut off by its own slice with **8.7 s of 24 s left that nothing then spends**, because the reserve is held for `q:uf-fmf-full`, which declines a non-pure-UF query in one cheap scan. **The ladder runs out of RUNGS, not clock**, and the arithmetic puts `q:egraph` at ~3.3 s here, so [ADR-1970] describes a different family — as its own `bound_by=q:mbqi` on 27 of 37 rows said. Hand that clock back through a genuine one-way ceiling (`AXEYUM_QINST_EGRAPH_RETRY_SHARE=1`, the retry takes the whole remaining ROOT deadline) and the family is **0 of 87 across FOUR divisions** (Wilson 95 % `[0 %, 4.2 %]`) — so these files are out of reach of **every** budget policy on this rung. The A/B nets `UFNIA` +0, `UFLIA` +2, `UF` and `AUFLIA` controls **0/0** with the route binding 26 and 65 of their undecided rows, **0 disagreements and 0 sat↔unsat flips in 1,600 solves**; after 3x-per-arm re-checks, **+2 confirmed, +1 unconfirmed (ADR-1957), 0 stable losses, 1 UNSTABLE** — and that UNSTABLE row is the *only* file that churns across three base-arm noise runs (54/53/53, **band 1 file**). **Ships OFF**: every gain came from a *different* family, and the mechanism is measured **non-monotone** — round admission consults the remaining budget (`qinst_egraph.rs:2267`) and breaks to a final ground check, so the ceiling arm admits **391 rounds and 787 ground terms** on `f2_rw120` and still refutes nothing. The vein is search power, not clock. Separately: the five `distinct` pair-expansion refusals are **four files z3 refutes in 111–508 ms** that we never hand to a solver at all.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1970]'s own handoff named what was left on `UFNIA`/`UFLIA`: *"the 32-row
family that stops with a third of the clock unspent — whose remedy is a rung that
does not exist, not a budget"*. This ADR takes that family. Half of that sentence
is right; the half that matters is not. There **is** a budget the loop is denied,
the denial is measurable to the millisecond, and handing it back decides **none**
of the family — for a reason that is a capability statement about the
instantiation loop rather than a scheduling one.

## The budget architecture, which had not been written down

**One root deadline, and sibling slices cut out of what is left of it.** The two
give-up strings in the census are not two clocks. `finish_quantified_solve`
(`auto.rs:405`) threads a single `deadline` through every rung; each rung calls
`config_with_remaining_timeout` (`auto.rs:210`) to re-derive *what is left of the
root clock*, and some then cut a `LadderSlice` out of that remainder. So the
clocks are **nested**, and one rung's slice is a **sibling** of the next's.

- `quantified solve time budget exhausted after <stage>` = `quantified_timeout()`
  (`auto.rs:309`): the **root** deadline passing.
- `e-matching: instantiation time budget exhausted` = `egraph_timeout()`
  (`qinst_egraph.rs:2698`): a rung's **own slice** expiring strictly inside it.

A row with the second string as its final give-up therefore still had root clock:
median `24,000 − wall` is **+8,675 ms** (`UFNIA`, 37 rows) and **+2,671 ms**
(`UFLIA`, 24 rows), re-derived on merged `main`.

## The second string is `q:mbqi`'s, not `q:egraph`'s

`run_egraph_quantified_fallback` (`auto.rs:345`) **declines** its `Unknown`, so
rung `q:egraph` cannot be what emits that string as a verdict. `q:mbqi` is:

    prove_unsat_by_mbqi_inner            auto.rs:9582
      -> shape guard (5 sites: 9613, 9620, 9630, 9638, 9654)
      -> prove_unsat_by_ematching        auto.rs:9976
        -> skolemized_egraph_retry       auto.rs:10126
          -> prove_quantified_unsat_via_egraph   <- the SAME loop as q:egraph,
                                                    on the SKOLEMIZED assertions
          under QINST_EGRAPH_RETRY_SLICE = fraction(1/2)

**The e-graph instantiation loop runs twice** on any quantified query reaching
`q:mbqi`. The census's own `bound_by` column said so and was not read: `q:mbqi`
on **27 of the 37** `UFNIA` rows.

## The starvation question, answered by measurement

The census `qtrace` reads `egraph@24.017:declined;(+23 segments of other stages
dropped)`. **That `(+N dropped)` is a rendering limit on the trace string** and
nothing here is inferred from it. `AXEYUM_QPROBE=1` prints the lines that can
distinguish "ran for microseconds" from "ran and declined" from "never started".
On four files of the family (base arm, board envelope, one pinned core):

    wall 15,316 / 15,222 / 15,320 / 15,217 ms   of 24,000
    mbqi-shape  exit=quantifier-below-top-level
    skolemized-egraph  budget=8.83 s  elapsed=8.85 s

1. **The retry is cut off by its own slice**, not the root deadline: granted
   8.83 s, spends 8.85 s.
2. **Nothing spends the remaining 8.7 s.** The run ends at 15.3 s — the ladder
   ran out of **rungs**. The half is reserved for `q:uf-fmf-full`, which declines
   a non-pure-UF query in one cheap scan. **36 % of the budget is returned
   unused.**
3. **`q:egraph` is not the clock holder here.** Rung `q:mbqi-quick` is handed
   1/8 = 3.0 s (so ~24 s remained above it) and the retry is handed half of what
   is left = 8.83 s (so 17.7 s remained at its entry), which puts everything
   between them — `q:egraph` included — at **~3.3 s**.

### Why [ADR-1970]'s ceiling was not one-way for the e-graph family

Its `share = 1` arm moved clock off `q:egraph` onto `q:mbqi` — **which hands half
of whatever it gets straight back to the same loop**. That arm re-proportioned
the two e-graph passes rather than funding the non-e-graph rungs. Its null is a
null about *where inside the e-graph family the clock sits*.

## The measurement

`AXEYUM_QINST_EGRAPH_RETRY_SHARE` **ships OFF** (`off`/`0`/empty/unparseable/
absent all resolve to the shipped `2`). The measured arm is `1`: the retry takes
the whole remaining **root** deadline. Nothing on that rung can grant more, and
unlike ADR-1970's it does not route the clock back through what it took it from.

Interleaved per-file A/B, **one binary and two env values**, arms back to back on
the same file on the same pinned physical core with the order alternating, 24 s
wall / 8 GiB `ulimit -v`, 8 shards on s5 and s6. Branch `7276aaa7a`;
`git merge-base main HEAD` is `main`'s HEAD, so the base arm is the shipped tree.

| division | n | base | ceiling arm | net | gain | loss | sat↔unsat flips |
|---|---:|---:|---:|---:|---:|---:|---:|
| `UFNIA` | 200 | 54 | 54 | **+0** | 1 | 1 | 0 |
| `UFLIA` | 200 | 73 | 75 | **+2** | 2 | 0 | 0 |
| `UF` *(control)* | 200 | 90 | 90 | **+0** | 0 | 0 | 0 |
| `AUFLIA` *(control)* | 200 | 86 | 86 | **+0** | 0 | 0 | 0 |

**Soundness, with the comparable denominator on the same line ([ADR-1957]):**

    UFNIA   vs :status 15/15 base, 14/14 arm
    UFLIA   vs :status 73/73 base, 75/75 arm
    UF      vs :status 88/88 base, 88/88 arm
    AUFLIA  vs :status 86/86 base, 86/86 arm
    DISAGREEMENTS: 0.  sat<->unsat flips: 0 in 1,600 solves.

**Neither control is vacuous, and the numbers that say so are published rather
than asserted.** On `UF` the rung whose reserve this arm spends —
`q:uf-fmf-full` — is the binding route on **26** of its 110 undecided rows
(`q:uf-fmf-probe` on another 29). On `AUFLIA`, `q:mbqi` — where the retry lives —
binds **65** of 114. The route runs on both controls; both are flat.

**Noise floor, measured on one whole division, base arm, three times:**

    UFNIA base-arm totals: 54 / 53 / 53      BAND: 1 file
    files that disagree with themselves:  1  (z3.885941)
    sat<->unsat between runs of one arm:  0

**The arm does what it is designed to do.** On the target family the median wall
goes 15,325 → 24,135 ms (`UFNIA`) and 21,279 → 24,231 ms (`UFLIA`), and the rung
budget read back at the dispatch site goes 8.83 s → 16.17 s. The stranded clock
is spent.

### And it decides zero of the family it was built for

    TARGET FAMILY decided by the ceiling arm:   UFNIA 0 of 37   UFLIA 0 of 24

**0 of 61.** Wilson 95 % on 0/61 is `[0 %, 5.9 %]` — at most 3.6 files, and the
point estimate is zero. Because `share = 1` is a genuine one-way ceiling on this
rung, **these 61 files are out of reach of every budget policy on it at this wall
budget.**

Every row that *did* move came from a different family:

| file | direction | base give-up family |
|---|---|---|
| `UFNIA t3_rw1159` | gain | quantified solve time budget (ROOT deadline) |
| `UFNIA z3.885941` | apparent loss | — (base `unsat`) |
| `UFLIA javafe…TagConstants.001` | gain | quantified solve time budget (ROOT deadline) |
| `UFLIA smtlib.993567` | gain | query has quantifiers instantiation does not reach |

### Every moved row, three runs per arm, against three authorities

    rows re-checked: 4   GAIN 3   LOSS 0   UNSTABLE 1   CONTRADICTED 0
    NO INDEPENDENT CHECK AT ANY BUDGET (ADR-1957): 1 of 4  <-- VACUOUS for that row

| row | base ×3 | arm ×3 | verdict |
|---|---|---|---|
| `UFNIA z3.885941` | unknown, unknown, unsat | unknown, unknown, unsat | **UNSTABLE** — identical under both arms |
| `UFLIA javafe…001` | unknown ×3 | unsat ×3 | **GAIN**, `:status`/z3/cvc5 all `unsat` |
| `UFLIA smtlib.993567` | unknown ×3 | unsat ×3 | **GAIN**, `:status`/z3/cvc5 all `unsat` |
| `UFNIA t3_rw1159` | unknown ×3 | unsat ×3 | **GAIN but UNCONFIRMED** — `:status unknown`, cvc5 `unknown` at 24 s *and* 600 s, z3 no verdict at either |

**The `UFNIA` loss was ambient.** `z3.885941` produces the identical sequence
under both arms, and it is the *only* file that churns across the three
noise-floor runs. Three instruments that share no mechanism agree it is the
machine, not the lever. It is not counted in either direction.

**The `UFNIA` gain is unconfirmable** and is reported as such rather than folded
into the zero — exactly [ADR-1957]'s case.

So the re-checked effect over the 400 primary files is **+2 confirmed, +1
unconfirmed, 0 stable losses**, against a measured 1-file-per-division band.

## The finding that outlives the null: the loop's verdict is not monotone in its budget

The instantiation loop's round admission asks whether another round fits **with
growth headroom** against the *remaining budget*
(`qinst_egraph.rs:2267-2269`: `remaining < last_round_duration * 8`), and then
breaks to a **final ground check** over everything accumulated — whose own code
records the hazard: *"the full-set final check over a near-cap conjunction is
itself a wall (measured 26.7 s-then-unknown over 8192 conjuncts)"*
(`qinst_egraph.rs:4081`).

So changing the share changes the **number of rounds admitted**, hence the
**size of the ground set the final check is handed** — and a bigger ground set is
not a better one. This is not an argument; it is measured, on `f2_rw120`:

| arm | wall | verdict | `n_exits` | loop exit | rounds | ground |
|---|---:|---|---:|---|---:|---:|
| base | 15,217 ms | unknown | 1 | `Fixpoint` | 37 | 14 |
| ceiling | 24,222 ms | unknown | 2 | `GrowthHeadroom` | **391** | **787** |

**Ten times the rounds, fifty times the ground set, the same verdict.**

`n_exits` is load-bearing and its absence was a defect in the first version of
this probe: the loop runs twice, and an invocation killed at a **round head**
returns `egraph_timeout()` *before* the exit line is printed
(`qinst_egraph.rs:2256-2258`). So the base row's `Fixpoint / 37 / 14` is the
`q:egraph` **rung's** exit, not the retry's — the retry printed nothing because
it was cut off. Reading that row as the retry's was the first error this column
was added to prevent.

Three divisions now point the same way. `UF`'s own largest family is 69 rows of
`e-matching instantiation reached fixpoint` with a median 10,476 ms unspent — the
exit whose own documentation says *"more rounds, and more clock, are both worth
exactly zero. The gap is instance selection or trigger coverage."*

## Decision

**Ship the lever OFF.** It stays, registered in the configuration registry and
gated by `qinst_egraph_retry_share_row` in `hooks/pre-push`, so the next lane can
re-ask the question with one environment variable and no patch — the same
disposition as `AXEYUM_QUANT_EGRAPH_RESERVE` after [ADR-1970].

The pre-registered decision rule was "net ≤ +1 ⇒ negative result; net ≥ +4 ⇒
propose shipping". The realised **+2 falls in the gap between them**, which I did
not specify in advance, so both readings are recorded rather than the one I
prefer being chosen after the fact:

- **For shipping:** two gains that survive three runs per arm and agree with
  `:status`, z3 4.13.3 and cvc5 1.3.4; zero stable losses; both controls flat.
- **Against, and it is what decides it:** the lever's stated rationale is
  **refuted**. The family it was built for — 87 rows across four divisions that
  stop with a third of their clock unspent — is **0 for 87** when handed exactly
  that clock, against a genuine one-way ceiling. The +2 is a side effect on a
  *different* population, through a mechanism now measured to be **non-monotone**
  in the budget: the same change that produced three gains also produced the
  apparent loss, and only the re-check distinguished them. Shipping a change
  whose measured benefit nobody can explain, on a rung where more budget is known
  to be able to make things worse, buys two files and spends the ability to
  reason about the ladder.

**What the next lane should NOT do:** reach for a clock on this rung. The ceiling
is one-way and it is worth zero on the family that looks clock-bound.

**What the measurement points at instead:** instance *selection*. The ceiling arm
admits **391 rounds** and **787 ground terms** on `f2_rw120` and refutes nothing;
`UF`'s largest family is 69 rows of `Fixpoint`, where by the loop's own
documentation more rounds and more clock are worth exactly zero. Three divisions
agree.

**The one narrow question the +2 leaves open**, and it is worth one cheap lane:
both confirmed gains came from the **root-deadline** family (115 rows across
`UFNIA`/`UFLIA`), not from the retry's-own-slice family. Whether ~2 in 115 is a
real rate there is answerable by re-running this same binary and lever on that
population alone — no new code, no new harness.

[ADR-1970]: adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md
[ADR-1975]: adr-1975-valid-universal-elimination-spends-24-seconds-to-prevent-a-107-millisecond-refutation.md
[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
