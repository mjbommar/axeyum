# Roadmap 3.5 measured: no declined quantified file needs one of cvc5's six strategies

Measured 2026-09-10 on `s4` at `474423c8d`. Roadmap item 3.5
([`11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md))
lists six quantifier instantiation strategies cvc5 has and we do not —
conflict-based (QCF), CEGQI, enumerative/full-saturate, pool-based, SyGuS,
sub-conflict — and sets the gate:

> "The UF corpus's declined files (dated 2026-09-09 comment in `auto.rs`) —
> classify which strategy each needs."

**The classification came back with a different answer than the item's framing
expects. Recommendation: DO NOT BUILD any of the six.** The blocker on the
files we decline is not a missing strategy family. Two cheaper defects account
for the population, both inside machinery we already have, and both are named
with a measurement below.

The evidence that settles it in one line: **z3 refutes 18 of the 32 seed files
in the same 24 s budget, using the same strategy family we have (E-matching +
MBQI) and none of cvc5's six.** We refute 0. A gap our own reference solver
closes without the six strategies is not evidence for the six strategies.

## The question, as a number

For each quantified file we decline, which specific instantiation strategy would
decide it?

| population | what it is | files | we decide | we decline |
|---|---|---|---|---|
| A | the 32 UF parity losses named in the seed comment (`bench-results/parity-losses-20260908/UF.txt`) | 32 | 0 | **32** |
| B | random sample of NAS SMT-LIB 2024 `UF`/`UFLIA`/`UFNIA`, 60 per division, seed 20260910 | 180 | 56 | **124** |
| C | every quantified file in `corpus/regression` | 12 | 5 | **7** |

**224 quantified files examined, 163 declined.** Of the declined, 92 carry a
declared `:status` of `sat`/`unsat` — 32 in A (30 `unsat`, 2 `unknown`-declared),
53 in B, 7 in C. An undecided file whose declared status is `unknown` cannot
support a claim that some strategy "would decide it", so the attribution table
below uses the 92.

### Denominator honesty

`corpus/regression` holds **12** quantified files and they are one family
(`uflia_induction`). That is far too small and too homogeneous to settle this
question on its own — the same finding items 3.6 and 3.1 reported. Everything
load-bearing here comes from the NAS divisions; population C is reported because
it is what a reader can reproduce without the mount, and because its profile is
genuinely different (see "What population C adds").

## Method

Item 1.8 landed `route_trace::quant_rung` (`828607b95`, 2026-09-09) so the
quantified ladder records the rung that decided or failed. That is the
instrument, per the brief — not stderr. Route attribution is collected by
`smtcomp_cli --trace`, which prints `; route decided_by=… bound_by=…` and a
`; route-trail <json>` carrying per-segment `elapsed_ns`, and prints both as
`; partial …` plus a `; route-open ms=… after=…` line when the watchdog kills
the worker mid-rung.

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
AXEYUM_QTRACE=1 AXEYUM_QPROBE=1 \
  ./target/release/examples/smtcomp_cli <file.smt2> --timeout-ms 24000 --trace
```

24 s is the budget in `bench-results/parity-losses-20260908/MANIFEST.json`, so
population A is measured at the budget its loss list was produced at. Runs were
`taskset`-pinned to the P-cores; load average over the sweeps was 1.9–10.4.

**Coverage / positive control.** The instrument fires: on
`corpus/regression/uflia_induction/unguarded_int_nonneg.smt2` the trail is
`fd:parse → q:ground-subset(declined) → q:skolem-qf(probe) → … → q:skolem-qf
decided sat`, and on `guarded_sum_gauss.smt2` it reports
`; partial route decided_by=none bound_by=q:mbqi-quick … attempts=6` plus
`; partial route-open ms=17771 after=q:mbqi-quick`. Both halves — a closed
decision and a watchdog kill — produce a usable trail. Every file in all three
populations produced a trail; none was silently skipped.

### Two hazards found in the instrument itself

Both matter for anyone re-running this, and both are recording defects left by
item 1.8's part 1, not measurement error:

1. **`q:egraph` reports `not-applicable` no matter why the loop gave up.**
   `run_egraph_quantified_fallback` (`auto.rs:285-292`) maps every
   `Ok(Sat | Unknown)` to `DeclineReason::NotApplicable`, discarding the
   `UnknownReason` the loop returned. So the trail's reason for the single most
   expensive quantified rung is uninformative — the loop's real message has to
   be recovered from `AXEYUM_QPROBE`. Same shape as the `decide_instantiation`
   problem the 2026-09-09 comment itself was written to fix, one rung over.
2. **`q:mbqi`'s wall clock is attributed to `q:uf-fmf-full`.** In the ladder's
   tail (`auto.rs:445-513`) MBQI runs first but `q:uf-fmf-full` is recorded
   *before* `q:mbqi`, so the segment between the previous record and
   `q:uf-fmf-full` covers **both** runs and `q:mbqi` always shows ~0 ms.
   `bound_by=q:uf-fmf-full` therefore means "MBQI plus the full finite-model
   finder", never the finder alone.

A third hazard is in `AXEYUM_QTRACE`, not in `RouteTrace`: `qtrace`'s `+Xs` is
**cumulative** for the five stages that share `solve_quantified_ladder`'s single
`t0` (`auto.rs:328`) and **per-stage** for `mbqi-quick` and `nat-induction`,
which take their own. Subtracting consecutive `+Xs` values yields negative
"costs". Per-rung wall clock in this note comes from the trail's `elapsed_ns`,
which is per-segment by construction.

## Finding 1 — the seed comment's substance holds; its named disjunct has moved

The 2026-09-09 comment in `auto.rs:8809-8820` says:

> "on 26 of the 32 files the loop stops at its accumulated-ground ceiling
> (`e-matching: ground-term count budget exhausted`) or at its final refutation
> check"

Re-measured on the same 32 files at 474423c8d:

| what the e-graph loop reported | files |
|---|---|
| `e-matching instantiation did not refute within the round budget` (the **final refutation check**) | 25 |
| `e-matching: instantiation time budget exhausted` | 4 |
| both, across the two invocations | 1 |
| no probe line (killed before the retry) | 2 |
| `e-matching: ground-term count budget exhausted` | **0** |

Separately, **24 of 32 did reach the 8192 accumulated-ground ceiling** in at
least one invocation (`QPROBE egraph-fixpoint … ground=8192`). So the comment's
disjunction is still true in substance — the loop stops at the ceiling *or* at
the final check — but the branch that actually returns is the **final refutation
check**, not the ceiling, and the ceiling message the comment names is now
emitted by nobody in this population. `AXEYUM_QPROBE` reports **zero
`skolem-bail` on all 32**, which is the one part of the comment that is
unchanged and exactly right: the skolemizer reaches every file.

That distinction is the whole finding, because "stopped at a ceiling" and
"searched, saturated, found no refutation" call for opposite work.

## Finding 2 — it is not the ground ceiling (DO NOT raise it)

The ceiling has an env override, so this is directly testable.

```sh
AXEYUM_QINST_GROUND=65536 <same sweep>     # 8x the shipped MAX_GROUND_TERMS = 8192
```

Control that the override took: max `ground=` seen across the raw dumps is
**65536** in the arm and **8192** in the baseline.

| arm | files decided of 32 |
|---|---|
| shipped (`ground=8192`) | 0 |
| `AXEYUM_QINST_GROUND=65536` | **0** |

**An 8x ground-term ceiling flips nothing.** Eight times as many instances, no
refutation. The instances we are generating are not the ones the refutation
needs — generating more of the same kind does not help.

## Finding 3 — it is not the budget either

A throwaway probe ran the e-graph refuter *alone*
(`axeyum_solver::prove_quantified_unsat_via_egraph`) with the **whole** budget,
so the question "would this rung decide the file if nothing above it took a
slice first" is answered directly rather than inferred. Positive control: on a
hand-written two-line unsat query (`∀x. p(x)`, `¬p(a)`) the probe returns
`unsat 0ms`; the same probe returns `unsat` on the MBQI entry point too.

| arm | decided of 32 | median wall before giving up |
|---|---|---|
| solo e-graph, 24 s budget | **0** | 4.75 s |
| solo e-graph, 240 s budget | **0** | 4.02 s |

A **10x budget does not move the median wall clock at all**, let alone the
verdict. The refuter is not budget-bound: it stops on its own, early, and says
`did not refute within the round budget`. 28 of 32 abandon the search before the
24 s budget is spent; 5 abandon it in **under one second**.

## Finding 4 — z3 decides 18 of the 32 with the strategies we already have

The parity manifest scored these against cvc5/bitwuzla/yices and only z3 is
installed on `s4`, so z3 was run as an independent control. z3's default UF
configuration is E-matching plus MBQI — the same family as ours, and **none of
cvc5's six strategies**.

```sh
z3 -T:24 <file>
```

| | files of 32 |
|---|---|
| z3 `unsat` | **18** |
| z3 `timeout` | 14 |
| ours `unknown` | 32 |

Cross-tabulated against how long our own refuter searched before giving up:

| our refuter gave up after | z3 `unsat` | z3 `timeout` |
|---|---|---|
| **< 1 s** | **5** | **0** |
| 1–5 s | 6 | 5 |
| 5–20 s | 5 | 7 |
| ≥ 20 s (ran the budget out) | 2 | 2 |

**Every one of the five files our refuter abandons in under a second is a file
z3 refutes.** Three of them are tiny: `smtlib.1116374.smt2` has **6** universals
and our loop saturates at 656 ground terms in 322 ms; `uf.966336.smt2` has
**24** universals and our loop saturates at 273 ground terms in **41 ms**;
`smtlib.1098821.smt2` has **4** universals (2 of them triggerless) and saturates
at 424 ground terms in 904 ms. z3 refutes all three. A 4-universal unsat problem
is the case basic E-matching is *for*. Nothing in cvc5's conflict-based,
CEGQI, pool, SyGuS or sub-conflict machinery is required to decide it.

This is the measurement that closes the item. The gap is inside our E-matching —
premature saturation and instance selection — not in the strategies we lack.

## Finding 5 — 56% of the budget on declared-unsat files goes to a model finder

Wall clock per route segment, summed over all 32 seed files (from the trail's
`elapsed_ns`; the `OPEN-after-*` rows are watchdog-killed segments the trace
could not attribute):

```
    199668 ms   29.8%  q:uf-fmf-full          (>=100ms on 25 files)
    176329 ms   26.4%  q:uf-fmf-probe         (>=100ms on 31 files)
    164094 ms   24.5%  q:egraph               (>=100ms on 31 files)
     67465 ms   10.1%  OPEN-after-q:egraph    (>=100ms on  5 files)
     38613 ms    5.8%  q:mbqi-quick           (>=100ms on 30 files)
     20256 ms    3.0%  OPEN-after-q:mbqi-quick
      1972 ms    0.3%  q:forall-exists-witness
    668910 ms  total
```

`q:uf-fmf-probe` and `q:uf-fmf-full` are the **SAT-side finite-model-finding**
rungs. They can only ever turn an `unknown` into a checked `sat`; by
construction they cannot produce `unsat`. **30 of these 32 files are declared
`unsat`.** They take **56.2%** of the total wall clock. On 21 of the 32 the
widest single segment is one of them.

`q:uf-fmf-probe`'s share is not incidental. `probe_budget` (`auto.rs:4127`) is

```rust
fn probe_budget(config: &SolverConfig) -> SolverConfig {
    UFBV_ONLINE_PROBE_SLICE.apply(config, config.timeout)
}
```

— `UFBV_ONLINE_PROBE_SHARE = 2`, i.e. **half the caller's clock**, a constant
whose own doc comment says it is the *declared-sort `QF_UFBV` online probe's*
share and that "whether it is wrong here is unmeasured, and this lane did not
retune it" (`auto.rs:4131-4138`). It is measured now: on 32 declared-unsat UF
files it consumes 26.4% of the wall clock and cannot decide any of them. The
files where it costs almost exactly 12 000 ms of a 24 000 ms budget —
`smtlib.1116374` 12057, `smtlib.1098821` 12247, `uf.966336` 12103, `uf.573210`
12066, `dl_copy_invariant_19_2` 12092 — are the slice firing at its documented
fraction. On the three small files in Finding 4 the e-graph refuter received
**160 ms, 199 ms and 519 ms** while 23 s went to model finders on a query
declared unsat.

This is a budget-allocation defect, not a strategy gap. It is worth naming
separately because it is cheap and because on its own it does **not** close the
population: the solo runs in Finding 3 gave the refuter the entire budget and
still decided 0 of 32. Fixing the allocation buys the refuter time it currently
does not get; it does not fix what the refuter does with it.

## The per-file attribution table

Blocker class for each declined file, across all three populations (92 files
with a declared status; class from the trail plus the `AXEYUM_QPROBE` fixpoint
census):

| blocker | A (32) | B (53) | C (7) | total |
|---|---|---|---|---|
| **F. saturation** — the e-matching loop ran to completion below the ceiling and its instances did not refute | 7 | 14 | 6 | **27** |
| **E. ceiling** — the loop filled the 8192 ground cap and did not refute | 17 | 11 | 0 | **28** |
| **C. clock** — the watchdog killed a *refutation* rung mid-run | 8 | 8 | 1 | **17** |
| **D. clock** — the watchdog killed the *SAT-side* finite-model probe | 0 | 8 | 0 | **8** |
| **G. loop never ran** — declined or timed out above the e-matching rung | 0 | 9 | 0 | **9** |
| **A. fragment** — skolemizer bailed, or no quantified rung ran at all | 0 | 3 | 0 | **3** |

Read against the item's question — *which strategy would decide this file* —
the table says:

- **55 files (E + F) stop inside e-matching**, and Findings 2–4 say neither more
  instances nor more time changes their verdict while a solver with the same
  strategy family decides 18 of the 32 in A. Their blocker is **instance
  selection**: which trigger, which instance, in which order. cvc5's five
  trigger-selection modes and six match-generator classes are the relevant
  comparison point — not its six strategies.
- **25 files (C + D) are killed by the clock**, 8 of them inside a model finder
  running on a declared-unsat query (Finding 5).
- **12 files (G + A)** never reach e-matching at all; nothing about
  instantiation strategy applies to them.
- **0 files** were classified as needing conflict-based, CEGQI, enumerative,
  pool, SyGuS or sub-conflict instantiation, because no file in the population
  reached a state where those are the missing ingredient — the loop either did
  not finish, or finished having generated instances that an equivalent solver
  turns into a refutation.

### What population C adds

The 12 committed files have a genuinely different profile and it is worth
recording: `q:uf-fmf-probe` costs **0 ms** on all of them (they are `UFLIA`, not
pure UF, so the finder declines in one cheap scan), and 6 of the 7 declined are
class **F. saturation**. The budget-allocation defect in Finding 5 is specific
to the **pure-UF fragment**; the saturation defect is not.

### Trigger-health census (the one number that points at a real cvc5 feature)

Across population A the fixpoint census reports **10 451** universals carrying
**7 383** patterns and **640 triggerless** universals, with at least one
triggerless universal on **21 of 32** files, and **63 451 starved joins**
(a join truncated by its ceiling) across 24 files. A triggerless universal
cannot be instantiated by e-matching at all, which is the one place cvc5's
enumerative/full-saturate pass has a structural advantage. But the split is
**275 triggerless on the 14 files z3 cannot solve** versus **365 on the 18 it
can** — triggerless universals are *more* common on the files z3 refutes, so
they do not separate the population and cannot be the blocker on the files we
are losing.

## Soundness cross-check

Across all three populations, 51 verdicts we produced have a declared
`:status` to compare against. **51 agree, 0 disagree.** No wrong `sat`/`unsat`
was produced at any arm, including the 8x-ground-ceiling arm.

## Recommendation

**DO NOT BUILD** conflict-based (QCF), CEGQI, enumerative/full-saturate,
pool-based, SyGuS, or sub-conflict instantiation on this evidence. Not one of
the 92 attributable declined files was classified as blocked on any of them, and
a reference solver with none of them decides 18 of the 32 files that motivated
the item.

Ranked cheaper work the measurement does name, with the number each is grounded
in:

1. **Fix why the e-matching loop saturates early.** 27 files stop with the loop
   *finished* and no refutation, 5 of them in under a second with the whole
   budget available, and all 5 of those are files z3 refutes. `uf.966336.smt2`
   — 24 universals, 273 ground terms, **41 ms** — is the reproducer to start
   from. This is the largest and best-evidenced item and it is a defect in
   machinery we already have.
2. **Stop giving half the clock to a model finder on a declared-unsat query.**
   `probe_budget`'s `UFBV_ONLINE_PROBE_SHARE = 2` is documented as unmeasured
   for this call site; it costs **26.4%** of the wall clock on 30 declared-unsat
   UF files and 56.2% counting both SAT-side rungs. 8 further files in
   population B are killed by the clock *inside* that probe. Cheap, bounded,
   and independently useful.
3. **Repair the two item-1.8 recording defects** named under Method, so the next
   lane's attribution does not have to be recovered from `AXEYUM_QPROBE`:
   `q:egraph` should carry the loop's `UnknownReason` instead of
   `NotApplicable`, and `q:mbqi` should be recorded before `q:uf-fmf-full`
   rather than after it.
4. **Do NOT raise `MAX_GROUND_TERMS`.** Measured at 8x: 0 files flip.

## What I did not measure

- **cvc5 itself.** It is not installed on `s4` (`command -v cvc5` → nothing).
  Every claim about what cvc5's six strategies *would* do on these files is
  therefore an inference from where our own ladder stops, not a head-to-head.
  A cvc5 build plus a per-option ablation (`--no-cbqi`, `--full-saturate-quant`,
  `--no-e-matching`) on population A is what would upgrade Findings 4 and the
  attribution table from "the strategies are not implicated" to "the strategies
  are ruled out". That is the single highest-value follow-up.
- **Whether the 27 saturation files are refutable at all.** 14 of the 32 in A
  time out in z3 too. Declared `unsat` means some solver, once, refuted them —
  not that E-matching can.
- **CEGQI specifically.** Its target is quantified *arithmetic* and the
  populations here are UF-dominated. `UFLIA`/`UFNIA` are in population B but
  were not separated out by division in the attribution table. A CEGQI-specific
  measurement would need an `LIA`/`NIA`/`AUFLIA` population, which is a
  different item.
- **The `unknown`-declared files.** 71 of the 124 declined files in population B
  carry `:status unknown` and were excluded from the attribution table. They are
  the majority of what we decline on a random NAS draw, and nothing here says
  anything about them.
- **Contention.** The sweeps ran at load 1.9–10.4 on a 16-core box shared with
  other lanes, pinned to the P-cores. Verdict counts are robust to this; the
  wall-clock percentages in Finding 5 and the medians in Finding 3 are not
  pinned to a reference frame and should be treated as ratios, not absolutes.
- **Incremental / scoped quantified queries.** `corpus/incremental` was not
  swept; the whole measurement is one-shot `check-sat`.

## Reproducing

Probe code was throwaway and is not in the tree, per the Phase 3 brief. The
solo-rung probe was ~85 lines calling the two public entry points
`axeyum_solver::prove_quantified_unsat_via_egraph` and
`axeyum_solver::prove_unsat_by_mbqi` from a big-stack worker thread, modelled on
`crates/axeyum-bench/examples/route_solo.rs`; it is worth re-creating rather
than keeping, since `route_solo` already has the shape and only lacks the two
quantified routes in its table. The sweep harness, its raw per-file dumps
(224 files x 3 arms), and the parsers live in this session's scratchpad and are
not committed.

The populations are reproducible:

```sh
# A
cp bench-results/parity-losses-20260908/UF.txt /tmp/pop-A.txt
# B: 60 per division, sorted file list, random.Random(20260910).sample
#    over /nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/{UF,UFLIA,UFNIA}
# C
grep -rlE '\((forall|exists)\b' corpus/regression --include=*.smt2 | sort
```
