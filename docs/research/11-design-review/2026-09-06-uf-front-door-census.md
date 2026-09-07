# UF's 32 reference-only losses: half the budget goes to model finding on a population that is 100% refutation

Date: 2026-09-06. Lane `uf-front-door-census`.
Solver commit measured: `cc75cd023`. Host s7 (idle, load 0.14, 16 cores),
`taskset -c 0-7`, 24 s budget, release binary from a `git archive --touch`
snapshot, every invocation under `timeout -k 5 120`.
Artifacts: `bench-results/parity-losses-20260906/UF.front-door.census.tsv`
(per file: class, budget-spending stage, its share, wall, the corrected
per-stage ladder, and the qtrace line the attribution is read from), plus the
parser and runner beside it.
Population: `bench-results/parity-losses-20260905/UF.txt`, the 32 files cvc5 1.3.4
solves and we do not, from the 2026-09-06T22:35:13Z parity run (85 / 93,
61 both / 24 ours-only / 32 theirs-only).

Predecessors: the [S3 census](2026-09-05-parity-loss-census.md), whose UF class
was an artifact of `explain_corpus`; and
[S11a](2026-09-06-s11a-uf-ackermann-measured.md), which found that and left the
UF cause open.

## Method, and the one correction it turns on

`explain_corpus` is not admissible here — it runs `check_auto_explained` on the
flat assertion view, not `solve_smtlib`, and its own banner records that the two
disagree on 134 of 397 committed benchmarks. Every number below comes from
`uf_unknown_probe`, which is `solve_smtlib`, with `AXEYUM_QTRACE=1`.

The correction that makes the timing readable: `qtrace` prints
`since.elapsed()`, and `finish_quantified_solve` creates **one** `t0` and hands
it to `forall-exists-witness`, `finite-expansion`, `uf-fmf-probe`, `egraph`
(forwarded as `started`), `mbqi` and `uf-fmf-full`. Those six printed numbers
are **cumulative**; a stage's own cost is the difference from the previous
checkpoint. `mbqi-quick` and `nat-induction` carry their own `Instant`.
`egraph-seg` / `match-seg` / `nested-quant` are segment-local sub-stages inside
whichever top-level window they fall in, and are summed separately.

Reading a printed `+N s` as one stage's cost overstates it by everything above
it. S11a's "`uf-fmf-probe` costs 1.5 / 8.1 / 17.1 s on three of five traced
files" is that reading; the corrected per-stage costs on the same rung across
all 32 are 0.02–16.3 s, median 3.2 s.

Coverage check: the traced stages account for **679.7 s of the 688.0 s** of
total wall (98.8%), so nothing rests on an unmeasured remainder.

## Finding 0 — the population is 100% refutation, and that alone kills the
## finite-model-finding hypothesis

From `bench-results/parity-details/UF.tsv` at the parity run above, the 200-file
division splits nine ways:

| axeyum | cvc5 | declared | files |
|---|---|---|---:|
| unsolved | unsolved | unknown | 77 |
| **unsat** | **unsat** | unsat | **61** |
| **unsolved** | **unsat** | unsat | **30** |
| **sat** | unsolved | sat | **20** |
| unsolved | unsolved | unsat | 4 |
| unsolved | unsolved | sat | 2 |
| **unsolved** | **unsat** | unknown | **2** |
| **unsat** | unsolved | unsat | **2** |
| **sat** | unsolved | unknown | **2** |

**All 32 reference-only losses are cvc5 `unsat`.** Not one is satisfiable. The
2026-08 gap analysis named bounded finite-model finding as the UF lever; a model
finder searches for a model, so it cannot decide any of these 32. The hypothesis
is refuted by the population, before a single trace is read.

The inverse is just as sharp: **22 of the 24 axeyum-only wins are `sat`, and the
division has no sat/sat cell at all.** Every satisfiable UF file this division
decides, only we decide. Our UF strength is model finding; our UF weakness is
refutation, and they are the same fact seen from two sides.

## Finding 1 — the cause: 50.4% of the loss population's wall is spent in the
## finite-model finder we already ship

Summed over the 32 files (688.0 s of wall in total):

| stage | seconds | share |
|---|---:|---:|
| `egraph` | 190.8 | 27.7% |
| **`uf-fmf-full`** | **189.2** | **27.5%** |
| **`uf-fmf-probe`** | **157.8** | **22.9%** |
| `mbqi` | 103.0 | 15.0% |
| `mbqi-quick` | 38.8 | 5.6% |
| pre/post-ladder (parse, QF front door, skolemize) | 8.3 | 1.2% |
| `forall-exists-witness`, `finite-expansion`, `nat-induction` | 0.0 | 0.0% |

**347.0 s — 50.4% — goes to the two pure-UF finite-model-finding rungs, on 32
files every one of which is unsat.** The refutation family (`mbqi-quick` +
`egraph` + `mbqi`) gets 48.4%. Per file, a finite-model rung is the
budget-dominant stage on **16 of the 32**: `uf-fmf-full` on 9, `uf-fmf-probe`
on 7.

The two rungs are not equally at fault, and the difference decides the lever.

**`uf-fmf-probe` runs BEFORE the whole refutation family** —
`finish_quantified_solve` orders it `finite-expansion` → **`uf-fmf-probe`** →
`mbqi-quick` → `egraph` → `mbqi` → `uf-fmf-full` — and `probe_budget` hands it
`timeout / 2`. Its own doc comment says it is "cheap, cannot starve the
refutation family", on the strength of `UF_FMF_PROBE_SOLVE_ASSERTIONS = 2_000`.
Measured on this population that is false: on **7 of the 32 files the probe
spends 10.3–16.3 s** — five of them within a few milliseconds of exactly half
the budget (12 034 / 12 042 / 12 045 / 12 048 / 12 089 ms) — **before any
refuter has run**. That is budget theft in the strict sense: time taken from an
enclosing search, on queries the taker cannot decide.

**`uf-fmf-full` is terminal.** It runs after every refuter has declined and
nothing runs after it, so the 189.2 s it consumes is budget the ladder would
otherwise discard — the same shape S11a found at the declared-sort rung. It
costs no refutation time. It is still worth bounding, for Finding 3.

## Finding 2 — the second cause: the e-graph loop saturates its ground cap

`egraph` is the budget-dominant stage on 8 files and the largest single stage
overall (190.8 s). **25 of the 32 files reach `MAX_GROUND_TERMS = 8192`** in the
instantiation loop, and the 7 `search-timeout` files die there — `egraph`
dominant at 18.1–22.1 s of a 24 s budget, **all 7 with a last recorded
`ground = 8192`.**

Where inside the loop is answerable exactly, because the sub-stage traces stop
early. Summing every traced `egraph-seg` / `match-seg` / `nested-quant` segment
inside the `egraph` window and subtracting from the window's own cost:

| file | `egraph` window | traced segments | **untraced** | last `ground` |
|---|---:|---:|---:|---:|
| `x2015_09_10_16_46_58_732_1021788` | 21 867 ms | 662 | **21 205** | 8192 |
| `uf.974621` | 22 051 | 1 271 | **20 780** | 8192 |
| `uf.1065126` | 19 731 | 809 | **18 922** | 8192 |
| `uf.1158058` | 18 057 | 3 338 | **14 719** | 8192 |
| `uf.813308` | 18 316 | 6 067 | **12 249** | 8192 |
| `uf.1198393` | 21 039 | 12 907 | **8 132** | 8192 |
| `dl_remove_postcondition_of_dl_remove_50_4` | 21 498 | 18 356 | **3 142** | 8192 |

The untraced remainder is 3.1–21.2 s (median 14.7 s). It is not the loop's
prologue: `closed-universal done` and `targeted done` print `+0.000s` on all 7.
The only code between the last traced admission and the window's close is the
**cap-hit branch** at `qinst_egraph.rs:1341` — `if ground.len() > MAX_GROUND_TERMS
{ … quantifier_qf_refutation_check(…) }` — which is the one refutation call site
in the loop with no qtrace line. On `x2015…1021788` the loop reaches 8192 ground
terms at **round 2** (128 → 1 823 → 8192), admits two more rounds, and then the
window closes 21.2 s later with nothing traced in between.

This is the wall `FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND`'s own comment already
records — "a final check over 8192 conjuncts burned 26.7 s on `uf.1158058` and
returned unknown". `uf.1158058` is in this population and still does it.

The `mbqi` window is the same machinery a second time: `prove_unsat_by_mbqi` →
`prove_unsat_by_ematching` → skolemize → re-instantiate → the skolemized e-graph
loop on half the remaining budget. Its dominant sub-stages on the 8 files where
`mbqi` leads are `nested-quant nested-activity` (7 of 8) and `egraph-seg
qf-check` (6 of 8). So Finding 2's mechanism covers 16 of the 32 files across
two windows, not 8.

Rounds reached range from 4 to 511, and they do **not** cleanly separate the
classes — `search-timeout` spans 4–266 (median 14), residual-quantifier spans
7–511 (median 258). What the low-round `search-timeout` files show is the
damaging shape: the cap is not reached by patient search, it is **flooded in a
handful of rounds**, and the flood is then checked at full price.

## Finding 3 — the third cause: the budget is neither spent nor bounded

- **11 of 32 return with 5–19 s of the 24 s budget unspent** (5 313 ms at the
  low end). The ladder ran out of rungs, not out of time.
- **6 of 32 overshoot the 24 s budget**, and `smtlib.663965.smt2` runs
  **62 866 ms — 2.6x the budget — with 60 982 ms of it inside `uf-fmf-full`.**
  Under the 24 s scoring protocol that file is a loss no matter what it would
  eventually have decided.
- The overshoot is not specific to the model finder. With both finite-model
  rungs disabled by an env gate, `smtlib.573364.smt2` (an axeyum-only *win*,
  decided `sat` in 108 ms by the probe) ran past the external
  `timeout -k 5 120` — over **5x** its 24 s budget — inside the refutation
  family alone. Measured on 1 file; not generalised.

## What is refuted

| Hypothesis | Source | Status |
|---|---|---|
| Finite-model finding is the missing UF capability | 2026-08 gap analysis | **Refuted.** All 32 losses are unsat. The finder we already ship is the single largest consumer of their budget. |
| All 32 are the declared-sort CEGAR bound (64 pairs) | S3 census | **Refuted, independently of S11a.** No front-door trace or verdict on any of the 32 contains `congruence pair` / `Ackermann` / `declared-sort` (positive control: the same grep matches 102 times in `crates/axeyum-solver/src/euf.rs`). All 32 enter the quantified ladder — 32 of 32 print a `forall-exists-witness` line — so the quantifier-free UF ladder where that bound lives is not on their path at all. |
| Boolean search power (watched literals, VSIDS) | S1, S1b | **Refuted by measurement elsewhere**: neither slice moved this division. Consistent with this census — 0.0% of the loss wall is in a quantifier-free SAT search that either slice touches. |
| The losses are simply the big files | — | **Refuted.** The 32 losses (median 61.2 KB, 357 asserts, 420 `forall`s), the 61 both-solved (63.8 KB, 359, 417) and the 83 nobody-solved (60.7 KB, 355, 381) are indistinguishable on every size axis measured. Size does not separate what we lose from what we win. |

## What the 24 axeyum-only files have in common

1. **22 of 24 are satisfiable** (20 declared `sat`, 2 declared `unknown` and
   resolved by us). The other 2 are `unsat`.
2. **`uf_fmf` is what decides them.** Positive control and A/B arms: with both
   finite-model rungs gated off, the files that decide `sat` in 0.1–0.6 s return
   `unknown`. Nothing else in the ladder finds these models.
3. **They are an order of magnitude smaller than everything else in the
   division** — median 9.8 KB / 68 asserts / 46 `forall`s, against ~61 KB / ~357
   / ~420 for the losses, the both-solved, and the nobody-solved alike. Small
   enough that a bounded finite model exists and the finder reaches it.
4. **They are not a different corpus.** FFT, Fundamental_Theorem_Algebra, Hoare,
   Arrow_Order, TypeSafe and coinductive_list all appear on *both* sides of the
   division. The split is by satisfiability and size, not by source.

So the 24 are a genuine, defensible strength — and they are also the reason no
lever here may simply delete the finite-model finder.

## The lever test, run rather than argued

Finding 1 makes an obvious lever obvious: the probe takes half the budget before
any refuter runs, so give the refuters that time back. It was measured, on both
populations, before being recommended.

One binary, three env-gated arms on a throwaway snapshot (both measurement
patches are committed beside the artifacts; neither is proposed for the tree),
every arm run back to back per file so all arms see the same load.

**On the 32 losses** (idle s6, `taskset -c 0-7`, 24 s):

| arm | decided | PAR-2 (s) | wall (s) |
|---|---:|---:|---:|
| `base` (shipped, probe budget `t/2`) | **0** | 1536.0 | 690.5 |
| `probe16` (probe budget `t/16`) | **0** | 1536.0 | 733.8 |

Verdict changes: 0. The knob demonstrably fired — on
`x2015…1522663` the probe goes 5 817 ms → 1 957 ms, and on
`x2015…1048482` the whole file goes 26 535 ms → 18 930 ms — and **it moves
nothing.** Handing the refutation family back up to 10.5 s of a 24 s budget
changes no verdict on any of the 32.

**On the 24 wins** (idle s7, same protocol):

| arm | decided | PAR-2 (s) | wall (s) |
|---|---:|---:|---:|
| `base` | **24** | 20.8 | 20.8 |
| `probe16` | **23** | 59.1 | 35.2 |
| `nofmf` (both finite-model rungs off) | **2** | 1057.7 | 263.4 |

`nofmf` names the producer: with the finder gated off, all 22 `sat` wins become
`unknown` and only the two `unsat` files survive. `probe16` costs exactly one —
`smtlib.1262852.smt2`, which base decides at 8 616 ms. The other 21 decide in
1.1 s or less.

So the reallocation lever is **net −1 with zero upside**, and it is refuted.
The files that lose half their budget to the probe are not budget-starved; they
are capability-limited, and returning the time proves it.

Reproducibility: the s6 `base` arm and the s7 census — different hosts, and a
patched binary with its gates unset against an unpatched one — agree on
**verdict and detail for 32 of 32**.

## Recommendation

**1. No budget-reallocation lever is justified, and this is the finding, not a
gap in the work.** It was the one lever the cause analysis pointed at, it was
built and measured on both populations, and it moves 0 of 32 while costing 1 of
24. Do not spend a slice on re-tuning `probe_budget`, the ladder order, or the
`mbqi_first_refusal` fraction; the measurement above already answers all three
the same way.

**2. The lever the data does support is the flooded cap-hit refutation check.**

- *Change*: the `ground.len() > MAX_GROUND_TERMS` branch at
  `qinst_egraph.rs:1341` runs one `quantifier_qf_refutation_check` over the
  whole saturated 8192-conjunct set and spends 3.1–21.2 s (median 14.7 s) there.
  The generation-layered subset check the file already carries
  (`FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND`, `FLOOD_FINAL_SUBSET_MAX_GENERATION`)
  exists for exactly this shape. The slice is to establish why it is not what
  fires at the cap, and to bound that call.
- *Scoring population*: the 7 `search-timeout` files, named in Finding 2's
  table. All 7 reach `ground = 8192`; all 7 die in that call.
- *Exit criterion*: at least 3 of the 7 decide `unsat` inside 24 s; **0** verdict
  flips and **0** contradictions of a declared `:status` across the 61
  both-solved and the 24 axeyum-only; the full 200-file
  `bench-results/parity-lists/UF.txt` sweep does not lose a file.

**3. Fix the deadline before anything is tuned against it.** `smtlib.663965.smt2`
runs **62 866 ms** of a 24 s budget in the shipped binary, and **115 835 ms** in
the `probe16` arm. `smtlib.573364.smt2` — a file we decide `sat` in 108 ms — ran
past a 120 s external kill under `nofmf`. Under a 24 s protocol an overshoot is a
loss regardless of what the run would eventually have found, and it also makes
every budget measurement above noisier than it should be.

- *Scoring population*: the 200-file UF list.
- *Exit criterion*: no file exceeds 1.1x its budget; 85 decided is preserved
  exactly (the 6 overshooting files are already unsolved, so this cannot cost a
  decided file); 0 verdict flips.

**4. The largest single group needs capability, not tuning, and should be
scoped as such.** The 32 partition cleanly by what the clock did:

| | files | every one's class |
|---|---:|---|
| **A — returns with the budget unspent** (5.3–18.7 s of 24 s) | **11** | `route-decline(residual-quantifier)`, all 11 |
| B — spends the budget and ends `unknown` | 15 | 6 `search-timeout`, 8 residual-quantifier, 1 instantiation-satisfiable |
| C — overshoots the budget | 6 | 4 residual-quantifier, 1 `search-timeout`, 1 instantiation-satisfiable |

Group A is the sharpest statement in this census: **11 of 32 files run out of
routes, not out of time.** Every one ends at "query has quantifiers
instantiation does not reach (nested, existential, or non-top-level)" with
5–19 s of budget still on the clock. No scheduling change, no cap raise and no
faster search can move them; the instantiation engine has to reach a quantifier
shape it currently cannot. That is a capability slice (trigger coverage for
nested / existential / non-top-level quantifiers, the terminal decline in
`decide_instantiation`), and it is where the largest homogeneous group of this
division's losses lives.

Getting from 85 to 93 needs 8 of these 32. On the measured partition the
plausible supply is group B's 7 `search-timeout` files (lever 2) plus group A's
11 (lever 4). Nothing else in this census offers any.

## What was not determined

- **Whether raising `MAX_GROUND_TERMS` alone helps.** Not measured. The trace
  says the cap is reached in as few as 2–4 rounds and that the cost is in the
  check *over* the saturated set, so raising it plausibly makes that check
  worse — but that is an inference, not a measurement, and the A/B was not run.
- **Whether `CHAIN_INSTANCE_CAP = 4096` is what leaves the residual
  quantifier.** The code comment at `auto.rs:7448` says so for "the whole
  residual bucket on the scored UF corpus". This census confirms the *terminal
  message* on 23 of 32 but did **not** instrument which chains overflow, so the
  attribution to that constant is inherited, not re-measured here.
- **Where inside `find_uf_finite_model` the 189.2 s of `uf-fmf-full` and the
  157.8 s of `uf-fmf-probe` go.** There is no qtrace inside `uf_fmf`. It did not
  matter for this census — the lever was refuted at the rung boundary — but it
  would matter for lever 3.
- **The full 200-file UF sweep.** Did not run. Everything here is measured on
  the 32 losses and the 24 axeyum-only wins; the 61 both-solved and the 83
  nobody-solved were characterised by size only, never re-run.
- **Whether the `nofmf` 120 s overshoot on `smtlib.573364.smt2` generalises.**
  Measured on 1 file, in one arm. Reported as one observation.
- **`AXEYUM_NESTED_QUANT`'s default is documented in two places that
  contradict.** `quant_skolemize.rs:118` says "Default **ON** as of 2026-08-02
  (slice 4)"; the comment at `auto.rs:7423` still says "(default off)". The code
  agrees with the former (`is_none_or`). Not acted on here, but the stale comment
  is on the path anyone reading this census will take.
