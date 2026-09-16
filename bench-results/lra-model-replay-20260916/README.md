# What arithmetic is actually outside the incremental engine?

Status: **CENSUS COMPLETE. The question's premise is refuted.** No Rust
shipped, no A/B, no ADR — the round was closed after the census by the
coordinator.

## The question, and why it was asked

[ADR-2111](../../docs/research/09-decisions/adr-2111-qf-lra-what-the-same-simplex-does-differently.md)
found `QF_LRA`'s largest addressable undecided bucket is 32 rows that die
inside `lra.rs`'s offline Fourier–Motzkin fallback. `LRA-ATOM-SCREEN`
([`bench-results/lra-atom-screen-20260916/`](../lra-atom-screen-20260916/README.md))
then measured that admitting them to the online CDCL(T) engine decides
**nothing**: 10 were already admitted, 18 more enter at 16×, and all of them
stop at the same string, emitted from two call sites —

> `online CDCL(T) LRA model did not replay (arithmetic outside the
> incremental engine)` — `lra_theory.rs:491` and `lra_theory.rs:502`.

So: **what arithmetic?** The brief named the suspects — `ite` over reals,
`distinct`, real `/` by a non-constant, `to_real`/`to_int` mixes,
disequalities, Boolean structure the engine linearized away.

**Answer: on the measured population, none of the first four, and the
sentence is wrong about its own subject in 82 % of cases.** Every atom in
every file of the target population linearizes — `unsupported=0` on all of
them. There is no arithmetic outside the incremental engine. There are three
other things, and only one of them is a construct.

## The instrument

`census-patch{1,2,3}.py` patch a `scripts/lane-snapshot.sh` tree **only**;
nothing here touches the shipped crate. Behind
`AXEYUM_LRA_REPLAY_CENSUS=1` the patched binary prints, per query that
produced a candidate model:

* the atom-kind split read straight off the live `LraTheory`
  (`Order` / `Equality` / `Unsupported`), so it is the engine's own
  classification and not a re-derivation;
* how many `Equality` atoms the SAT assignment set **false** — the theory's
  documented no-op at `lra_online.rs:2610`;
* for every **original assertion that fails to replay**, the constructs its
  own atoms carry;
* at every reconstruction decline, **which** pressure was on: deadline
  already past, memory watchdog tripped, or neither.

Two design choices in the instrument are load-bearing.

**It keys on the failing ASSERTION, not on the atom population.** `replays`
(`lra_online.rs:5728`) evaluates the original assertion, so an atom the
theory dropped costs nothing when the Boolean skeleton satisfies its
assertion anyway — the same effect z3 buys deliberately with the relevancy
filter over `m_not_handled` (`theory_lra.cpp:1793-1810`). Counting offending
atoms overstates the wall; counting failing assertions does not.

**Construct names are not guessed.** `census_lin_refusals` mirrors
`AtomBuilder::linearize` (`lra_online.rs:3556`) arm for arm: a node that
function accepts is silent, a node it refuses is named. That function's
accepted set is exactly {real constant, real symbol, `RealNeg`, `RealAdd`,
`RealSub`, `RealMul` with one constant side} — `Op::RealDiv` has **no arm at
all**, so even `(/ x 2)` would leave the engine. It never comes up, because
nothing reaches the atom builder unlinearized.

**The third patch exists because of a near-miss.** The first smoke test came
back `LRAMODELPROBE site=simplex-declined`, and `Status::Unknown` from the
simplex covers four different events (`simplex.rs:1441` deadline,
`:1453` memory watchdog, `:1465` `MAX_PIVOTS`, `:2180` overflow-poisoned)
that demand completely different work. Without separating them the census
would have reported "the simplex declined" and let a reader supply their own
cause.

## Method

Two sweeps, both on **s7**, each pinned to one physical core pair, run
concurrently on disjoint pairs; 24 s budget, 8 GiB `ulimit -v` soft, `--trace`.
Timing via bash's `$EPOCHREALTIME` with a **unit self-check before any solve**
(s7's `date` is uutils and silently prints nanoseconds for `%3N`); both runs
read 205 ms for a 200 ms sleep.

| arm | binary | sha256 | env | cores |
|---|---|---|---|---|
| `baseline` | shipped `smtcomp_cli` at `4f81de9c1` | `1ca58672c11008f8a679df7868cbf77a62a3e0f86606b0f39a63a07536ba1de2` | (screen unset) | `1,9` |
| `census` | same tree + `census-patch{1,2,3}` | `7c6e8765ffefcd05a880191649ba3d76738c214a2aad69ef44b978a863ad14ce` | `AXEYUM_LRA_ATOM_SCREEN=16`, `AXEYUM_LRAMODELPROBE=1`, `AXEYUM_LRA_REPLAY_CENSUS=1` | `3,11` |

`AXEYUM_LRA_ATOM_SCREEN=16` is LRA-ATOM-SCREEN's measured level at which all
22 screen-refused rows of ADR-2111's 32 are admitted, so it is the level at
which the target population exists at all.

**Population, re-derived rather than inherited.** The pinned 200 is
re-extracted from `bench-results/board-ab-20260915/QF_LRA.tsv` (200 rows,
200 distinct corpus paths) and is byte-identical to the list LRA-ATOM-SCREEN
used; all 200 readable on the NAS corpus (`verify-list.sh`).

## The baseline, re-derived

Shipped binary, screen unset, s7 core pair `1,9`, all 200 files:

| verdict | files |
|---|---:|
| `sat` | 66 |
| `unsat` | 41 |
| `unknown` | 93 |
| **decided** | **107 / 200** |

200 of 200 exit 0. **This reproduces the board's 107 exactly.**

The census arm (screen 16×) decides the same 107 — 66 `sat`, 41 `unsat`,
0 gains, 0 losses, 0 flips — plus **8 rows that abort** (`exit=134`,
verdict `none`), all of them `unknown` at the baseline. LRA-ATOM-SCREEN
predicted 6 aborts at 16× on s5 with the shipped binary; this arm is a
different host and a binary doing extra per-model evaluation, so the two
counts are not the same measurement and 8 ≠ 6 is not a contradiction —
recorded rather than reconciled.

## The target population, and its denominator

A census block fires whenever the online CDCL(T) route produced a candidate
model and it failed. **53** of the 200 files do that. On **6** of them the
ladder then decides anyway by a later route (four `clocksynchro`, `sc-5`,
`ecoliMILP…` — all `sat`/`unsat`), so the wall cost nothing there. On **47**
the wall is the final answer.

The 47 and the 6 partition cleanly against an independent earlier
measurement: the 47 undecided are **exactly** the 53 ∩ LRA-TRACE's 93
undecided rows, and the 6 recoveries are exactly the 6 outside that list.
Restricted to the 47, LRA-TRACE's own `modelprobe` column (captured at the
SHIPPED screen, by a different lane, months of code ago) reads 30 `n/a`
(never reached the wall at the shipped screen), 11
`model-built-but-does-not-replay`, 6 `simplex-declined` — consistent with
this census once the screen is opened.

**The histogram is over those 47.**

## The histogram

| bucket | files | tableau | clock |
|---|---:|---|---|
| **no model** — Fourier–Motzkin witness extraction declined | **27** | ABSENT | still available |
| **disequality** — equality atom asserted FALSE; model built, replay failed | **11** | present | n/a |
| **no model** — simplex re-check refused at pivot 0 | **7** | present | **gone** |
| **no model** — Fourier–Motzkin declined | **2** | ABSENT | gone |

| | |
|---|---:|
| atoms the engine could not represent, summed over all 47 files | **0** |
| files with any `AtomKind::Unsupported` atom | **0** |
| files where the warm tableau was ABSENT | 29 |
| files where it was present | 18 |
| exit statuses in the population | 47 × exit 0 |

`fm-fallback-declined` and "tableau ABSENT" agree on 30 of 30 rows of the
unrefined 53 — the two readings are independent (one is this lane's probe
site, the other is `simplex_rows=n/a` in the shipped route trace) and they do
not disagree on a single file.

### The disequality bucket, per file

One parametric family plus one outlier. Every row has the model built, the
failing assertion(s) evaluating to `false` (never to an evaluation error),
and the offending atoms being equalities asserted false:

| file | equality atoms | asserted FALSE | assertions | failing |
|---|---:|---:|---:|---:|
| `sc/sc-7.base.cvc.smt2` | 218 | 103 | 29 | 1 |
| `sc/sc-9.base.cvc.smt2` | 280 | 135 | 37 | 1 |
| `sc/sc-11.base.cvc.smt2` | 342 | 162 | 45 | 1 |
| `sc/sc-13.base.cvc.smt2` | 404 | 192 | 53 | 1 |
| `sc/sc-15.base.cvc.smt2` | 466 | 224 | 61 | 1 |
| `sc/sc-17.base.cvc.smt2` | 528 | 254 | 69 | 1 |
| `sc/sc-19.base.cvc.smt2` | 590 | 282 | 77 | 1 |
| `sc/sc-21.base.cvc.smt2` | 652 | 308 | 85 | 1 |
| `sc/sc-23.base.cvc.smt2` | 714 | 341 | 93 | 1 |
| `sc/sc-25.base.cvc.smt2` | 776 | 371 | 101 | 1 |
| `sal/pursuit/pursuit-safety-16.smt2` | 650 | 392 | 217 | 2 |

The `clocksynchro_{2,4,6,8}clocks` family and `sc-5` hit the identical wall
and are rescued by a later route, so the disequality shape reaches **16** of
the 200 files and costs the verdict on **11**.



## What the histogram says, in words

The message names "arithmetic outside the incremental engine". Across the
whole target population the count of atoms the engine could not represent is
**zero**. Three different things are behind the one sentence.

### 1. The tableau never existed, so the witness is extracted by Fourier–Motzkin

The largest bucket. `simplex_rows=n/a` in the route trace — the warm simplex
is `None`, so `LraTheory::model` (`lra_online.rs:2439`) takes its `else`
branch into `solve_values`, a **full Fourier–Motzkin elimination of every
variable** that keeps a clone of the whole system per variable
(`lra_online.rs:3797-3808`), and it declines on its own budget with the
deadline still available.

Why the tableau is absent is the sharp part. The online route builds it with
`TableauAdmission::DenseCells` (`lra_online.rs:1308`), which refuses when
`m × (nvars+m) > MAX_TABLEAU_CELLS` (`simplex.rs:2090`) — **a dense-cell
count over storage that ADR-2111 made sparse**. The nonzero-based currency
already exists in the same file and is already used by the warm cube decider
(`lra_online.rs:2144`, `simplex.rs:2047-2063`); the online route simply does
not ask that question, and its own doc comment says so:

> "The online route keeps `TableauAdmission::DenseCells` byte for byte; only
> the warm cube decider asks the other question." — `lra_online.rs:1312-1314`

ADR-2125 already measured the two currencies disagreeing by three orders of
magnitude on one file (8,797,712 cells against 4,688 nonzeros, 188 KB of
actual storage). This bucket is that refusal, reached from the model side.

### 2. The clock was gone before the witness was read out

`LraTheory::model` re-runs `Incremental::check` before materializing
(`lra_online.rs:2443-2446`), and `Tableau::run` polls the deadline at pivot 0
(`simplex.rs:1441`), so an expired clock returns `Unknown` **before a single
pivot**. `Incremental::point` (`simplex.rs:2287`) takes `&self` and only
materializes — it does no solving. Every file in this bucket has
`deadline_passed=true`.

Where the budget went is in the same trace: on
`_standard_init5_ground.i_3_2_2.bpl_7.smt2`, `theory_propagate_ms=18781` of
24,000 — 78 % of the budget — buying **249 propagations against 1,186,982
decisions**, with 929,053,570 atom visits. `LraTheory::propagate`
(`lra_online.rs:2501`) loops over every atom on every call and runs up to two
full simplex probes per unassigned order atom (`probe_entails`,
`lra_online.rs:2539`). ADR-2111 §6 already sized this as "propagation is not
weak but **absent**"; this census shows it also *causes* the reported
"model did not replay" on these files.

This bucket is a **timeout wearing an incompleteness label**. Whether the
witness could simply be read out of the tableau is a HYPOTHESIS this lane did
not close: it holds only if `sync` moved nothing at the decline and the
materialized point satisfies the live system as it stands. `census-patch4.py`
is written and measures exactly those two things; it was not run before the
round closed. **Do not treat "the witness was already there" as measured.**

### 3. The disequality — the only actual construct

The model **was** built, the failing assertions evaluate to `false` (not to
an evaluation error, so no symbol is missing a value), and the only offending
atoms inside them are real equalities the SAT solver asserted **false**.

`TheorySolver::assert` drops exactly that case, and says so:

```rust
// Equality-false (disjunction) and unsupported atoms add nothing.
(AtomKind::Equality { .. }, false) | (AtomKind::Unsupported, _) => Vec::new(),
```
— `lra_online.rs:2610`, with the reasoning at `:2588-2593`.

The comment there asserts the case cannot arise: *"the driver only ever sets
equality atoms true anyway, since `check_qf_lra_online` does not abstract
bare equalities."* That is true of the **offline** `check_qf_lra_online`
driver it names. It is **not** true of the CDCL(T) driver this route uses:
`is_lra_atom` (`lra_online.rs:5580`) admits any `Op::Eq` over reals, so the
encoder gives every real equality a skeleton variable and the SAT solver sets
it either way. The census counts the false ones directly and finds them in
the thousands on some files.

The same drop is repeated at `lra_online.rs:1958` (propagation validity),
`:2082` (`cube_check`), and `:2610` (`assert`); the propagator skips these
atoms as targets at `:2513`, and the tableau opens no row for them
(`:3014`).

## How the references host it — `file:line`, both sides

### The disequality

| | mechanism | where |
|---|---|---|
| **axeyum** | dropped; the theory records the assignment and adds no constraint | `lra_online.rs:2610` |
| **z3** | **eager**: at `new_diseq_eh` the adapter emits three "triangle-eq" theory axioms over two non-strict bound atoms, and the SAT solver does the case split. The LP never sees a disequality. | `theory_lra.cpp:1076-1080` → `arith_eq_adapter.cpp:240-243` → `mk_axioms` `arith_eq_adapter.cpp:163-178`, axioms at `:208-210` (verified verbatim: `ctx.mk_th_axiom(tid, t1_eq_t2_lit, ~le_lit, ~ge_lit, …)`) |
| **z3 (old `theory_arith`)** | same adapter; the simplex core dropped disequality handling in Z3 2.0 — "Starting at Z3 V2.0, we split disequalities. So, we do not need to handle them." | `theory_arith_core.h:1453-1458`, comment at `:3146-3148` |
| **cvc5** | **lazy, model-driven**: queue the disequality; at full effort compare the `DeltaRational` assignment against the RHS and emit `(or (<= x y) (>= x y))` only when they are equal | queue `theory_arith_private.cpp:1046-1050` (`d_diseqQueue`, decl `theory_arith_private.h:276`); `splitDisequalities` `:4251`, the test at `:4271-4286` (verified verbatim); lemma built at `constraint.cpp:1281-1286`; invoked from `postCheck` at `:4006-4009` |

**cvc5's shape is the near one.** We already detect the violation — that is
precisely what the `replays` gate at `lra_theory.rs:498` does — and we turn it
into `unknown` instead of into a lemma and a continued search. The missing
piece is not a decision procedure; it is the loop-back.

### An atom the theory cannot represent (does not arise here, recorded for completeness)

| | mechanism | where |
|---|---|---|
| **axeyum** | `AtomKind::Unsupported`, a registered no-op; nothing distinguishes an irrelevant one | `lra_online.rs:378-380`, `:2610`, `:3014` |
| **z3** | records it, then at final check **filters by relevancy** before giving up — an unhandled term in an irrelevant branch does not cost a `sat` | `found_unsupported` `theory_lra.cpp:291-295`; the giveup loop `:1793-1810`; `eval_unsupported` `:1682-1688` |
| **cvc5** | defers to `nl::NonlinearExtension`, else marks the result model-unsound | `theory_arith.cpp:265-288`; division/`to_int` family refused at `theory_arith_private.cpp:1557-1566` |

### Real-valued `ite` (does not arise here — it is eliminated upstream)

z3 internalizes it in the **core**, not in arithmetic: a fresh enode with
congruence suppressed plus two gate clauses (`smt_internalizer.cpp:915`,
clauses at `:942-943`); `theory_lra::mk_ite_axiom` is dead code behind an
unconditional `return` (`theory_lra.cpp:1247-1249`). cvc5 purifies it to a
skolem plus `(ite c (= k a) (= k b))` (`term_formula_removal.cpp:300-311`).
Our front door evidently does the equivalent before the atom builder: `ite`
appears in 49 of the 200 files textually and in **zero** unsupported atoms.

## The text prior, and the two hypotheses it killed before any solve

`text-prior.py` counts tokens in the raw SMT-LIB, before parsing — an upper
bound, and a cross-check rather than a finding.

| construct | files (of 200) | occurrences |
|---|---:|---:|
| `ite` | 49 | 1,381 |
| `/` | 64 | 2,661 |
| `(not (= …))` | 24 | 440 |
| `distinct` | **0** | **0** |
| `to_real` | **0** | **0** |
| `to_int` | **0** | **0** |
| `is_int` | **0** | **0** |
| `declare-fun` arity > 0 | 13 | 86,883 |

`distinct`, `to_real`, `to_int` and `is_int` are structurally absent from
this population, so they cannot be the answer at any measurement. `ite` and
`/` are present in a third of the files and still produce zero unsupported
atoms — the rewriter removes them upstream.

## What this lane did NOT do

Scope was cut to the census by the coordinator mid-round. Reported as **did
not run**, not as a negative result:

* no Rust shipped, no `config_registry` entry, no lever;
* no A/B, no held-out draw, no mover recheck;
* no differential fuzzes;
* no ADR (2139 remains unallocated by this lane);
* `census-patch4.py` (the stranded-witness measurement) is written and
  compiles against the same anchors but **was not built or run**, so bucket
  2's "the witness was already there" remains a hypothesis.

## Files here

| file | what it is |
|---|---|
| `census-patch.py` | instrument part 1 — atom-kind split, offending atoms, construct naming |
| `census-patch2.py` | instrument part 2 — re-key the report on the failing ASSERTION |
| `census-patch3.py` | instrument part 3 — separate the four `Status::Unknown` causes |
| `census-patch4.py` | instrument part 4 — stranded-witness test. **WRITTEN, NOT RUN.** |
| `analyze-census.py` | parses the captures into `per-file.tsv` + `histogram.tsv` |
| `crosscheck.py` | target population vs LRA-TRACE's independent `modelprobe` column |
| `run-sweep.sh` | the sweep driver (clock self-check, pinned cores, per-file ledger) |
| `launch.sh` | single-launch guard — refuses a second writer on one output dir |
| `verify-list.sh` | re-derives the pinned 200 from the board and checks the corpus |
| `text-prior.py`, `text-prior.txt` | the construct prior |
| `qflra-200.txt` | the re-derived pinned list |
| `ledger-baseline.tsv`, `ledger-census.tsv` | per-file verdict/exit/ms/sha ledgers |
| `per-file.tsv` | the per-file census table |
| `histogram.tsv` | the histogram |
| `final-report.txt` | the raw output of the final analysis, unedited |
