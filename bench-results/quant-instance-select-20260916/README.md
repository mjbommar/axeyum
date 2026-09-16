# QUANT-INSTANCE-SELECT: sizing the instance-selection lever before building it

Lane `quant-instance-select`, ADR-2133. Population: ADR-2113's **53
reference-minimal UFLIA cores**, the same set QUANT-INSTANCE-PROBE used.
Envelope: release `smtcomp_cli --trace`, `--timeout-ms 24000`, `ulimit -v
8388608`, host **s6** (idle, load 0.02 at launch), pinned physical core pairs
`1,9` / `3,11` / `5,13` / `6,14`, four shards.

## Why this ran before any code was written

The lane was briefed to build generation- and relevance-bounded instantiation
with a per-round cap and an eager/lazy split. **Step 0 of a brief — does it
already exist? — answers yes for every pillar**, at `file:line` in
`crates/axeyum-solver/src/qinst_egraph.rs` at this lane's HEAD:

| briefed pillar | already shipped |
|---|---|
| per-term generation; cost `weight + generation` | `TermGenerations` `:4478`, `derivation_generation` `:4510` |
| queue in cost order, per-round cap | `budget_flood_slice` `:4256`; `FLOOD_ROUND_ADMISSION_CAP = 256` `:1225` |
| eager/lazy split on the generation axis | `FLOOD_EAGER_GENERATION_MAX = 1` `:1233` |
| throttle engagement floor | `FLOOD_THROTTLE_MIN_GROUND = 2048` `:1242` |
| incremental matching, new terms only | ADR-0112; module doc `:16-22` |
| nested universals registered for matching | `AXEYUM_NESTED_QUANT`, default **ON** (`config_registry.rs:7045`) |
| generation-bounded final check | `FLOOD_FINAL_SUBSET_MAX_GENERATION = 1` `:5235` |

The reference design the brief cites is the same one already implemented:
z3 `qi_queue.cpp` cost `(+ weight generation)` and its eager/lazy thresholds,
`smt_enode.h`'s per-e-node `m_generation`, `mam.cpp`'s match-only-new-terms
incrementality; cvc5's `instMaxLevel` / `instWhenMode`. The shipped
`FLOOD_EAGER_GENERATION_MAX` doc comment names `qi.eager_threshold` explicitly.

So the lane's first deliverable is not a lever. It is the measurement that says
what the shipped machinery does on this population — and that measurement
retired the briefed lever.

## The three headline numbers

**1. The per-round cap does engage — on 14 of 26 cores — but it acts on 0.30 %
of the rejected traffic.**

Pooled over all 53 cores with the admission census on (7,328,804 rejections):

| rejection | count | share |
|---|---:|---:|
| `rej_nocontext` (no `PositiveContext` licenses the instance) | 2,642,864 | **36.06 %** |
| `rej_poscap` (positive-replacement cap) | 2,009,088 | 27.41 % |
| `rej_seen` | 1,392,171 | 19.00 % |
| `rej_true` (congruence already makes the clause true) | 1,173,037 | 16.01 % |
| `rej_handoff` | 68,352 | 0.93 % |
| **`rej_flood` (the per-round cap's own truncation)** | **21,886** | **0.30 %** |
| `rej_dupother` | 21,406 | 0.29 % |

Seven of thirteen reject kinds are nonzero, which is the positive control that
the census is live. **Tuning a cap that truncates 0.30 % of the rejected
candidates cannot move this population**, whatever ordering it uses. The
dominant blocker remains `rej_nocontext` — ADR-2113 §4b's finding, and the same
mechanism QUANT-INSTANCE-PROBE re-derived from the other side when 46 % of z3's
own recovered instances turned out to be nested instantiations.

**2. On 22 of 35 open cores our ground set never reaches the generation z3's
refutation needs.** That is a REACH gap; no selection policy closes it, because
the needed instance is never built at all.

Of the 38 cores we do not decide, 35 leave a ground dump:

| | cores | median ground | terminal reason |
|---|---:|---:|---|
| `ours_maxgen < z3_maxgen` (never reach it) | **22** | 1086 | 16 `timeout-mid-round`, 3 `SHAPE`, 2 `CLOCK`, 1 `ground-ceiling` |
| `ours_maxgen >= z3_maxgen` (do reach it) | **13** | **516** | 7 `timeout-mid-round`, 5 `SHAPE`, 1 `CLOCK` |

Eight of the 22 admit **zero** instances. And on the 13 that do reach the right
depth, the ground set handed to the final check has a median of **516** terms —
which is not a set any ground checker drowns in, and is consistent with the
probe's result that our ladder refutes z3's own instance sets on 6 of 7 cores.

**3. z3 needs generation >= 3 on 25 of 53 cores; our one generation-bounded
final check only ever sees generation <= 1, and only above ground 2048.**

z3 `:max-generation`, per core, from `ref-cores.tsv` (`z3_maxgen`, which this
lane re-derived from `z3 -st` and confirmed is that statistic):

| z3_maxgen | 0 | 1 | 2 | 3 | 4 | 5 | 7 | 8 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| cores | 1 | 16 | 11 | 14 | 2 | 4 | 2 | 2 | 1 |

`<= 1`: 17/53. `<= 2`: 28/53. **`>= 3`: 25/53.**

Our own ground sets, pooled over the 37 cores that dump: gen0 52.7 %, gen1
16.8 %, gen2 22.4 %, gen3 7.8 %, gen4 0.3 %. So `FLOOD_FINAL_SUBSET_MAX_GENERATION
= 1` admits **69.5 %** of terms to the subset-first check — a weak reduction —
and `FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND = 2048` means that check does not run
at all on **26 of the 37** dumped cores (median ground **1061**).

## The increment this indicates, and the lever it ships behind

Not a per-round admission cap. A **generation LADDER on the final refutation
check**: try the ground set restricted to `gen <= 0`, then `<= 1`, … ascending,
stop at the first `unsat`, fall through to the unchanged full check otherwise.
`GENERATION_LADDER_LEVEL` (env `AXEYUM_QINST_GEN_LADDER`), `0` = shipped
behaviour byte for byte.

It cannot produce a wrong verdict in either direction: every layer is a subset
of the conjunction the full check already takes, and every member of that
conjunction is an original assertion or an admitted instance of an asserted
universal — so a layer's `unsat` refutes the whole set, a layer's non-`unsat`
is discarded rather than believed, and no layer can stop the full check from
running. It is strictly additive: `unknown` -> `unsat` and nothing else.

## Two measurement traps hit on the way, both of which printed a wrong number

- **`flood_slices` is itself census-gated.** `census.flood_slices +=
  usize::from(census.enabled)` (`qinst_egraph.rs:4273`), and `census_enabled()`
  reads a SECOND variable, `AXEYUM_QPROBE_CENSUS`, on top of `AXEYUM_QPROBE`.
  The first arm therefore reported `flood_slices = 0` on 26 of 26 cores, and
  "the selection machinery never engages" was written down before the census
  arm was run. The true figure is **14 of 26**. Both arms are kept (`size0/`
  unperturbed with the ground dumps, `size1/` with the census) because the
  census costs a hash lookup per pool term per round in a loop its own comments
  call perturbation-sensitive.
- **A join key that silently dropped every row.** The sweep writes
  `cap/<core>.txt` and `dump/<core>.dump`; joining `ref-cores.tsv` on the
  capture filename matched nothing, and the report printed `z3_maxgen=?` for
  all 53 while every other column looked right. `size-report.py` strips the
  `.txt` in one named place and says why.

## Files

| path | what |
|---|---|
| `size-report.py` | the analysis; reads both arms, writes `sizing.tsv` |
| `sizing.tsv` | one row per core: our verdict, ground, generation histogram, census counters, z3's columns |
| `size-sweep.sh`, `size-sweep2.sh` | the two sweep arms (staged under `/nas3/data/axeyum/lanes/quant-instance-select/`) |

Reproduce: `python3 bench-results/quant-instance-select-20260916/size-report.py`.
