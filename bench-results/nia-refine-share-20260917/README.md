# NIA-REFINE-SHARE — is ADR-2136's loss the SLICE or the LEMMAS?

Lane A13-NIA, ADR-2148. ADR-2136 built z3's order and monotonicity lemma
classes behind `AXEYUM_NIA_ORDER_LEMMAS` and measured 10 stable gains against 3
stable losses over 800 files. Its D1 attributed the three losses — all
`unsat → unknown` — to arming also widening `RefinementSetup::refine`, which
granted the loop a larger share of the per-file budget and starved a later
ladder route. This lane separates the two ("emit the lemmas" versus "widen the
slice"), scores the split on the 13 files that moved, and then A/Bs the arm
that keeps the most.

Host: s7 (AMD 7840HS, 16 threads, uutils `date` — every timing here is
`$EPOCHREALTIME` with a 200 ms self-check before each sweep), corpus on
`/nas3`. Cores `1` and `3` for the two shards (one sibling of each pair), `5`
and `7` for single-file probes.

## 1. Sizing — where the lever reads, and what the three losses actually are

### 1.1 Read sites at head (`f7cd4195f`)

- `nia_linearize.rs::check_with_nia` reads `nia_order_lemmas_enabled()` once
  and threads it into `check_with_nia_armed`.
- `RefinementSetup::refine` was
  `mccormick + splits > 0 || (order_lemmas && !rewritten_triples.is_empty())`
  and did TWO jobs: `solve_with_refinement` iterates past a spurious model only
  when it is true, and `NiaRefinementPolicy::slice(config.timeout, setup.refine)`
  selected `remaining / NIA_MCCORMICK_BUDGET_SHARE` (a third) when true and the
  600 ms `NIA_SLICE_MS` hang guard when false. That is the coupling ADR-2136
  §C named and this lane splits.

### 1.2 The 13 scoring files re-derived at head, 3× per arm

`recheck-movers-env.sh` (ADR-2136's own), head binary
(`4dd1f8a1…2044`), `AXEYUM_NIA_ORDER_LEMMAS=0` vs `=1`, 24 s / 8 GiB, cores 1
and 3 (`head-recheck-a.tsv`, `head-recheck-b.tsv`; `redo2`/`redo3` are the
three rows re-run on a quiet core after a `cargo build` on the same host
overlapped them — see §1.4).

| file | ADR-2136 | at head | note |
|---|---|---|---|
| `From_T2__n-21…` (held-out) | STABLE-LOSS | STABLE-LOSS | decides at the budget edge (§1.3) |
| `305.smt2` (held-out) | STABLE-GAIN | STABLE-GAIN | |
| `39.smt2` (held-out) | STABLE-GAIN | UNSTABLE (B 2/3, then 1/3) | marginal gain, load-sensitive |
| `f2_rw160` … `int_check_bvugt…` (7 UFNIA) | STABLE-GAIN ×7 | STABLE-GAIN ×7 | |
| `From_T2__ex36…` (pinned) | STABLE-LOSS | STABLE-LOSS (redo) | |
| `From_T2__n-7…` (pinned) | STABLE-LOSS | STABLE-LOSS (redo) | |
| `Larraz…Iteration6…` (pinned) | STABLE-GAIN | STABLE-GAIN | |

12 of 13 reproduce at head; `39.smt2` is a marginal gain.

### 1.3 The three losses, per route, both arms (`traces/`, `--trace` + `AXEYUM_NIA_DEBUG=1`)

| file | arm | `mccormick` / `splits` | `refine` | `nia-linearize` | `int-blast-ladder` | verdict |
|---|---|---:|---|---|---|---|
| `n-21` | 0 | 0 / 100 | **true (shipped)** | declined, 6,644 ms (slice exhausted) | declined, 13,345 ms | unknown (traced); unsat 3/3 untraced |
| `n-21` | 1 | 0 / 100 | true | declined, 6,651 ms | declined, 13,330 ms | unknown |
| `ex36` | 0 | 0 / 136 | **true (shipped)** | **decided unsat, 3,191 ms** | — | **unsat** |
| `ex36` | 1 | 0 / 136 | true | declined, 6,666 ms | declined, 13,325 ms | unknown |
| `n-7` | 0 | 0 / 82 | **true (shipped)** | **decided unsat, 2,224 ms** | — | **unsat** |
| `n-7` | 1 | 0 / 82 | true | declined, 6,669 ms | declined, 13,520 ms | unknown |

**ADR-2136 D1's attribution does not hold on its own three files.** All three
carry small-domain splits (`splits > 0`), so `refine` is already true and the
slice already `remaining / 3` (≈ 6.65 s) in the SHIPPED arm; arming widens
nothing there. And no later route is starved: on `ex36` and `n-7` the shipped
arm is decided by `nia-linearize` ITSELF, in 2–3 s of its 6.65 s slice, and
the armed arm's `nia-linearize` runs out of the same slice without reaching
`unsat`. `n-21` is the same shape at the slice's edge: at a 60 s budget both
arms are decided by `nia-linearize` (`unsat`, 5.9 s shipped vs 6.3 s armed,
3 interleaved pairs), which at 24 s is a 6.65 s slice the shipped loop just
fits and the armed loop does not.

The cost is inside the loop. With `AXEYUM_NIA_DEBUG=1` (`rounds/`): on `n-7`
the shipped loop refutes at round 1 (`relaxed=264`, 6.07 s left); the armed
loop adds 20 order/monotone lemmas at round 0 (`relaxed=284`) and the lazy LIA
driver then spends the whole 6 s on round 1 ("exhausted the configured timeout
after 94 rounds this solve"). On `ex36`: shipped `unsat` at round 3 with 5.2 s
left; armed adds 24+3+3 lemmas and is at round 3 with 0.77 s left, `unknown`.
The extra lemmas make the per-round relaxation harder for the lazy LIA driver
to refute, on exactly the Farkas/template files it refutes quickly without
them.

### 1.4 A measurement hazard, recorded

A `cargo build` of the split binary (16 threads, ~2 min) ran on s7 while the
head recheck shards were on cores 1 and 3. Three rows overlapped it and came
out UNSTABLE; re-run on a quiet core (`head-recheck-redo2.tsv`,
`head-recheck-redo3.tsv`) `ex36` and `n-7` are STABLE-LOSS and `39.smt2` is
UNSTABLE (B 1/3). Never build on the measurement host during a sweep; the
class-selector binary was built on s4 and copied.

## 2. The split (`1505f035c`)

`AXEYUM_NIA_ORDER_LEMMAS` keeps its meaning (emit the classes; on a
product-bearing query the loop iterates so they are reachable) and no longer
touches the slice. `AXEYUM_NIA_REFINE_SHARE=N` (ships `0`) grants
`remaining / N` on a product-bearing query whose entailed bounds produced
nothing; `0` keeps the 600 ms hang guard. `refinement_setup` computes the two
independently; `=1`/`=3` is byte for byte ADR-2136's B arm. Five unit tests
and mutation suite `nia-refine-share` (three couplings, each killing exactly
one distinct test) pin it.

## 3. The 2×2 on the 13 files (`quad.sh`, `quad-a.tsv`, `quad-b.tsv`)

One binary (`e6feebd0…2df2`), four env settings, 3 passes per arm interleaved
within each pass, 24 s / 8 GiB, cores 1 and 3. A file is DECIDED for an arm
only when all three passes decide.

| file | L0S0 shipped | L1S0 lemmas, old share | L0S3 no lemmas, share 3 | L1S3 ADR-2136 B |
|---|---|---|---|---|
| `n-21` (loss) | UNDECIDED¹ | UNDECIDED | MIXED (1/3) | UNDECIDED |
| `305` (gain) | UNDECIDED | **DECIDED** | UNDECIDED | DECIDED |
| `39` (gain) | UNDECIDED | **DECIDED** | UNDECIDED | DECIDED |
| `f2_rw160` (gain) | UNDECIDED | **DECIDED** | UNDECIDED | DECIDED |
| `t3_rw96` (gain) | UNDECIDED | **DECIDED** | UNDECIDED | DECIDED |
| `f2_rw120` (gain) | UNDECIDED | **DECIDED** | UNDECIDED | DECIDED |
| `t3_rw25` (gain) | UNDECIDED | UNDECIDED | UNDECIDED | **DECIDED** |
| `t3_rw21` (gain) | UNDECIDED | **DECIDED** | UNDECIDED | DECIDED |
| `f2_rw163` (gain) | UNDECIDED | **DECIDED** | UNDECIDED | DECIDED |
| `int_check_bvugt…` (gain) | UNDECIDED | **DECIDED** | UNDECIDED | DECIDED |
| `ex36` (loss) | MIXED (1/3)¹ | UNDECIDED | MIXED (2/3) | UNDECIDED |
| `n-7` (loss) | **DECIDED** | UNDECIDED | DECIDED | UNDECIDED |
| `Larraz…` (gain) | UNDECIDED | UNDECIDED | UNDECIDED | **DECIDED** |

¹ Three sweeps shared the host during this run; `n-21` and `ex36` are decided
by the shipped arm at the slice's edge (§1.3) and did not fit it here. They
are counted as losses regardless, since the armed arm never decides them.

**Reading.** The share is not the mechanism of the losses: `L1S0` keeps all
three. It is the mechanism of two gains: `t3_rw25` and `Larraz…` are decided
only with `ProductShare(3)` (their queries have no entailed-bound structure,
so without the share the loop has 600 ms). The other 8 gains decide inside the
hang guard (`f2_rw160` in 606 ms, the four others in 106–506 ms, `305`/`39`
carry splits and already had the wide slice). `L0S3` gains nothing: a wider
slice with only tangents to cut is the pure budget tax `refine` was written to
refuse.

**So no quadrant ships by the criterion.** `L1S0` keeps 8 of 10 gains and all
3 losses; `L1S3` keeps 10 and all 3. The loss is the lemmas themselves, on the
`splits > 0` family, inside the slice they already had.

## 4. Which class costs the losses — `AXEYUM_NIA_ORDER_LEMMAS=2` (order only) / `=3` (monotonicity only)

Per-round lemma counts under the ADR-2136 arm (`rounds/f*-L1S3.txt`): the
seven UFNIA gains are decided by ONE lemma per round (1–2); `305`/`39` by
26–28 at round 0; `Larraz…` by 51; the three losses build 20–39 at round 0.
A per-round cap cannot separate them. Whether one CLASS can is §4.1.

### 4.1 The class 2×2 (`quad-classes.sh`, `quadc-a.tsv`, `quadc-b.tsv`) and the iteration control (`tangents-a.tsv`, `tangents-b.tsv`)

`770d23545` makes the lever a mode: `2` = order class only, `3` = monotonicity
only, `4` = NEITHER class — the loop iterates on a product-bearing query
exactly as the armed arms do, cutting spurious models with tangent planes
only. Mode 4 is the control ADR-2136 §C introduced inside its one lever and
never measured apart. Class runs on cores 1/3 (binary `150fedb9…8384`), mode
4 on cores 5/7 (`72816651…eaab`, `recheck-movers-env.sh` with A = share 0,
B = share 3), 3× per arm.

| file | Order S0 | Order S3 | Monotone S0 | Monotone S3 | Tangents S0 | Tangents S3 |
|---|---|---|---|---|---|---|
| `n-21` (loss) | ✓ 10.7 s | ✓ | ✓ 9.3 s | ✓ | edge (0/3) | edge (1/3) |
| `305` (gain) | ✓ | ✓ | ✓ | ✓ | ✗ | ✗ |
| `39` (gain) | ✓ | ✓ | ✗ | ✗ | ✗ | ✗ |
| `f2_rw160` (gain) | ✓ | ✓ | ✓ | ✓ | **✓** | **✓** |
| `t3_rw96` (gain) | ✓ | ✓ | ✓ | ✓ | **✓** | **✓** |
| `f2_rw120` (gain) | ✓ | ✓ | ✓ | ✓ | **✓** | **✓** |
| `t3_rw25` (gain) | 2/3 | ✓ | ✗ | ✓ | **✓** | **✓** |
| `t3_rw21` (gain) | ✓ | ✓ | ✓ | ✓ | **✓** | **✓** |
| `f2_rw163` (gain) | ✓ | ✓ | ✓ | ✓ | **✓** | **✓** |
| `int_check…` (gain) | ✓ | ✓ | ✓ | ✓ | **✓** | **✓** |
| `ex36` (loss) | ✗ | ✗ | ✗ | ✗ | **✓ kept** | **✓ kept** |
| `n-7` (loss) | ✗ | ✗ | ✗ | ✗ | **✓ kept** | **✓ kept** |
| `Larraz…` (gain) | ✗ | ✓ | ✗ | ✓ | ✗ | **✓** |

**Eight of the ten ADR-2136 gains are iteration gains, not class gains.** The
seven UFNIA files and `t3_rw25` decide under mode 4 with no class lemma at
all (their per-round logs under the ADR-2136 arm show ONE order/monotone lemma
per round, which was never the cut that mattered); `Larraz…` decides under
mode 4 with share 3. The classes are worth `305` and `39`, both of which need
the ORDER class. **The losses are the classes**: either class alone keeps
`n-21` (≤ 20 lemmas instead of 39) and still loses `ex36` and `n-7`; mode 4
loses nothing, because on an envelope file it IS the shipped code.

A third arm was written and rejected before it was measured on files: emit
the classes only in a round where the tangent pass added nothing
(`NiaRefinementNoNewLemma`, the round the shipped loop would have left). It
was unit-tested, then checked against the T1 ledgers: that decline occurs on
**0 of 200 `QF_NIA` and 0 of 200 `UFNIA` rows** (`bench-results/ledger/t1-*-db31113fa.tsv`) —
the tangent loop never stalls, it runs its slice out — so the arm is inert on
the corpus and was removed rather than shipped as a mode nothing reaches.

## 5. The A/B of mode 4 against the shipped default (`launch-ab.sh`)

Two A/Bs, one binary (`72816651…eaab`), the shipped setting
(`AXEYUM_NIA_ORDER_LEMMAS=0 AXEYUM_NIA_REFINE_SHARE=0`) against mode 4 with
the hang guard (`=4 =0`, s7 cores 1, 9, 3, 11) and against mode 4 with share
3 (`=4 =3`, cores 5, 13, 7, 15), interleaved per file, 24 s / 8 GiB, all
eight logical cores of four physical ones at once — conservative for a ship
gate and not for a gain, so every mover is re-checked 3× per arm afterwards.
Pinned `QF_NIA`, `QF_NRA` (control), `UFNIA`, and the held-out `QF_NIA` draw
ADR-2136 used (overlap with pinned 0/200).

### 5.1 Coverage and verdicts (`summarize-ab.py`, exits nonzero on a short sweep, a disagreement, or a `:status` contradiction)

| division | rows | shipped | **mode 4, hang guard** | shipped | **mode 4, share 3** |
|---|---:|---:|---:|---:|---:|
| `QF_NIA` (pinned) | 200/200 | 83 | 85 | 82 | 84 |
| `QF_NRA` (control) | 200/200 | 123 | 123 | 122 | 122 |
| `UFNIA` (pinned) | 200/200 | 54 | **60** | 54 | **61** |
| `QF_NIA` held-out | 200/200 | 81 | 81 | 82 | 81 |

**Disagreements (one arm `sat`, the other `unsat`): 0 of 800 in each A/B.
Verdicts contradicting the benchmark's own `(set-info :status)`: 0 of 800 in
each.** The control moves nothing (123 → 123, 122 → 122; the two shipped
columns differ by one because the two A/Bs ran on different core pairs at
the same time, and that file is the shipped arm at a budget edge, not a
mover in either A/B). Exit status of every run 0.

### 5.2 Movers, re-checked 3× per arm on a quiet core (`recheck-L4S0.tsv`, `recheck-L4S3.tsv`)

| | raw movers | STABLE-GAIN | STABLE-LOSS | UNSTABLE |
|---|---:|---:|---:|---:|
| **mode 4, hang guard** | 8 | **6** (all `UFNIA`) | **0** | 2 (`DivMinus…`, `Stroeder_15__NonTermination2…`: `sat` 6/6 on the quiet core — both arms decide them; the raw gain was load) |
| **mode 4, share 3** | 10 | **8** (`Larraz…` + 7 `UFNIA`) | **0** | 2 (`DivMinus…` `sat` 6/6; `529.smt2` — the one raw held-out LOSS — `sat` 6/6 in both arms) |

The eight stable gains of the share-3 arm are exactly the eight files the
13-file 2×2 predicted (§4.1): the seven `UFNIA` files ADR-2136 credited to
the lemma classes plus `t3_rw25`, and `Larraz…` which needs the share. **No
stable loss in either arm, across 800 files each.** The held-out `QF_NIA`
draw has no stable mover in either arm.

### 5.3 The held-out draw for the division that moved (`ab-L4S3-ufnia-heldout/`)

The criterion asks for a stable gain on a held-out list, and the held-out
draw ADR-2136 used is `QF_NIA`, where mode 4's effect is +0 on 200 pinned and
+0 on 200 held-out — the pinned gain it does show (`Larraz…`) is one file. The
division mode 4 moves is `UFNIA` (+7, 54 → 61), which had no held-out draw. So
the share-3 arm was run against the shipped default on the seeded, disjoint
200-file `UFNIA` held-out list ADR-2106's lane drew
(`bench-results/derived-order-20260915/heldout-lists/UFNIA.txt`, seed
20260915, excluding every pinned path and every ledger row; overlap with the
pinned list 0/200), four shards of 50 on cores 1, 3, 5, 7, same envelope.

| | rows | shipped | mode 4, share 3 | disagreements | `:status` contradictions | raw movers |
|---|---:|---:|---:|---:|---:|---|
| `UFNIA` held-out (`ab-L4S3-ufnia-heldout/ab-UFNIA-heldout.tsv`) | 200/200 | 51 | **58** | 0 | 0 | 7 gains, 0 losses |

Re-checked 3× per arm on a quiet core (`recheck-L4S3-ufnia-heldout.tsv`):
**6 STABLE-GAIN** (`f2_rw166`, `f2_rw292`, `f2_rw268`, `f2_rw290`, `f2_rw62`,
`t3_rw62`, all `unknown → unsat`), **0 STABLE-LOSS**, 1 UNSTABLE
(`test14-Microsoft.Boogie…get_IsAddrOf`, `unsat` 6/6 in both arms — the
shipped arm decides it too, at the budget edge). Every exit code 0.

## 6. The ship decision

**Mode 4 with share 3 ships**: `NIA_ORDER_LEMMAS_ARMED = 4`,
`NIA_REFINE_SHARE = 3`, ADR-2148 `accepted`. Against the criterion:

- **0 stable losses** — on 800 pinned+held-out files in each of two A/Bs and
  200 more on the UFNIA held-out draw, every raw loss re-ran as `sat`/`unsat`
  in both arms on a quiet core.
- **0 flips** (one arm `sat`, the other `unsat`): 0 of 1,800 rows.
- **0 `:status` disagreements**: 0 of 1,800 rows, checked by `summarize-ab.py`
  against each benchmark's `(set-info :status)`.
- **≥ 1 stable gain on pinned AND held-out**: pinned **8** (`Larraz…` in
  `QF_NIA`, 7 in `UFNIA`), held-out **6** on the `UFNIA` draw. On the `QF_NIA`
  held-out draw the arm has **0** stable movers, and that is stated rather than
  absorbed: mode 4's measurable effect is in `UFNIA` (54 → 61 pinned, 51 → 58
  held-out, +13 % each), where `q:skolem-qf` hands the nonlinear integer tail
  to the quantifier-free ladder; on `QF_NIA` it is +1 pinned, +0 held-out, and
  the control `QF_NRA` is +0/+0.

What does NOT ship, and why: ADR-2136's two lemma classes (modes 1–3). They
are worth `305` and `39` on the `QF_NIA` held-out draw and cost `ex36` and
`n-7` on the pinned list in every combination that emits them — a 2-for-2
trade with the losses on the `splits > 0` Farkas/template family the tangent
loop refutes alone. The classes stay behind the lever (`=1`, `=2`, `=3`) for
the lane that finds the shape on which they do not reshape a refutable
relaxation.
