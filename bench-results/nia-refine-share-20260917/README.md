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

(§4.1 and the A/B follow below once the class 2×2 completes.)
