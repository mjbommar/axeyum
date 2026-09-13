# QF_ABVFP, QF_BVFP, QF_UFBV — the FP/array and UF/BV divisions, first measured

**2026-09-12, lane `board-fpbv`.** `QF_ABVFP` (18,129 files), `QF_BVFP`
(17,249), `QF_UFBV` (1,510) — **36,888 files** — had never been run. These are
their first parity rows. The board moves from 20 of 84 SMT-LIB divisions to 23.

    axeyum  467 / 600  (77.8 %)
    z3      571 / 600  (95.2 %)
    cvc5    557 / 600  (92.8 %)

| division | files on disk | axeyum | z3 | cvc5 |
|---|---:|---:|---:|---:|
| QF_BVFP  | 17,249 | **199** | 200 | 197 |
| QF_ABVFP | 18,129 | **179** | 197 | 198 |
| QF_UFBV  |  1,510 |  **89** | 174 | 162 |

## The REACHED-SOLVER label: CONFIRMED at n = 200, on all three

`bench-results/session-20260911-smtlib/coverage/blockmap.txt` marks all three
`REACHED-SOLVER` on a **3-file** sample, and that file carries a
`PARTLY REFUTED` banner because four of its other rows were measured wrong. So
the label was worth re-testing rather than inheriting.

It holds. Nothing here is structurally blocked: the solver parses, dispatches
and decides in every division, and on `QF_BVFP` it decides 199 of 200 and beats
cvc5. The label understated `QF_BVFP` rather than overstating it.

The blockmap's own rows for these three divisions can now be replaced with
n=200 measurements. **Its other untested rows remain 3-file samples** and this
lane says nothing about them.

## Soundness: 0 disagreements, and the zero is not vacuous

Every verdict **we** produce, against three independent checks:

| division | decided | vs `:status` | vs z3 4.13.3 | vs cvc5 1.3.4 | disagreements |
|---|---:|---:|---:|---:|---:|
| QF_ABVFP | 179 | 178 of 179 | 179 of 179 | 178 of 179 | **0** |
| QF_BVFP  | 199 | 199 of 199 | 199 of 199 | 196 of 199 | **0** |
| QF_UFBV  |  89 |  89 of 89  |  89 of 89  |  87 of 89  | **0** |

The middle columns are the ones that make the zero mean something: a
zero-disagreement figure over a division that decides nothing, or whose
comparisons are mostly `unknown` on both sides, is vacuous. None of these are —
every division is comparable on ≥ 97 % of what it decides, against all three
checks. **Reference-vs-reference conflicts: 0** in every division too, so the
ground truth the checks rest on is not itself in dispute.

`summarize.py` computes this, `controls/` proves it can fail, and
`controls/mutants.py` breaks each subject and requires the naming guard to die —
**nine mutants, nine kills**, including two that revert ADR-1941 and one that
publishes only one of its two readings. The fixture also carries a row where every solver
agrees, which must produce **nothing**: a checker that flags everything has a
zero that means as little as one that flags nothing.

## Protocol

Matches `bench-results/dt-divisions-headtohead-20260912` and
`bench-results/session-20260911-smtlib/head-to-head`.

- **200 files per division**, from `bench-results/parity-lists/`, committed at
  **`04e0df4ac` BEFORE anything was measured**. That commit is what makes these
  rows non-cherry-picked.
- **24 s wall, 8 GiB address space**, three solvers **interleaved per file**
  (all three finish file N before any starts N+1) on one pinned physical core of
  one idle box, with the solver that goes first **rotating** per file. Units
  differ and are set accordingly: `z3 -T:24` SECONDS, `cvc5 --tlimit=24000`
  MILLISECONDS.
- **Wrapper timeout is 24 + 16 s.** A previous census used +8 under load, killed
  17 processes and produced rows that read as "no reason". Every run records its
  own outcome in a `*_k` column. **No row in any of these three boards is
  `wrapper-killed`** — on any solver.
- **Live probe before any measurement**: each of the three solvers had to
  *decide* a file first. z3 was absent on a host once and 800 files scored a
  silent 0/200 that read exactly like a result.
- One division per box, two modulo-interleaved shards per box on distinct
  physical cores (`0,8` and `2,10`; a Ryzen 7 7840HS is 8 cores with SMT
  siblings at +8). The merged TSV is re-ordered back into the pinned list's
  order, so the artifact does not encode the shard split, and
  `merge-division.py` **aborts** on an incomplete shard set rather than writing
  a smaller denominator.
- Runner `shard-run.sh`, launcher `launch.sh`. Solvers: axeyum built from this
  branch (see below), z3 4.13.3, cvc5 1.3.4. Boxes s5 / s6 / s7, Ryzen 7 7840HS,
  26 GB.

### The row key is the PATH, not the basename

These KLEE divisions reuse basenames across directories: the 200 `QF_ABVFP`
files carry 198 distinct basenames and the 200 `QF_BVFP` files carry 196. The DT
lane's runner keys rows by `basename`, which here would silently merge two
different benchmarks when the TSV is joined back to a list. This runner keys by
the path relative to the corpus root.

### Two shards per box, not three

The 8 GiB cap is per **run**, and these boxes have 26 GB. Three concurrent
shards can reach 24 GiB.

### The sampling: full-span spacing, not `N//200`

`find | sort`, then 200 indices evenly spaced over `0 .. N-1` inclusive
(`mklist.py`). Not a path-sorted prefix — a prefix of these lists is a sample of
one benchmark family, a mistake that produced four wrong censuses in one
session. And **not the plain `N//200` integer stride** either: that stops at
index `199 * (N//200)` and never reaches the tail. On `QF_UFBV` it stops at 1393
of 1510 and drops the last three families — Certora, btfnt, calc2, 107 files,
7 % of the division — entirely. We score **0 of the 15 sampled files** in those
three families, so the obvious stride would have hidden a real hole.

On the two FP divisions the sample is 198/1/1 across families, and that is the
population, not a defect: `QF_ABVFP` is 18,033 of 18,129 one family
(20170428-Liew-KLEE, 99.5 %) and `QF_BVFP` is 17,156 of 17,249 the same family.
At 200 draws the expected count from the entire remaining tail is 1.06.
**These two divisions are, to two significant figures, one benchmark family**
(KLEE symbolic-execution queries from `20170428-Liew-KLEE`) and their rows
should be read that way — they are not a broad statement about floating point.

### The reference frame, measured rather than asserted

`loadframe.tsv` samples each box's 1-minute load and its count of foreign pinned
jobs every 30 s for the life of the run. Per host, **33 of 36 samples showed
zero foreign pinned jobs**; load1 ran 0.03–3.75 (s5), 0.00–2.35 (s6),
1.06–4.24 (s7), most of which is this lane's own two shards.

The boxes were not hermetically idle, and three samples per host caught 2–4
foreign pins. What the protocol actually rests on is the **per-file
interleaving**: all three solvers run file N back to back on the same pinned
core, so ambient drift cancels in the *difference*. The absolute counts can be
depressed by contention; the axeyum-vs-z3-vs-cvc5 comparison within a file is
not. Quote the comparison, and treat a 1–2 file absolute difference as noise.

### The binary

Built from scratch in an empty target dir on this branch
(`cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli`,
3 m 57 s) and verified newer than every `crates/**/*.rs` before use — `find
crates -name '*.rs' -newer <binary>` returned nothing. Cargo decides freshness by
mtime, and a stale prebuilt binary reported a false ABSENT three separate times
in this repository today.

**No solver code changed in this lane.** It is a measurement lane: a board row
and a behaviour change in one branch cannot be told apart afterwards.

## Reading the rows

### QF_BVFP — 199 / 200, and we beat cvc5

The one undecided file
(`imperial_svcomp_float-benchs_svcomp_filter1.x86_64/query.10.smt2`) is a clean
24.33 s budget exhaustion, not a refusal: `attempts=13` on a 13-rung ladder,
`bound_by=qf-bv` with `bound_ms=23795` of `total_ms=24121` — **98.6 % of the
budget inside a real bit-blast solve**. Both references decide it in ~2.5 s.

We decide 3 files cvc5 does not and 1 fewer than z3. Median axeyum time 0.11 s;
total wall 72 s against z3's 37 s and cvc5's 28 s over the same 200.

### QF_ABVFP — 179 / 200, and the census refuses to rank itself

z3 decides 18 we do not, cvc5 20; we decide 1 cvc5 does not and 0 that z3 does
not. **20 of the 21 undecided files burn the full 25 s**, so this is a
clock-bound row on its face — but the census says that reading is wrong. See
*The blocker census* below and `findings/README.md`.

### QF_UFBV — 89 / 200, and the failures are refusals

This is the row with a real gap: **z3 decides 85 files we do not, and we decide
0 that z3 does not.**

**102 of our 111 undecided files return in under 20 s** of a 24 s budget, most
under 1 s. We are not running out of clock here; we decline. That is a much more
actionable shape than "slow", and it is why the full census matters.

    family                             n   axeyum   z3   cvc5
    2018-Goel-hwbench                158       89  158    156
    20210312-Bouvier                  26        0   11      5
    20230314-Jaroslav-Bendik-Certora  10        0    1      1
    calc2                              4        0    4      0
    2019-Wolf-fmbench                  1        0    0      0
    btfnt                              1        0    0      0

Two stories, not one: 56 % of the dominant hardware-model-checking family, and
**0 of the 42 files outside it**.

**cvc5's 162 is a depressed floor, not its capability.** 38 of its 200 runs
ended `rc134` — the 8 GiB address-space cap this protocol sets — and all 38 are
scored undecided. That cap is applied evenly to all three solvers (z3 hit it 0
times, we hit it 0 times), but the number is not "cvc5 decides 162 of 200
QF_UFBV benchmarks". Name the reference when quoting this gap: **z3 is the
leader in this division**, by 12 files over cvc5 even before the cap.

## The blocker census

Every file we leave `unknown` while a reference decides it — the **whole**
winnable set, not a sample — re-run with `--trace` at the same 24 s / 8 GiB /
pinned-core envelope. Runner `census-run.sh`, ranking `census-summarize.py`.

**[ADR-1936](../../docs/research/09-decisions/adr-1936-a-gap-census-reports-attempts-and-marks-an-unfinished-dispatch-unclassified.md)
governs this table**, and taking it seriously produced
**[ADR-1941](../../docs/research/09-decisions/adr-1941-attempts-alone-cannot-classify-a-census-row-the-open-segment-is-the-discriminator.md)**,
which this lane wrote because the rule as stated was not checkable.

ADR-1936 says to mark `UNCLASSIFIED` any row whose dispatch did not reach the
end of the ladder, and to "record the ladder length the division's dispatch
reaches when it completes". A census cannot observe that length — the best proxy
is the maximum `attempts=` it saw. Using that proxy gave:

| division | rows | max `attempts=` | UNCLASSIFIED by the proxy |
|---|---:|---:|---:|
| QF_ABVFP | 21 | 14 | 20 |
| QF_UFBV  | 87 | 18 | 77 |

The first number is right and the second is wrong, and **a field already being
printed separates them**:

- On `QF_ABVFP` the 20 rows carry `; route-open ms=24982 after=dl-online
  attributed_ms=17` — 24.98 s of a 25 s budget in a segment no route attempt
  covers. The dispatch did not finish.
- On `QF_UFBV`, **87 of 87 rows have no `route-open` line at all**, with
  `bound_ms` ≈ `total_ms` (median 770 ms of 829 ms at `attempts=14`). The budget
  is fully attributed. Those dispatches ran to the end of a **shorter** ladder —
  ladder length is query-dependent, and rows at `attempts=14` and at
  `attempts=18` end on the *same* give-up reason.

So ADR-1941 makes the **open segment** the discriminator and keeps `attempts=`
as a reported column. The strict reading is published beside the ranked one on
every division (the `[ADR-1941]` line in `census-summarize.py`'s output), because
the proxy's answer is evidence, not an error to hide.

Getting this wrong in the conservative direction is not free: the proxy would
have rendered `QF_UFBV` as "77 unrankable" and suppressed the single largest
finding on this board.

### QF_ABVFP — 21 winnable, and 19 of them are UNCLASSIFIED

    CLASSIFIED 1    UNCLASSIFIED 19    no-route 0    internal-error 1
    wrapper-killed 0

    16  attempts=3   open_after=dl-online            open_ms 24.6-25.0 s
     3  attempts=5   open_after=aufbv-online-cdclt   open_ms 24.8-25.0 s
     1  attempts=6   terminal internal error (reported, never ranked)
     1  attempts=14  — the only rankable row (a genuine budget exhaustion)

Nineteen rows put **24.6–25.0 s of a 25 s budget into the open segment**. Their
give-up reason is `Watchdog`, which ADR-1936 is explicit is a fact about the
harness, not a cause.

So this division's blocker census is 19/21 unrankable, and **that is the
finding**, not a failure of the census: it names a rung to fix rather than a
capability to build. A census that is almost entirely `UNCLASSIFIED` is a
complete and useful result.

What the rung is doing is in `findings/README.md`: `abv-online-cdclt` is entered
and, at a **600 s** budget — 25× the board's — completes **zero CEGAR rounds**
on a query with `row_sites=4` that both references decide in 0.11 s. A 25×
budget bought zero rounds, so it is not converging slowly; it is not reaching
its first round.

### QF_BVFP — 1 winnable, 1 classified

`Timeout: combined-theory timeout after scalar backend`, `attempts=13`,
98.6 % of the budget inside the solve. **With n = 1 the ADR-1936 partition is
vacuous here** — "the ladder length is the max attempts observed" is
self-fulfilling on a single row — so the `bound_ms`/`total_ms` ratio is what
carries the claim that this dispatch did not stop early, not `attempts=`.

### QF_UFBV — 87 winnable, and 84 of them are two constants

    CLASSIFIED 86    UNCLASSIFIED 0    no-route 1    wrapper-killed 0

    | 52 | `ResourceLimit`: online UFBV has N semantic atoms, exceeding the cap of N |
    |    | measured N: min 1065, median 1601, max 5458 — **1.04x to 5.33x** over |
    | 31 | `NodeBudget`: online UFBV input has N DAG nodes, exceeding the cap of N |
    |    | measured N: min 16437, median 26734, max 229961 — **1.00x to 14.04x** over |
    |  2 | `Timeout`: online UFBV canonical CdclT search exhausted its budget |
    |  1 | `ResourceLimit`: online UFBV **dynamic** theory atoms exceed the cap of N |
    |  1 | no route trail at all (its own row, not an absence) |

**84 of 87 winnable files — 97 % — are stopped by two hardcoded constants**,
both in `crates/axeyum-solver/src/ufbv_online.rs`:

```rust
const MAX_INPUT_DAG_NODES: u64 = 16_384;   // line 89 — 31 files
const MAX_THEORY_ATOMS: usize = 1_024;     // line 93 — 52 + 1 files
```

This is what the census exists to produce, and it is the opposite of QF_ABVFP's
answer. These rows ran to the end of their dispatch, their budget is fully
attributed, and their reason is a number in a source file — not a fragment we
cannot decide and not a search that ran out of clock. **Only 2 of 87 are actual
budget exhaustion.**

The magnitudes are reported beside the counts because they are what decides
whether raising a cap helps, and they say two different things:

- **The atom cap is close.** 29 of the 52 are under 1.6x it; a cap of 2,048
  would admit 37 of 52 and 4,096 would admit 50 of 52.
- **The node cap is not uniformly close.** 25 of 31 are under 4x (65,536), but
  the tail reaches 14.04x — 229,961 nodes.

Neither number is a recommendation. A cap exists to bound something, and this
lane measured what it turns away, not what happens if it stops. **Raising a cap
can convert a fast `unknown` into a slow `unknown` and buy nothing** — which is
exactly what the 2 rows that *did* exhaust the budget are a warning about. The
next lane's job is the A/B, and it now has a sized target and a pinned
population to run it over (`winnable/QF_UFBV.txt`).

## What this says about where to spend effort

Three different answers, and the point of the census is that they are different:

1. **QF_BVFP needs nothing.** 199/200, ahead of cvc5. The FP core is strong and
   this confirms it at n=200 rather than at QF_FP's n=200 alone.
2. **QF_ABVFP needs a bug fixed, not a capability built.** 16 of 21 winnable
   files stop in one place, and a 600 s probe shows that place making no
   progress at all on a 4-array-site query. Fixing it is the cheapest coverage
   on this board. It is **not** an FP weakness — the combination is what costs,
   exactly as the brief predicted — and it is **not** a slow search.
3. **QF_UFBV is two constants, not a missing decision procedure.** This is the
   answer the census changed. 85 files behind z3 and 102 of 111 failures are
   fast declines — and **97 % of the winnable set is stopped by
   `MAX_THEORY_ATOMS = 1_024` (53 files) and `MAX_INPUT_DAG_NODES = 16_384`
   (31 files)**, two literals on adjacent lines of one file. Only 2 of 87 are
   real budget exhaustion.

   That is *not* the same as "raise them and gain 84 files". A cap converts a
   slow `unknown` into a fast one; removing it can just move where the time
   goes. But it does mean the next step is a bounded A/B over a pinned
   population, not a design for a decision procedure we do not have.

Nothing here is a decision to build. The measured claim is: **one cheap bug
(QF_ABVFP, 16 of 21 files in one non-progressing route), two sized constants to
A/B (QF_UFBV, 84 of 87 files), and one division already done (QF_BVFP,
199/200).** No division on this board points at a decision procedure we lack —
which is itself the finding, since that was the plausible prior for three
untested divisions.

## Files

| path | what |
|---|---|
| `QF_*.tsv` | the board rows, in pinned-list order |
| `census/QF_*.tsv` | the blocker census over the whole winnable set |
| `winnable/QF_*.txt` | the winnable sets themselves, so the census denominator is re-derivable |
| `findings/` | the two defects, with repros, and the 600 s probe log |
| `controls/` | the checkers' own fixtures and mutants |
| `mklist.py` `shard-run.sh` `launch.sh` `census-run.sh` | the runners |
| `merge-division.py` `summarize.py` `census-summarize.py` | the derivations — every number above is re-derivable, not transcribed |
