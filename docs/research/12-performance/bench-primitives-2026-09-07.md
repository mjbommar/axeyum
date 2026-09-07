# bench-primitives — a running diary, 2026-09-07

Status: measured
Lane: `bench-primitives` (`docs/plan/status/1740-bench-primitives.md`)

## What this is

A diary, not a report. It records what was measured, what was expected, what
was found, and — the part worth the file — **where the expectation was wrong**.
A diary of confirmations is worth much less than one that records a surprise,
so the surprises get their own headings and are not smoothed away afterwards.
Five are recorded below, three of them about this lane's own reasoning rather
than about the code.

Subject: the three shared primitives every division above them pays for.

| crate | what it owns | benches before this lane |
|---|---|---|
| `axeyum-ir` | term arena + interning, `Value`, ground evaluator, LSB-first bit conversion | 1 (`arena_intern`) |
| `axeyum-bv` | term-to-AIG bit lowering, `lower_terms` / `IncrementalLowering` | **0** |
| `axeyum-smtlib` | SMT-LIB parser, sharing-preserving writer | **0** |

This lane follows
[`microbenchmarks-2026-09-05.md`](../08-planning/microbenchmarks-2026-09-05.md),
which added the first seven benches in the workspace. It does not repeat them.

## The rule this lane is held to

From the brief, and the reason for every "proxy for" paragraph in every bench
added here:

> A microbenchmark that does not predict the real workload is worse than none.
> Measured on this repo 2026-09-06: `cdclt_solve_php_6_7`, a 42-variable
> pigeonhole, says engine A is 3.4% faster than engine B — while on a
> 330,000-variable real skeleton the same swap decides 4 MORE files at 12.9%
> better PAR-2. The benchmark and the corpus disagreed in **direction**.

Finding 2 below is this lane's own instance of that hazard, and it points the
same way: a microbenchmark and an in-tree figure about a real file disagree by
a factor of about thirty.

## Method

- Host: `s4` (the shared dev box, hybrid CPU, 16 logical CPUs). Sibling lanes
  hold `s5`–`s7`; `scripts/cargo-serialized.sh` takes a **host-wide** flock, so
  a build's own wall clock is not a measurement.
- Every timing run pinned to the performance cores with `taskset -c 0-7`,
  matching
  [`frontier-ratchet-reference-frame.md`](../08-planning/frontier-ratchet-reference-frame.md).
  Unpinned, this host is measured 1.84x slower on the E-cores, which has
  already produced one phantom REGRESSION elsewhere.
- `/proc/loadavg` read **before and after** every timing run; the 1-minute
  figures across this lane's runs were **0.88 – 2.46**, i.e. a comparatively
  quiet box. An orphan sweep
  (`ps -eo pid,ppid,etimes,%cpu,cmd | awk '$2==1 && $4>10'`) before the first
  run returned nothing.
- `perf` was not used. Every attribution below is by **composition** — running
  a primitive and its caller separately and checking whether the caller's cost
  is accounted for by the primitive's cost times the call count — or by a
  falsifiable shape prediction made before the run. Both are recorded so a
  reader can rerun them.

---

# The numbers

All medians, criterion, release, pinned. Where two runs exist both are given;
their spread is a result in itself (see "Variance" below).

## `axeyum-smtlib` — ingest

| file | bytes | `read_all` | `parse_script` | reader's share | parse throughput |
|---|---:|---:|---:|---:|---:|
| `crafted__bit-counting` | 2,762 | 20.8 µs | 71.6 µs | 29% | 38.6 MB/s |
| `preprocess__array__nondestr_subst7` | 50,762 | 373 µs | 880 µs | 42% | 57.7 MB/s |
| `solver__array__random3.btor` | 1,084,746 | 16.5 ms | 27.3 ms | 60% | 39.7 MB/s |
| `rewrite__array__rw17.btor` | 10,493,712 | 154 ms | 346 ms | 45% | 30.4 MB/s |

## `axeyum-bv` — lowering and model replay

| bench | median |
|---|---:|
| `lower_terms_bvmul/w8` | 7.39 µs |
| `lower_terms_bvmul/w16` | 29.6 µs |
| `lower_terms_bvmul/w32` | 199.7 µs |
| `lower_terms_bvmul/w64` | 895 µs |
| `lower_terms_corpus_bit_counting` | 577 µs |
| `lowering_incremental_vs_oneshot/oneshot` | 579 µs |
| `lowering_incremental_vs_oneshot/incremental` | 574 µs |
| `model_replay_input_values/w16` | 386 ns |
| `model_replay_input_values/w32` | 995 ns |
| `model_replay_input_values/w64` | 2.94 µs |
| `model_replay_input_values/w128` | 9.85 µs |
| `model_replay_input_values/w512` | 181 µs |
| `model_replay_input_values/w1024` | 631 µs |
| `model_replay_input_values/corpus_bit_counting_391_symbol_bits` | 11.92 µs |

## `axeyum-ir` — evaluator, bit conversion, interning

| bench | median |
|---|---:|
| `eval_shared_dag` | 4.31 µs (4.83 µs in run 1) |
| `eval_replay_16_assignments/fresh_map_per_call` | 69.6 µs (68.9) |
| `eval_replay_16_assignments/reused_map` | 59.5 µs (57.5) |
| `value_to_lsb_bits/w8 · w32 · w64 · w128` | 14.1 · 24.9 · 45.9 · 74.5 ns |
| `lsb_bits_to_value/w8 · w32 · w64 · w128` | 12.7 · 29.8 · 55.5 · 106.8 ns |
| `arena_intern_20000_bv_const` | 1.756 ms |

---

# Finding 1 — `BitLowering::input_values` is quadratic in symbol width, and 97% of it is redundant

**Named function:** `BitLowering::input_values`, `crates/axeyum-bv/src/lib.rs`.
**Data-structure choice:** `symbol_inputs: Vec<SymbolBitInput>` holds one entry
per symbol **bit**, and the loop over it calls
`value_to_lsb_bits(value)` — which allocates a `Vec<bool>` of the symbol's
**full width** — then reads exactly one bit out of it and drops the vector.

This was written down as a falsifiable prediction in the bench's own doc
comment *before* running it: doubling the width should roughly quadruple the
time. It does.

| width | median | ratio to previous |
|---:|---:|---:|
| 16 | 386 ns | — |
| 32 | 995 ns | 2.58 |
| 64 | 2.94 µs | 2.96 |
| 128 | 9.85 µs | 3.34 |
| 512 | 181 µs | 18.4 (width ×4) |
| 1024 | 631 µs | 3.48 |

Fitting `t = a·w + b·w²` to the 16/128 pair gives `a = 16.4 ns/bit`,
`b = 0.483 ns/bit²`. That model predicts **3,028 ns** at width 64 against a
measured **2,944 ns**, and **1,020 ns** at width 32 against **995 ns** — within
3% at both points it was not fitted on. The quadratic term is 65% of the cost
at width 64 and 79% at width 128.

**Two things make this an attribution rather than a shape.**

*The cost is the primitive, called too often.* `value_to_lsb_bits` at width 128
is 74.5 ns (measured independently in `axeyum-ir`'s `value_bits`). Times 128
calls, that is 9.54 µs — against a measured `input_values` of 9.85 µs. **97% of
`input_values` is accounted for by the redundant per-bit conversion**, so
nothing else in that loop needs looking at.

*It is the caller's loop, not one conversion routine.* Crossing width 128 moves
a bit-vector value from `Value::Bv` (`u128`-backed, `bv_value_to_lsb_bits`) to
`Value::WideBv` (`WideUint::to_lsb_bits`) — a different function on a different
representation. The quadratic **survives the crossing** unchanged (512 → 1024
is a clean 3.48x for a 2x width). That rules out "one conversion routine is
slow" and leaves the loop.

**The fix is small:** hoist the conversion out of the per-bit loop — one
`value_to_lsb_bits` per *symbol*, reused across that symbol's bits. In practice
`symbol_inputs` is already built in symbol order (bits are appended as a symbol
is first lowered), so even a one-entry "last symbol seen" cache would collect
almost all of it; a `FastMap<SymbolId, Vec<bool>>` collects all of it without
depending on that ordering.

**Why this is not being sold as a headline — the counterweight is in the same
bench group.** On the real committed benchmark this file otherwise uses,
`input_values` costs **11.92 µs over 391 symbol bits**, against **577 µs** to
lower that same file. That is **2.1% of lowering alone**, before any SAT
search. The committed `QF_BV` corpus is 32-bit registers, and at width 32 the
quadratic term is only about half of a sub-microsecond cost.

So the honest statement is two-sided and both halves matter:

- the shape is real, confirmed, fitted, and cheap to remove; and
- on the corpus that exists it is a rounding error, and it becomes material
  only at widths the committed corpus does not contain — **631 µs per model
  replay for a single 1024-bit symbol**, a width this crate's own tests
  (`incremental_lowering_interrupts_wide_division`) use and which
  `MAX_BV_WIDTH = 65,536` admits.

One cross-check that the synthetic fixture is not lying: the corpus case runs
at 30.5 ns per symbol bit (11.92 µs / 391), and the synthetic single-symbol
width-32 case runs at 31.1 ns per bit (995 ns / 32). The proxy predicts the
real file to within 2% **at the width the real file uses**. That is the
strongest form of proxy validation available here, and it is exactly why the
corpus case sits in the same group as the sweep rather than in a footnote.

# Finding 2 — ingest is linear in bytes, so the in-tree "58 MB takes ~54 s" figure is about thirty times slower than these numbers predict

This is the lane's microbenchmark-versus-real-workload disagreement, and it
is large.

`SmtError::DeadlineExceeded`'s own doc comment — the justification for putting
a deadline in the parser at all — records that "reading a 58 MB benchmark takes
~54 s", i.e. about **1.1 MB/s**, and that a 24 s budget produced real runs of
39.9 s, 49.4 s and 66 s.

Measured here over four committed files spanning 2.7 KB to 10.5 MB — nearly
four orders of magnitude — `parse_script` throughput is **30.4 to 57.7 MB/s**
with no trend toward the low end at the top:

| bytes | parse MB/s |
|---:|---:|
| 2,762 | 38.6 |
| 50,762 | 57.7 |
| 1,084,746 | 39.7 |
| 10,493,712 | 30.4 |

Ingest on this corpus is, to a good approximation, **linear in bytes**. A
linear extrapolation of the 10.5 MB point puts 58 MB at about **1.9 s**, not
54 s — a factor of roughly **30**.

Both numbers can be right at once; they are not measuring the same thing. The
possibilities worth naming, none of which this lane has settled:

- the 58 MB file's **shape** is the cost, not its size — deep nesting, a huge
  symbol table, or sharing structure that the four committed files do not
  have (all four here are `QF_ABV` bitwuzla or cvc5 regressions);
- the figure predates work that changed ingest, and is now stale; or
- "reading" in that sentence covers more than `parse_script` — a solve
  pipeline stage, not the parser.

**What must not happen is what the figure invites.** Quoted as a rate it says
"the parser runs at ~1 MB/s", and anyone sizing an ingest deadline, a resource
budget, or a shard from that rate will size it about thirty times too
pessimistically. A lane reading it would reasonably conclude the parser is the
bottleneck on large inputs; on everything committed, it is not.

The `array_rw17_10m` case exists in `smtlib_parse` specifically so this
comparison can be rerun rather than re-argued. Settling *which* of the three
explanations holds needs the actual 58 MB file, which is not in the tree — so
this is recorded as an open discrepancy, not a correction.

# Finding 3 — the s-expression reader is 29–60% of ingest, and its share tracks file shape rather than file size

`parse_script` is two passes: `read_all` builds an `SExpr` tree (lex,
paren-match, **one owned `String` per atom**), and the typed parser then walks
that tree doing sort checks and `TermArena` construction. Benching both over
the same files makes the pair a decomposition rather than two numbers.

| file | reader's share of full ingest |
|---|---:|
| 2.7 K | 29% |
| 50 K | 42% |
| 1.1 M | 60% |
| 10.5 M | 45% |

The consequence for anyone planning ingest work: **a faster typed parser is
capped at roughly half of ingest, and on the megabyte file at 40%.** The
reader is not a thin front end that can be ignored while the "real" pass gets
optimized.

The structural observation, which the share numbers support but do not by
themselves prove: `read_all` **materializes the entire `SExpr` tree, with an
owned `String` per atom, before the typed pass looks at anything**. On the
10.5 MB file that is a full second tree in memory whose only consumer is the
next pass. The shape of a fix is therefore fusion — stream tokens into the
typed builder — rather than a faster tokenizer. That is a design change with a
deadline-and-error-reporting story to work out, so it is named here as a
direction, not proposed.

# Finding 4 — `eval` pays 15% for a `FastMap` it allocates and drops on every call

`eval` builds a fresh `FastMap<TermId, Value>` per call and drops it on
return; `eval_with_memo` takes the caller's map. Over 16 replays of one DAG,
allocating once and clearing between assignments costs **59.5 µs against
69.6 µs** — a **14.5%** saving (16.6% in the first run).

This is a real but bounded number and it comes with a correctness caveat that
is the reason the bench clears the map: `eval_with_memo`'s doc is explicit
that memo values are valid only for the assignment that produced them and
"the caller owns invalidation". So the 15% is *allocation reuse only* — it is
not the (larger) saving a caller could get from true incremental invalidation, and
it is not available by simply keeping a map around.

Where it would be collected: the model-replay loop the hard rules mandate on
every `sat`, and the differential fuzzes, which call `eval` once per
iteration. The fixture is **synthetic** and its doc says so — `axeyum-ir` sits
below `axeyum-smtlib`, so there is no committed benchmark it can read, and
"shaped like a `QF_BV` skeleton" is the strongest claim available for it.

---

# Where this lane was wrong

## W1 — the reader's share, predicted before the run

Recorded in this file before the first run: *"I expect `read_all` to be the
minority of `parse_script` — under 40% — on the large file, because the typed
pass does interning and sort checking while the reader only allocates."*

It was **60%** on the 1.1 MB file and **45%** on the 10.5 MB file. Wrong at
both. The reasoning was wrong in a specific way worth keeping: I priced the
typed pass's *work* and forgot the reader's *allocations*. One `String` per
atom over a megabyte of source is a great many allocations, and allocation is
not cheaper than sort checking.

## W2 — a trend read off three points, broken by the fourth

After the first run (three files) I wrote that the reader's share **grows with
file size** — 31% → 37% → 50% — and started reasoning about why. The 10.5 MB
point came back at **45%**, below the 1.1 MB point's 60%.

There is no size trend. The share tracks the file's **shape** — its ratio of
atoms to term structure — and the four files are four different shapes. Three
monotone points are not a trend, and I treated them as one for about twenty
minutes before the fourth arrived. Any claim about how ingest scales that this
lane might have published off those three points would have been false.

## W3 — I nearly reported a settled negative as a new finding

Reading `axeyum-bv`, the `LoweringBuilder`'s memo is
`BTreeMap<TermId, Vec<AigLit>>` — an ordered tree keyed on a dense
insertion-order `u32` newtype, in a struct that already carries a dense
`Vec<Option<TermBitRange>>` beside it. It is a textbook data-structure finding
and I began drafting it as one.

**ADR-0300 already ran that exact experiment.** It preregistered the dense
`Vec<Option<Vec<AigLit>>>` candidate, froze a baseline, gated on structural
identity, ran a 12-process order-balanced timing schedule, and **rejected** it
— on run-total variance (baseline bit-blast CV `3.0023%` against a `3%`
ceiling, candidate `6.87%`), despite a favourable paired bit-blast geometric
mean of `0.922`. It also lists "select on comparison counts or
microbenchmarks" among its rejected alternatives, which is precisely what I
was about to do.

The general lesson, and it is the expensive one: **an obvious data-structure
finding in a mature codebase is more likely to be a settled negative than a
discovery.** The `BitLoweringMemoRepresentation` enum sitting in the public API
with a `DenseV1` variant that production never constructs was the visible tell,
and I read past it. `bv_lowering`'s module doc now says the crate does not
compare memo representations and why, so the next lane hits the ADR before the
draft.

Worth carrying separately: the rejection was on **variance**, and the baseline
failed its own ceiling by 0.02 points on a shared box. That is the same
run-to-run instability recorded under "Variance" below. A microbenchmark
median hides it completely.

## W4 — a 4x speedup I nearly attributed to a hasher

`arena_intern_20000_bv_const` measured **1.756 ms** here. The
[2026-09-05 micro-benchmark note](../08-planning/microbenchmarks-2026-09-05.md)
records the same bench at **7.024 ms**, on the crate's then-`SipHash` intern
table; `axeyum-ir` has since moved to `rustc-hash` via `fast_map.rs`. The
ratio is 4.0x and the temptation to publish it as the hasher's win was
immediate.

It is not comparable. That note records its own load average as **17.9–36.7**;
this lane's runs were at **0.88–2.46**, an order of magnitude apart on a
16-core box. The
[hasher measurement note](../11-design-review/2026-09-05-intern-table-hasher-measured.md)
that actually studied the swap reached "**~2.0% by pooled median, ~7.4% by
pooled min** — a weak, directionally-consistent signal, not a validated
speedup", under exactly those loaded conditions, and asked for a criterion
bench isolating hashing from parsing.

That bench now exists and this is its first quiet-host number, so **1.756 ms is
recorded as a fresh baseline and no speedup is claimed.** A controlled answer
needs both arms run today, interleaved; this lane did not run them and reports
that as did-not-run, not as a result.

## W5 — I expected incremental lowering to cost something

`IncrementalLowering::lower_with_deadline` moves five accumulator fields in and
out of a one-shot `LoweringBuilder` via `core::mem::take` on **every call**, and
its memo never sees the whole batch at once. I expected a measurable per-call
tax against `lower_terms` over the same roots.

Measured: **574 µs incremental against 579 µs one-shot**, over the same arena
and the same roots — indistinguishable, and if anything the incremental arm is
marginally ahead. The `mem::take` shuffle is a handful of pointer moves against
a lowering that is thousands of gates; it does not register. A design that
*looks* expensive per call is not expensive when the per-call work dwarfs it,
and I would have written the opposite into a note if I had not benched it.

---

# Variance, and what it means for anything measured here

Two runs of the same benches on the same commit, minutes apart, at reported
1-minute loads of 1.42 and 0.90:

| bench | run 1 | run 2 | spread |
|---|---:|---:|---:|
| `smtlib_read_all/array_random3_1m` | 13.45 ms | 16.5 ms | +23% |
| `smtlib_read_all/array_subst7_50k` | 309 µs | 373 µs | +21% |
| `eval_shared_dag` | 4.83 µs | 4.31 µs | −11% |
| `eval_replay_16/reused_map` | 57.5 µs | 59.5 µs | +3.5% |
| `model_replay_input_values/w64` | 3.03 µs | 2.94 µs | −3% |

**A single criterion median from this host carries roughly ±20% of run-to-run
uncertainty on the allocation-heavy benches**, even pinned, even at load below
1.5. That is not criterion's confidence interval, which was under 1% within
each run — it is between-run drift the interval cannot see.

Three consequences for anyone reading these numbers:

1. **Nothing here should be quoted to two significant figures.** The findings
   above are ratios and shapes (a quadratic, a 30x gap, a share between 29%
   and 60%) precisely because those survive ±20%; a 5% improvement claim would
   not.
2. **ADR-0300's variance rejection was not bad luck.** Its baseline missed a 3%
   CV ceiling by 0.02 points on this box. The spread above is the same
   phenomenon, and it means any future accept/reject gate on these primitives
   needs interleaved paired runs, not two blocks minutes apart.
3. **The allocation-heavy benches are the noisy ones** — `read_all` (a `String`
   per atom) and `eval` (a map per call) move ±20%, while the arithmetic-bound
   `input_values` sweep moves ±3%. That is itself a hint about where the
   allocator is in the picture, and it is consistent with Finding 3.

---

# Registered benches

| crate | target | groups | proxy status |
|---|---|---|---|
| `axeyum-smtlib` | `smtlib_parse` | `smtlib_read_all`, `smtlib_parse_script` × 4 committed files | **not a proxy** — real committed files; but see Finding 2 and the size-distribution caveat |
| `axeyum-bv` | `bv_lowering` | `lower_terms_bvmul` (w8–w64) | **proxy, narrow, unvalidated** — a quadratic circuit; ADR-0300's family split says arithmetic is a minority shape |
| `axeyum-bv` | `bv_lowering` | `lower_terms_corpus_bit_counting` | **not a proxy** — a committed `QF_BV` file's real assertions |
| `axeyum-bv` | `bv_lowering` | `lowering_incremental_vs_oneshot` | proxy for the warm `IncrementalBvSolver` push path |
| `axeyum-bv` | `bv_lowering` | `model_replay_input_values` (w16–w1024 **+ the corpus case**) | shape sweep **validated against the corpus at width 32** (31.1 vs 30.5 ns/bit) |
| `axeyum-ir` | `term_eval` | `eval_shared_dag`, `eval_replay_16_assignments` | **proxy, synthetic, unvalidated** — stated as such in the module doc |
| `axeyum-ir` | `value_bits` | `value_to_lsb_bits`, `lsb_bits_to_value` (w8–w128) | partial proxy for model lifting; the caller-side interaction is measured in `axeyum-bv` |

Run them with `taskset -c 0-7 cargo bench -p <crate> --bench <target>`. Each
target completes in well under five minutes; the largest,
`smtlib_parse`, is about 90 s.

# What this lane did not measure

Reported as **did not run**, not as absent:

- **A controlled hasher A/B.** See W4. Needs both arms built and interleaved on
  one quiet host; not done.
- **The 58 MB file behind Finding 2.** It is not in the tree, so which of the
  three explanations holds is unsettled.
- **`write_script`.** The sharing-preserving writer got no bench. It was in
  scope and was displaced by the `input_values` investigation; the shape to
  measure is round-trip cost against DAG size, since the writer's whole
  contract is that output is linear in the DAG rather than the unfolded tree,
  and nothing currently checks the cost of keeping that promise.
- **What fraction of a whole solve model replay actually is.** Finding 1's
  counterweight compares `input_values` against *lowering* on one file, not
  against an end-to-end solve. The right instrument is `axeyum-bench`, not
  criterion.
- **The `demanded` / `range-demanded` lowering routes.** Only ordinary full
  lowering is benched.
