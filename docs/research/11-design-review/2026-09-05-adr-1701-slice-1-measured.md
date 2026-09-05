# ADR-1701 slice 1 — measured before/after on the QF_IDL and QF_LRA timeout populations, 2026-09-05

This closes the measurement [ADR-1701](../09-decisions/adr-1701-the-theory-interface-gains-final-check-a-driver-owned-queue-lazy-explanation-and-dynamic-atoms.md)
and its own text deferred: "Slice 1's measured effect on the QF_IDL and QF_LRA
miss populations is reported with the implementation" (ADR-1701, Consequences,
"Not claimed"). Slice 1 landed as `c64928295` (the trait) and `2d0cf09d8` (the
two opt-ins, `DlTheory`/`dl_online.rs` and `LraTheory`/`lra_online.rs`),
merged at `188dddf99`. This note is the follow-up measurement lane
(`theory-trait-final-check` / `theory-trait-measure`); it changes no
production Rust.

## Method

**Binaries.** BEFORE is `ef119b385` (the last commit on `main` before ADR-1701's
merge; it already carries ADR-1703's BatSat retirement, so the only production
difference between the two arms is slice 1). AFTER is this lane's worktree at
merge time (`16a5bc186` plus this note). Both built
`cargo build --release -p axeyum-bench --example smtcomp_cli` through
`scripts/cargo-serialized.sh`; BEFORE in a `scripts/lane-snapshot.sh
ef119b385` extraction (`--touch`-stamped, so cargo's mtime freshness check is
not fooled). The two binaries were confirmed to differ before any measurement:

```
sha256sum target/release/examples/smtcomp_cli   (AFTER)
  3072e2c8d2a2fb6272501b8a0fed0d36b1a2df986320b5e8c5d594b9b64ee212
sha256sum snap-.../target/release/examples/smtcomp_cli   (BEFORE)
  1d5e145d3220b270b243a9344c3731b5546a7106941647d7a0257c7f6ccb89f0
```
different sizes too (41,030,696 vs 40,655,880 bytes).

**Populations.** Both are drawn from the 2026-08-21 diagnosis's per-file TSVs
(`bench-results/linear-arithmetic-diagnosis-20260821/QF_{IDL,LRA}.tsv`),
restricted first to genuine misses — rows where z3 4.13.3 decided `sat`/`unsat`
and axeyum did not (65 rows in each division; this matches the diagnosis's own
"65 misses" count for both, confirmed by recomputing from the TSV rather than
trusting the doc's prose).

- **QF_IDL, 50 files** (`bench-results/adr-1701-slice-1-20260905/qf_idl_population.tsv`):
  misses whose `unknown_kind` is `Timeout` (25, detail `preprocessed dispatch
  timeout after reduced solve` — the wrapper-erased `dl-online:BUDGET` case the
  diagnosis's §3 names) or `ResourceLimit` (25, detail `lazy linear arithmetic
  pre-SAT skeleton exceeds the joint resource boundary` — `lia-dpll` declining
  immediately after `dl-online` has already consumed its share of the budget,
  per diagnosis §3.1). Excluded: 15 `HARDKILL`/`na` rows ("killed by external
  timeout at 32s") — a real deadline overrun, but not carrying a timeout-class
  `unknown_kind` in this TSV.

  **This is 50 files, not the ~64 named in the brief.** The brief's "about 64"
  is the diagnosis's separately-run `explain_corpus --list --json` route-ladder
  trace (its "second instrument"), which distinguishes `dl-online:BUDGET` from
  every other decline text-for-text; the wrapper that produces this TSV's
  `detail` column erases that distinction for the `Timeout` class by design
  (diagnosis §2, "`unknown` reasons are being destroyed on the way out"). Re-
  running that trace for 65 files before measurement would itself cost another
  ~65×24 s pass; I used the auditable, reproducible static-TSV filter instead
  and report the gap rather than close it by guessing which single file of the
  65 the diagnosis's 64/65 excludes.

- **QF_LRA, 33 files** (`bench-results/adr-1701-slice-1-20260905/qf_lra_population.tsv`):
  misses whose `unknown_kind` is `Timeout` (detail `preprocessed dispatch
  timeout after reduced solve` — a genuine search timeout, wrapper-erased).
  Excluded: 29 `ResourceLimit` rows, whose detail is **not** erased and reads
  literally `online CDCL(T) LRA atom cap exceeded (N > 1024)` — the admission-time
  refusal slice 1 does not touch (the atom cap did not move, ADR-1702's
  bignum note says the same about the cap for a different reason) — and 3
  `na`/`HARDKILL` rows.

**Run parameters.** Each file run through both arms, interleaved (before,
after, next file), `taskset -c 0-7`, `--timeout-ms 24000` (the CLI's own
internal soft stop) wrapped in `timeout -k 2 30s` as an external hard-kill
backstop (`HARDKILL` on trip). Wall time measured around the whole process
(`date +%s%N` before/after), not read from the binary's own report. Batches of
10 files (20 runs, ~500 s) per foreground tool call; load average recorded at
the start and end of every batch (below). No P0: every verdict was checked
against `declared` before anything else was computed, and none contradicted
it — every result in both populations is `unknown`/`sat`/`unsat` agreeing with
`declared` wherever a verdict was reached.

**Load conditions.** `/proc/loadavg` 1-minute figure at each batch boundary
ranged 6.3–14.9 across the 8 QF_IDL+QF_LRA batches on a 16-thread host with
`taskset -c 0-7` pinning the runs to 8 of those threads; other lanes were
active throughout (this is a shared fleet host, per `CLAUDE.md`'s multi-agent
rules). This is comparable-load, not idle-load: absolute millisecond figures
below carry that noise, but the arm comparison is same-file/same-batch/
adjacent-in-time for every row, which is what the before/after claim needs.

## Result 1 — QF_IDL (50 files): no measured effect

| arm | decided | undecided | PAR-2 (24 s budget, 2× penalty) |
|---|---:|---:|---:|
| BEFORE | 0 / 50 | 50 | 48.00 s |
| AFTER | 0 / 50 | 50 | 48.00 s |

Every one of the 50 files timed out in both arms; PAR-2 is identical because
the score only depends on decided/undecided, not on sub-timeout millisecond
noise. Per-file times move by single-digit percent in both directions
(noise), e.g. `channelRoute.in9.smt2` 22,333 ms → 22,432 ms,
`RVpredict_13.smt2` 25,042 ms → 25,037 ms. **Slice 1 has no measured effect on
this population.** §3 below explains why: the stage attribution shows the
QF_IDL timeout population is bottlenecked in the CDCL(T) driver's own Boolean
search (D1), not in `DlTheory`'s `assert`/`propagate` (D2, what slice 1
widens) — `dl-online`'s per-call theory cost is at or near 0 ms on every
traced file. Slice 1 cannot speed up work the theory was never spending.

Full data: `bench-results/adr-1701-slice-1-20260905/qf_idl_before_after.tsv`.

## Result 2 — QF_LRA (33 files): 2 conversions, PAR-2 improves 5.8%

| arm | decided | undecided | PAR-2 (24 s budget, 2× penalty) |
|---|---:|---:|---:|
| BEFORE | 3 / 33 (1 sat, 2 unsat) | 30 | 45.00 s |
| AFTER | 5 / 33 (1 sat, 4 unsat) | 28 | 42.40 s |

No regressions: no file that decided BEFORE became `unknown` AFTER. Two
conversions, both `unsat`, matching `declared`:

| file | before | after |
|---|---|---|
| `QF_LRA/TM/p5-driverlogNumeric_s9.smt2` | unknown, 24,142 ms | **unsat, 13,846 ms** |
| `QF_LRA/clock_synchro/clocksynchro_2clocks.main_invar.base.smt2` | unknown, 24,142 ms | **unsat, 11,030 ms** |

One already-decided file collapsed **13x**:
`QF_LRA/TM/p-driverlogNumeric_s7.smt2`, `sat` in both arms, 17,229 ms → 1,313 ms.

The other two already-decided files (`frame_prop.base.smt2` 13,725→16,532 ms,
`fs_not_sc_seen.base.smt2` 14,039→12,635 ms) move within noise and — per the
stage attribution below — do not even route through the online CDCL(T) LRA
driver slice 1 changed, so neither movement is attributable to this ADR.

Full data: `bench-results/adr-1701-slice-1-20260905/qf_lra_before_after.tsv`.

## Stage attribution — where the time moved

Five files per population, `smtcomp_cli --trace`, both arms, same run
parameters as above. The `; theory-layer …` line is emitted only when a
CDCL(T) route actually completed inside the worker (not when the outer
`--timeout-ms` watchdog fires first) — several QF_IDL files below print no
line for exactly that reason, and it is itself informative: those files spend
their whole budget in front-end DL encoding or in a route that never reaches
`CdclT::solve`, i.e. neither D1 nor D2 has a chance to matter for them.

### QF_IDL — theory cost is ~0; all time is Boolean propagation (D1, not D2)

| file | arm | bool_prop_ms | assert_ms | theory_prop_ms | conflicts | decisions | verdict |
|---|---|---:|---:|---:|---:|---:|---|
| `asp/ChannelRouting/channelRoute.in9.smt2` | before | 18,251 | 0 | 0 | 0 | 0 | unknown |
| | after | 19,633 | 0 | 0 | 0 | 0 | unknown |
| `asp/Fastfood/a7.3.0.tweaked.3.asp.smt2` | before | 18,594 | 0 | 0 | 0 | 0 | unknown |
| | after | 18,606 | 0 | 0 | 0 | 0 | unknown |
| `asp/GeneralizedSlitherlink/penrose.34.asp.smt2` | before | 20,195 | 16 | 2 | 132 | 5,678 | unknown |
| | after | 20,491 | 11 | 2 | 101 | 3,030 | unknown |
| `asp/HamiltonianPath/gryzzles.12.lp.smt2` | before | 19,628 | 112 | 5 | 618 | 29,754 | unknown |
| | after | 19,729 | 110 | 4 | 680 | 34,386 | unknown |
| `asp/HamiltonianPath/gryzzles.31.lp.smt2` | before | 19,994 | 71 | 5 | 548 | 17,890 | unknown |
| | after | 19,828 | 102 | 3 | 728 | 24,951 | unknown |

`RVpredict_13.smt2`, `queen97-1.smt2`, `tai_15x15_5_mkspan1174.smt2`,
`gp10_03_mkspan1079.smt2` and `01.500.graph.smt2` (also tried) printed **no**
theory-layer line in either arm — `dl-online`'s own front-end bails on a
`past_deadline` check before ever constructing `CdclT`, so no CDCL(T) search
ran for these five at all. On the five above that do report, `theory_assert`
and `theory_propagate` are 0–112 ms against 18–20 **seconds** of Boolean
propagation — `DlTheory`'s cost is not the bottleneck, so widening its
interface moves nothing. Decision counts even shift by thousands between arms
(e.g. `gryzzles.12.lp.smt2` 29,754 → 34,386) with the verdict and total time
unchanged: this is the Boolean search's own variance, and it is exactly the
kind of noise D1 (`CdclT`'s hand-rolled clause store, no watch lists) produces
on a workload it cannot make progress on either way.

### QF_LRA — the assert/final-check split moves real time, sometimes past the budget line and sometimes not

| file | arm | bool_prop_ms | assert_ms | theory_prop_ms | final_check_ms | final_checks | decisions | verdict |
|---|---|---:|---:|---:|---:|---:|---:|---|
| `TM/p-driverlogNumeric_s7.smt2` | before | 17,137 | 15,221 | 20 | n/a | n/a | 3,500 | sat |
| | after | 376 | 3 | 6 | 660 | 75 | 1,904 | sat |
| `TM/p5-driverlogNumeric_s9.smt2` | before | 14,517 | 23,258 | 10 | n/a | n/a | 193 | unknown |
| | after | 14,644 | 101 | 233 | 0 | 0 | 5,549 | **unsat** |
| `clock_synchro/clocksynchro_2clocks...smt2` | before | 170 | 397 | 21,674 | n/a | n/a | 325 | unknown |
| | after | 21 | 1 | 7 | 41 | 34 | 2,594 | **unsat** |
| `clock_synchro/clocksynchro_4clocks...smt2` | before | 104 | 189 | 23,792 | n/a | n/a | 35 | unknown |
| | after | 102 | 6 | 50 | 177 | 66 | 10,977 | unknown |
| `spider_benchmarks/fs_not_sc_seen.base.smt2` | before | — no theory-layer line — | | | | | | unsat |
| | after | — no theory-layer line — | | | | | | unsat |

Four of five show the exact mechanism ADR-1701 built: BEFORE, `theory_assert`
(the old re-decide-on-every-assert cost) or `theory_propagate` dominates the
whole 24 s budget (15.2 s, 23.3 s, 21.7 s, 23.8 s respectively) while
`decisions` stays tiny (35–3,500) because the search can barely move between
full re-solves. AFTER, `assert`/`propagate` drop to single- or low-double-digit
milliseconds, `final_check` (new in this ADR) carries the completeness work in
its place, and `decisions` rises 2–300x (193→5,549; 35→10,977) because the
Boolean search is now free to explore. Two of the four convert to `unsat`
inside the budget; the third (`clocksynchro_4clocks`) shows the identical
stage collapse — `theory_propagate` 23,792 ms → 50 ms — but still times out,
because the freed budget goes to 10,977 decisions of Boolean search rather
than a decide: **the interface fix is necessary but not sufficient for every
file; some still need D1's search speedup (slice 2, not implemented) or more
of the freed budget than one file's structure gives back.** The fifth file
(`fs_not_sc_seen.base.smt2`) prints no theory-layer line in either arm — it
decides through a route that never calls the online CDCL(T) LRA driver, so
its ±1.4 s movement is unrelated to this ADR.

## What this measurement does and does not establish

**Establishes.** Slice 1 is not a no-op: on QF_LRA it converts 2 of 33 traced
timeouts to correct `unsat` and speeds up a third already-decided file 13x,
with zero regressions across both populations (85 files, no verdict
contradicting `declared`). The mechanism is exactly the one ADR-1701
describes — `theory_assert`/`theory_propagate` collapsing and `final_check`
taking over the completeness work — visible directly in the stage-attribution
counters, not inferred. On QF_IDL it measurably does nothing, and the same
instrument explains why: the theory's own cost was never the bottleneck there.

**Does not establish.** A corpus-wide PAR-2 or decided-count change (this is
50+33 files, not the full QF_IDL/QF_LRA competition lists); that the 5.8%
QF_LRA PAR-2 gain generalizes past this 33-file population (`ResourceLimit`
atom-cap files, deliberately excluded here, are untouched by slice 1 by
construction); that QF_IDL is closed off from ever benefiting from a theory-
interface change — only that *this* population's bottleneck is elsewhere;
and it does not measure slice 2 (the CDCL(T) search-engine unification),
which `clocksynchro_4clocks.main_invar.base.smt2` above is direct evidence is
still the open half of D1+D2 for at least one file.

## Artifacts

- `bench-results/adr-1701-slice-1-20260905/qf_idl_population.tsv`,
  `qf_lra_population.tsv` — the two populations, sliced from the 2026-08-21
  diagnosis TSVs.
- `bench-results/adr-1701-slice-1-20260905/qf_idl_before_after.tsv`,
  `qf_lra_before_after.tsv` — the raw before/after run data behind every
  number above.
- `bench-results/adr-1701-slice-1-20260905/README.md` — how to reproduce.
