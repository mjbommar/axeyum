# QF_ABV: where the budget actually goes on the files we lose

Measured 2026-09-08 on s4 at solver commit `f24c61f91`, through the **front
door** (`target/release/examples/smtcomp_cli <file> --trace --timeout-ms 24000`,
`taskset -c 0-7`, host load ~11), over the committed 19-file loss population
`bench-results/parity-losses-20260905/QF_ABV.txt`.

This is the front-door re-derivation the
[parity loss census](../11-design-review/2026-09-05-parity-loss-census.md)
correction block asks for before any `class` value in that file may be used for
`QF_ABV`. **It supersedes that division's class column**, which was produced by
`explain_corpus` and is wrong about the route on most of the list.

## Summary

| | files |
|---|---:|
| **decided by the current tree** (the population is stale) | 5 |
| declined with budget left — a deterministic bound, not the clock | 2 |
| tried and timed out | 12 |
| memory / size bound reached terminally | 0 |
| `unknown` for any other reason | 0 |

Of the twelve timeouts, **six spent the budget in the lazy CEGAR's select-
congruence violation scan**, which walks every site pair and evaluates both of
its index terms:

| file | rounds | pairs scanned | index evaluations | lemmas produced |
|---|---:|---:|---:|---:|
| `klee-selected-smt2/cu-no-caches/_csplit-query-000018.smt2` | 36 | 73,970,610 | 147,940,030 | 35 |
| `klee-selected-smt2/cu-no-caches/_csplit-query-000093.smt2` | 25 | 50,723,200 | 103,046,358 | 24 |
| `klee-selected-smt2/cu-large-qids/_lbracket-query-052.smt2` | 82 | 49,953,348 | 100,220,996 | 210 |
| `klee-selected-smt2/cu-no-caches/_lbracket-query-000333.smt2` | 50 | 30,166,801 | 60,327,512 | 91 |
| `klee-selected-smt2/cu-no-caches/_csplit-query-000188.smt2` | 13 | 25,361,848 | 51,783,800 | 12 |
| `2018-Mann/arbiter_array_cex_w32d32q16n4b34.smt2` | 6 | 722,240 | 1,444,400 | 31 |

**More than fifty million index-term evaluations to produce fewer than 250
lemmas**, on files that carry at most 2,294 abstracted reads. The scan is
`O(n²)` in the reads on one array and the deadline poll inside it read the
clock once per candidate pair.

Two of the twelve additionally paid for an eager Ackermann constraint set the
route that uses them never looks at:
`_csplit-query-000263.smt2` was killed **inside** that build (2,113,446 pairs,
zero CEGAR rounds reached), and `_csplit-query-000018/93/188` each built
4,226,892 pairs **twice** — once as the lazy route's admission test, once by the
route it admits to — and discarded both copies.

## Method, and why the previous classification was wrong

The route trail (`crate::RouteTrace`, ADR-1760) records an attempt **when the
route returns**. On a division whose losses are watchdog kills, the route that
spent the budget is by definition the one that did not return, so it is the one
attempt missing from the trail. Measured here: `bmc-arrays/bubbleSort.smt2`
printed `bound_by=fd:parse … 20ms` for a file that spent 25 seconds inside
`abv-online-cdclt`.

`crate::AbvStats` (`crates/axeyum-solver/src/abv/instruments.rs`) closes that
gap: it is opt-in, clock-free, records route **entry** as well as return, and
mirrors onto the cross-thread live board, so a watchdog kill prints
`; partial abv in_flight=<route> …`. It is armed by `--trace` alongside the
eight instruments already on that flag.

## Per-file classification

`in_flight` is the route that was running when the reading was taken; `—` means
every entered route returned.

| file | verdict | in flight | what it was doing |
|---|---|---|---|
| `dwp_formulas/…md5sum.set_char_quoting…` | **sat** | — | decided; no longer a loss |
| `dwp_formulas/…ptx.bkm_scale…` | **sat** | — | decided; no longer a loss |
| `dwp_formulas/…sum.set_char_quoting…` | **sat** | — | decided; no longer a loss |
| `dwp_formulas/…env.set_char_quoting…` | **sat** | — | decided; no longer a loss |
| `dwp_formulas/…stty.visible…` | **sat** | — | decided; no longer a loss |
| `dwp_formulas/…cat.next_line_num…` | unknown | — | **`MAX_ROW_ROUNDS` (64) exhausted** after 3.3 s of a 24 s budget |
| `dwp_formulas/…vdir.strcmp_size…` | unknown | — | **`MAX_ROW_ROUNDS` (64) exhausted** after 14.6 s of a 24 s budget |
| `klee…/_csplit-query-000018` | unknown | `array-fast-path` | congruence scan (table above) |
| `klee…/_csplit-query-000093` | unknown | `array-fast-path` | congruence scan |
| `klee…/_csplit-query-000188` | unknown | `array-fast-path` | congruence scan |
| `klee…/_csplit-query-000263` | unknown | `array-fast-path` | killed inside the eager Ackermann build (2,113,446 pairs, 0 rounds) |
| `klee…/_lbracket-query-052` | unknown | — | congruence scan |
| `klee…/_lbracket-query-000333` | unknown | `array-fast-path` | congruence scan |
| `2018-Mann/arbiter_array_cex…` | unknown | `array-fast-path` | congruence scan; also the largest encoding (2.08 M AIG nodes, 509 k CNF vars) |
| `brummayerbiere/fifo32ia04k08` | unknown | `array-fast-path` | **`MAX_ROW_SITES` (4096) refused a site** (4,109 materialised); scalar search |
| `brummayerbiere/wchains140se` | unknown | `array-fast-path` | **`MAX_ROW_SITES` (4096) refused a site** (4,484 materialised); 313,040 eager pairs built |
| `dwp_formulas/…mkfifo.get_quoting_style…` | unknown | `array-fast-path` | 29 rounds, scalar search |
| `bmc-arrays/bubbleSort` | unknown | **`abv-online-cdclt`** | route never returned |
| `platania/no_init_simple_delete55` | unknown | **`abv-online-cdclt`** | route never returned |

### Two printed reasons that are not the operative one

Both are the defect class the repository's measurement rules warn about, and
both were found by making the counter disagree with the message:

- **`MAX_ROW_SITES` refuses a site by returning `Ok(None)`**, which the caller
  cannot tell apart from "this array read is a shape we do not model" — so the
  route reports *"lazy-ROW declines: an array read is outside the modelled
  store/variable/const-array fragment"*. On `fifo32ia04k08` and `wchains140se`
  that message is describing a **capacity** event.
  `AbvStats::row_site_cap_refusals` is the counter that separates them.
- **`dwp cat.next_line_num` and `dwp vdir.strcmp_size` report** *"array shape
  left undecided by the lazy ROW/extensionality path and refused by bounded
  array elimination"*. They exhausted `MAX_ROW_ROUNDS = 64` — a deterministic
  round cap — with 20.7 s and 9.4 s of their budget unspent. The message names a
  shape; the event is a bound.

## The budget the online route keeps for itself

`abv-online-cdclt` runs first on every array query and takes `config.timeout` in
**full**, leaving nothing for the array routes below it. On four files in this
population it spent 24.009 s of a 24 s budget, declined, and `array-fast-path`
then decided the file in **0.191 s** — those four are `sat` today only because
the harness's watchdog grace period outlasts the budget:

```
; route decided_by=array-fast-path bound_by=abv-online-cdclt last=array-fast-path
  bound_ms=24009 total_ms=24207 attempts=5
   abv-online-cdclt   declined   24.009s  budget  online UFBV canonical CdclT search exhausted its budget
   array-fast-path    decided     0.191s
```

The tree already has the pattern for this — `dl_online`'s
`structural_probe_timeout` and `auto.rs`'s `UF_ARITH_LADDER_RESERVE_SHARE` both
reserve a share of the clock for the ladder below a probe. `abv-online-cdclt`
has no such reserve. Acting on it needs an A/B over the full 200-file division
(which files does that route decide today, and how long do they take?), so it is
recorded here as a measured opportunity rather than taken blind.

## Bounds this division reaches, and their registry status

Every one of these fired or was reached in this measurement. None of them was in
`crate::config_registry` before this note; `crates/axeyum-solver/src/abv.rs` and
`crates/axeyum-solver/src/ufbv_online.rs` are still not in `GOVERNED_FILES`, so
the rest of their constants remain unclaimed.

| constant | value | reached on |
|---|---:|---|
| `abv.rs::MAX_ROW_SITES` | 4096 | `fifo32ia04k08`, `wchains140se` |
| `abv.rs::MAX_ROW_ROUNDS` | 64 | `dwp cat.next_line_num`, `dwp vdir.strcmp_size` |
| `ufbv_online.rs::MAX_INPUT_DAG_NODES` | 16_384 | `arbiter_array_cex…` (32,695 nodes) |

## Reproducing

```sh
cargo build --release -p axeyum-bench --example smtcomp_cli
while read -r f; do
  taskset -c 0-7 target/release/examples/smtcomp_cli "$f" --trace --timeout-ms 24000
done < bench-results/parity-losses-20260905/QF_ABV.txt
```

The `; abv …` line is printed only when an array route was reached, and the
`; partial abv …` form only after a watchdog kill; a run without `--trace`
installs no board and every recording site is one thread-local `bool` read.
