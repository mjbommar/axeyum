# The ADR-2142 snapshot fix on the board: +8 of 3,200 (8 stable gains, 0 losses) in QF_UFLIA/QF_ABV/QF_BV/QF_NIA, and QF_ABV's decided files run 2× faster

**2026-09-17.** Interleaved per-file A/B of **`b11264ebe`** (the commit BEFORE
the ADR-2142 fix) against **`60e23fa39`** (the fix commit itself, whose parent
is `b11264ebe` — the arms differ by exactly one commit), over all **16
divisions × 200 files** of `bench-results/parity-lists/`. Both arms back to back
on the same file on the same pinned physical core, order alternating per file,
24 s wall / 8 GiB `ulimit -v`, 4 shards on s5 cores `1,9`+`3,11` and s6 cores
`1,9`+`3,11`, both hosts idle (load < 0.2, no other solver process) for the whole
2 h 43 m.

| | |
|---|---:|
| A (before the fix) | **2,424** |
| B (the fix) | **2,432** |
| net | **+8** |
| gains / losses / sat↔unsat flips (raw, one pass) | **9 / 1 / 0** |
| gains / losses after 3× per-arm recheck | **8 STABLE-GAIN / 0 STABLE-LOSS / 2 ambient (BOTH-DECIDE)** |
| exit-status differences between arms | **0** (5 files abort with 134 in BOTH arms — see below) |
| soundness | **4,380 comparisons vs declared `:status` (2,186 A + 2,194 B), 0 disagreements** |
| both-decided wall, A → B | **4,659.7 s → 4,475.0 s** (−4.0 %), median 106 ms → 106 ms |
| both-decided files where B's wall < 0.5× A's | **31** (30 `QF_ABV`, 1 `QF_BV`) |
| rows scored | 3,200 of 3,200; 0 malformed |

## The question, answered in plain words

**The fix moved 8 files on the 3,200-file board, all gains, in four divisions:
`QF_UFLIA` +5, `QF_ABV` +1, `QF_BV` +1, `QF_NIA` +1 — and every parity number
quoted for those four divisions before 2026-09-17 undercounts by exactly that
much; the other twelve divisions' numbers stand.** Each of the eight is a file
that was `unknown` because arm A ran to the 24 s budget and arm B decides in
8–23 s, 3 of 3 passes in each arm (five `QF_UFLIA`: four `wisas/xs_*` `sat` and
one `mathsat/Hash` `unsat`; one `dwp_formulas` `unsat`; one `Sage2` `sat`; one
`VeryMax/ITS` `sat`). That is the ADR's predicted shape made visible: nothing
flipped between `sat` and `unsat` and nothing disagreed with a declared
`:status` (0 over 4,380 comparisons), because the fix changes only how long a
trajectory takes, so the only verdicts that can move are the ones the clock
cut off. The single-pass board also showed one more `QF_UFLIA` gain and one
`QF_UFLRA` loss; both dissolved on recheck (each arm decides the file 3/3), so
they were ambient and `QF_UFLRA` is unchanged. The one division whose *time*
moved a lot without its count moving is `QF_ABV`: its 188 both-decided files
went from 293.5 s to 148.2 s (−49 %), 30 of them at under half the old wall
(the `dwp_formulas` family: 73 files, 261 s → 120 s, all `sat`) — those were
never near the budget, so they were already counted, but every timing claim
about `QF_ABV` made before today is roughly 2× pessimistic. So the pre-fix
levels `QF_UFLIA` 161, `QF_ABV` 188, `QF_BV` 186, `QF_NIA` 86 read 166, 189,
187, 87 with the fix, on this population, and the board reads 2,424 → 2,432.

## Per division

| division | A | B | net | gains | losses | flips | rc≠ | cmp A/B | dis | both | A wall s | B wall s | A med ms | B med ms | B<½A | noise |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_ABV | 188 | **189** | **+1** | 1 | 0 | 0 | 0 | 188/189 | 0 | 188 | 293.5 | **148.2** | 105 | 105 | **30** | 152 |
| QF_BV | 186 | **187** | **+1** | 1 | 0 | 0 | 0 | 171/172 | 0 | 186 | 150.8 | 138.5 | 105 | 105 | 1 | 175 |
| QF_DT | 171 | 171 | +0 | 0 | 0 | 0 | 0 | 171/171 | 0 | 171 | 58.0 | 58.6 | 105 | 105 | 0 | 171 |
| QF_FP | 199 | 199 | +0 | 0 | 0 | 0 | 0 | 199/199 | 0 | 199 | 29.1 | 29.3 | 105 | 105 | 0 | 199 |
| QF_IDL | 112 | 112 | +0 | 0 | 0 | 0 | 0 | 112/112 | 0 | 112 | 238.6 | 250.2 | 306 | 355 | 0 | 109 |
| QF_LIA | 120 | 120 | +0 | 0 | 0 | 0 | 0 | 117/117 | 0 | 120 | 192.6 | 192.8 | 105 | 105 | 0 | 119 |
| QF_LRA | 107 | 107 | +0 | 0 | 0 | 0 | 0 | 97/97 | 0 | 107 | 79.1 | 79.0 | 105 | 105 | 0 | 107 |
| QF_NIA | 86 | **87** | **+1** | 1 | 0 | 0 | 0 | 86/87 | 0 | 86 | 833.9 | 815.0 | 10,864 | 10,814 | 0 | 84 |
| QF_NRA | 124 | 124 | +0 | 0 | 0 | 0 | 0 | 123/123 | 0 | 124 | 114.7 | 112.8 | 105 | 105 | 0 | 124 |
| QF_RDL | 151 | 151 | +0 | 0 | 0 | 0 | 0 | 151/151 | 0 | 151 | 314.7 | 330.4 | 505 | 506 | 0 | 151 |
| QF_S | 186 | 186 | +0 | 0 | 0 | 0 | 0 | 165/165 | 0 | 186 | 37.3 | 37.3 | 105 | 105 | 0 | 186 |
| QF_SLIA | 193 | 193 | +0 | 0 | 0 | 0 | 0 | 7/7 | 0 | 193 | 159.1 | 159.1 | 107 | 106 | 0 | 193 |
| QF_UF | 200 | 200 | +0 | 0 | 0 | 0 | 0 | 200/200 | 0 | 200 | 105.2 | 105.7 | 105 | 105 | 0 | 197 |
| QF_UFLIA | 161 | **167** | **+6** | 6 | 0 | 0 | 0 | 161/167 | 0 | 161 | 1,035.5 | 1,010.1 | 1,205 | 1,105 | 0 | 156 |
| QF_UFLRA | 150 | 149 | **−1** | 0 | 1 | 0 | 0 | 150/149 | 0 | 149 | 664.1 | 656.0 | 3,309 | 3,207 | 0 | 148 |
| UF | 90 | 90 | +0 | 0 | 0 | 0 | 0 | 88/88 | 0 | 90 | 353.6 | 352.0 | 2,708 | 2,658 | 0 | 90 |
| **total** | **2,424** | **2,432** | **+8** | **9** | **1** | **0** | **0** | **2,186/2,194** | **0** | **2,423** | **4,659.7** | **4,475.0** | 106 | 106 | **31** | **2,361** |

Columns: `cmp A/B` = decided verdicts compared against a declared `:status`
(the denominator is published beside every zero, deliberately); `both` =
both-decided files, over which the wall columns are computed; `B<½A` = files
where B's wall is under half of A's; `noise` = both-decided files whose wall
ratio is within ±25 %. `board.tsv` carries the same numbers machine-readably;
`analysis.txt` is the analyzer's full output, and the four `shard*.tsv` files
are every row (absolute corpus path, both verdicts, both walls in ms from
`$EPOCHREALTIME`, both exit statuses, which arm ran first, declared `:status`).

## The movers, raw and rechecked

Raw movers from the single interleaved pass (A verdict / A ms → B verdict / B
ms):

| division | file | A | B |
|---|---|---|---|
| QF_ABV | `dwp_formulas/try5_small_difret_functions_dwp_mkfifo.get_quoting_style.il.dwp.smt2` | unknown 24,126 | **unsat 8,012** |
| QF_BV | `Sage2/bench_10451.smt2` | unknown 25,227 | **sat 9,313** |
| QF_NIA | `20170427-VeryMax/ITS/From_T2__slayer-4-filtered.t2__p22683_terminationG_0.smt2` | unknown 24,226 | **sat 23,325** |
| QF_UFLIA | `wisas/xs_17_27.smt2` | unknown 24,323 | **sat 17,318** |
| QF_UFLIA | `wisas/xs_21_31.smt2` | unknown 24,325 | **sat 17,720** |
| QF_UFLIA | `mathsat/Hash/hash_uns_04_11.smt2` | unknown 24,327 | **unsat 17,116** |
| QF_UFLIA | `mathsat/Hash/hash_uns_05_20.smt2` | unknown 24,330 | **unsat 16,116** |
| QF_UFLIA | `wisas/xs_16_26.smt2` | unknown 24,331 | **sat 16,319** |
| QF_UFLIA | `wisas/xs_20_30.smt2` | unknown 24,328 | **sat 16,321** |
| QF_UFLRA | `mathsat/RandomCoupled/pb_real_30_0600_10_16.smt2` | **sat 19,926** | unknown 25,032 |

Every mover re-run **3× per arm** on one pinned core (s5 `1,9` for the first
five, s6 `1,9` for the last five, both hosts otherwise idle) at the same 24 s /
8 GiB envelope with `recheck-movers.sh` (arms alternating within the three
passes; exit status recorded per pass — all 60 passes exited 0):

| division | file | A ×3 | B ×3 | class |
|---|---|---|---|---|
| QF_ABV | `dwp_formulas/try5_small_difret_functions_dwp_mkfifo…dwp.smt2` | unknown unknown unknown | unsat unsat unsat | **STABLE-GAIN** |
| QF_BV | `Sage2/bench_10451.smt2` | unknown unknown unknown | sat sat sat | **STABLE-GAIN** |
| QF_NIA | `20170427-VeryMax/ITS/From_T2__slayer-4-filtered…G_0.smt2` | unknown unknown unknown | sat sat sat | **STABLE-GAIN** |
| QF_UFLIA | `wisas/xs_17_27.smt2` | unknown unknown unknown | sat sat sat | **STABLE-GAIN** |
| QF_UFLIA | `wisas/xs_21_31.smt2` | unknown unknown unknown | sat sat sat | **STABLE-GAIN** |
| QF_UFLIA | `mathsat/Hash/hash_uns_04_11.smt2` | unknown unknown unknown | unsat unsat unsat | **STABLE-GAIN** |
| QF_UFLIA | `mathsat/Hash/hash_uns_05_20.smt2` | unsat unsat unsat | unsat unsat unsat | BOTH-DECIDE (ambient: A's board `unknown` was a noise pass at the budget edge) |
| QF_UFLIA | `wisas/xs_16_26.smt2` | unknown unknown unknown | sat sat sat | **STABLE-GAIN** |
| QF_UFLIA | `wisas/xs_20_30.smt2` | unknown unknown unknown | sat sat sat | **STABLE-GAIN** |
| QF_UFLRA | `mathsat/RandomCoupled/pb_real_30_0600_10_16.smt2` | sat sat sat | sat sat sat | BOTH-DECIDE (ambient: B's board `unknown` was a noise pass; A took 19.9 s on the board) |

**Stable: 8 gains, 0 losses, 0 unstable.** The board's raw `+8` (9 − 1) and its
stable `+8` (8 − 0) agree by coincidence, not by construction: one raw gain and
the one raw loss both dissolve on recheck, in opposite directions. So the
stable per-division movement is `QF_UFLIA` **+5**, `QF_ABV` **+1**, `QF_BV`
**+1**, `QF_NIA` **+1**, and `QF_UFLRA` **0**; the `QF_NIA` gain, at 23.3 s on
the board, is nonetheless 3/3 in B and 0/3 in A. The 2 ambient rows in 3,200
are a 0.06 % flip rate, under the 1–1.5 % the recheck script's header records
for these boxes under load, consistent with the hosts having been idle.
`recheck-movers.tsv` beside this README is the raw output.

## Wall time: where the fix is visible without moving a verdict

On the 2,423 both-decided files, B's wall is 4.0 % lower in total and the
median is unchanged at 106 ms (the floor is process start-up of a 45 MB binary
over NFS). The saving is concentrated: on the 637 both-decided files A took
≥ 1 s on, 37 are ≥ 20 % faster under B and 1 is ≥ 25 % slower; the other 599
are within noise. Of the 31 files under half of A's wall, 30 are `QF_ABV` — 29
of them `dwp_formulas` (73 files on the list, 261.2 s → 120.0 s; e.g.
`try5_small_difret_functions_dwp_stty.visible.il.dwp.smt2` 20.4 s → 1.3 s,
`try5_small_true_functions_flanagansaxe_cat.next_line_num.il.flanagansaxe.smt2`
18.1 s → 4.2 s) plus `platania/copy_array/copy_array11.c.smt2` 3.9 s → 1.0 s —
and one `QF_BV` (`spear/samba_v3.0.24/bin_eventlogadm_vc352379.smt2` 5.0 s →
2.2 s). Every one of these is `sat`, which is the ADR's diagnosis exactly: a
long conflict-free descent on a large trail, where every decision set a fresh
high-water mark and re-walked the whole trail. The divisions whose wall sums
rose (`QF_IDL` +4.9 %, `QF_RDL` +5.0 %) rose uniformly with no file outside
noise, and their per-file medians moved by 1 ms and 49 ms; those are load, not
the fix (the interleaving cancels it in the count and only approximately in the
sum).

## Soundness and the five aborts

0 flips; 0 disagreements over 4,380 comparisons. Five files exit 134 (SIGABRT,
the 8 GiB `ulimit -v` firing) in **both** arms with the same wall to within
0.5 s: `UF/sledgehammer/Arrow_Order/smtlib.663965.smt2`,
`UF/sledgehammer/QEpres/uf.924249.smt2`, two
`UF/20170428-Barrett/cdt-cade2015/nada/afp/*` files and
`QF_ABV/brummayerbiere/wchains140se.smt2`. They are pre-existing and identical
across arms (the exit-status column exists so that this can be said rather
than assumed — ADR-2045 measured `losses=0` by verdict and five new aborts
underneath it); they count as undecided in both arms.

## The board totals, and the population caveat

- **A vs B on this population: 2,424 → 2,432 of 3,200.**
- **Against the 09-14 references (z3 2,790, cvc5 2,652) the comparison is
  approximate, because those were taken on the 09-14 basename-reconstructed
  population and this run is on `bench-results/parity-lists/`.** Measured before
  launch: the two populations agree file-for-file on 12 divisions (200/200 or
  199/200) and differ on `QF_BV` (106 in common), `QF_LIA` (74 in common; the
  09-15 rows also hold only 140 distinct paths), `QF_SLIA` (172) and `QF_UF`
  (180). The A-arm levels here agree with the 09-15 B-arm on the 12 shared
  divisions to within the ambient band except where main has moved since
  (`QF_NRA` 117 → 124 is ADR-2121/2126 shipping ON; `QF_NIA` 85 → 86;
  `QF_UFLRA` 149 → 150), and differ where the population differs (`QF_BV` 180
  vs 186, `QF_LIA` 127 vs 120, `QF_SLIA` 196 vs 193). So B's 2,432 is not
  "2,419 + 13"; it is 2,424 + 8 on a population that is the parity ledger's,
  not the head-to-head's. The reference solvers have not been run on
  `parity-lists` as one board in this repository (the per-division entries in
  `bench-results/PARITY.md` were taken over several weeks); a same-day
  reference board on these lists is the next board, not this one.
- **The delta is unaffected by any of that:** both arms saw identical files on
  identical cores back to back.

## Why interleaved, and why the level is not the claim

The 09-14 board measured the same binary at 77, 79 and 85 on one division
depending only on load. This run had the hosts to itself (load 0.0–0.2 at
launch, 1–2 at the end from the shards themselves), so the levels are as clean
as a single-arm run can be, but the claim is still the difference: the count
delta survives contention and the wall-sum delta survives it approximately.
The per-shard lists interleave all 16 divisions (file i of division j → shard
(i + j) mod 4, 50 of every division in every shard), so the partial reads taken
at 539 and 1,134 rows during the run were samples of the board, not prefixes of
one division — and both already showed the final shape (0 flips, the `QF_ABV`
`dwp_formulas` speed-up, the first `QF_BV` gain).

## Sizing, on record before the run

| arm | commit | what it is | `smtcomp_cli` sha256 |
|---|---|---|---|
| A | `b11264ebe` | parent of the fix: the ADR-2142 reproducer commit on the AX-WARM branch (`git rev-parse 60e23fa39^`) | `f75fe25088ad40fdda11cf28e38b6075dda49819f0a609d1ec9872583c628d7f` |
| B | `60e23fa39` | the fix commit itself, whose parent is A — so no cherry-pick was needed and the diff is exactly one commit | `101ef322b4abdd7deee6badd6712dc3fb5913b0a0840775cebffcc3b3d5749ae` |

`git diff --stat b11264ebe 60e23fa39`:

```
 PLAN.md                                            |  19 ++
 crates/axeyum-cnf/src/lib.rs                       |  22 ++
 crates/axeyum-cnf/src/proof_sat.rs                 | 132 +++++++++-
 crates/axeyum-solver/examples/warm_session_age.rs  | 273 +++++++++++++++------
 crates/axeyum-solver/src/incremental.rs            |  16 ++
 docs/plan/status/ax-warm.md                        |  25 ++
 docs/research/09-decisions/README.md               |   1 +
 ...se-snapshot-re-walked-the-trail-per-decision.md | 226 +++++++++++++++++
 8 files changed, 633 insertions(+), 81 deletions(-)
```

The solver-side content of that diff: `proof_sat.rs` gains the two
stable-prefix marks (`target_stable`, `best_stable`) so `snapshot_target_phase`
copies `trail[stable..depth]` instead of `trail[0..depth]`, plus the
`phase_snapshot_entries` counter and its linear-bound test; `lib.rs` and
`incremental.rs` add read-only gauges (`learned_clause_count`,
`total_conflicts`, `retained_*`). No default, schedule or bound moves; the ADR's
claim is that search trajectories are byte-identical, so **the expected verdict
delta was 0 flips and ≥ 0 decided**, with any decided gain coming only from
files whose walk ate the 24 s budget. (That is what was measured.)

Both binaries were built fresh on s4 from `scripts/lane-snapshot.sh <ref>`
(`--touch` extraction) into their own target directories
(`/data0/axeyum-lane-targets/ax-board-2142-{a,b}`), `--release --features full
-p axeyum-bench --example smtcomp_cli`, each in 2 m 09–10 s (a real build, not
a cached artifact — the 09-14 board caught a 0.85 s "build" handing back a
three-day-old binary). Sizes 45,405,088 and 45,394,856 bytes; hashes distinct,
re-verified with `sha256sum -c` on both s5 and s6 before launch, and re-hashed
by each shard's driver at its start (`shard*.log`).

## Population and frame

- Lists: `bench-results/parity-lists/{QF_ABV,QF_BV,QF_DT,QF_FP,QF_IDL,QF_LIA,QF_LRA,QF_NIA,QF_NRA,QF_RDL,QF_S,QF_SLIA,QF_UF,QF_UFLIA,QF_UFLRA,UF}.txt`,
  200 corpus-relative PATHS each (the fix the 09-14 board asked for), 3,200
  distinct files. These are the parity-ledger lists (`bench-results/PARITY.md`
  pins their sha256 prefixes: QF_BV `6f873e15b191`, QF_SLIA `7d539c0182a6`,
  UF `ab432240d2f7`, …).
- 4 shards, one pinned physical core (a sibling pair) each: s5 `1,9`, s5
  `3,11`, s6 `1,9`, s6 `3,11`. Both hosts idle at launch (load 0.18 / 0.02,
  `pgrep -c smtcomp` = 0). Files interleaved ACROSS divisions in each shard
  (`make-shard-lists.py`). Shards ran 11:32–14:15 UTC.
- Per run: 24 s wall (`--timeout-ms 24000`, `timeout 40`), `ulimit -v` 8 GiB,
  arms back to back on the same file, order alternating per file (1,600 rows
  A-first, 1,600 B-first). Wall time read from `$EPOCHREALTIME` (s5's `date` is
  uutils); each shard self-checked a 200 ms sleep at 205 ms before its first
  solve, and recorded each arm's exit status per file.
- Scripts beside this README: `ab-two-bins.sh` (the 09-14 runner with the
  clock and exit-status changes), `board-ab-driver.sh`, `make-shard-lists.py`,
  `analyze.py`; movers re-checked 3× per arm with
  `bench-results/route-ownership-20260915/recheck-movers.sh` (copied unchanged
  to the harness).
