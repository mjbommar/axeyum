# Does the ADR-2142 snapshot fix move the board? (sizing — run in progress)

**2026-09-17.** Interleaved per-file A/B of the commit BEFORE the ADR-2142 fix
against the commit that IS the fix, over all **16 divisions × 200 files** of
`bench-results/parity-lists/`, on s5 and s6. This section was written and
committed **before any run** so the sizing is on record independent of the
result.

## The two arms differ by exactly the fix commit

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
delta is 0 flips and ≥ 0 decided**, with any decided gain coming only from files
whose walk ate the 24 s budget.

Both binaries were built fresh on s4 from `scripts/lane-snapshot.sh <ref>`
(`--touch` extraction) into their own target directories
(`/data0/axeyum-lane-targets/ax-board-2142-{a,b}`), `--release --features full
-p axeyum-bench --example smtcomp_cli`, each in 2 m 09–10 s (a real build, not
a cached artifact — the 09-14 board caught a 0.85 s "build" handing back a
three-day-old binary). Sizes 45,405,088 and 45,394,856 bytes; hashes distinct
and re-verified with `sha256sum -c` on both s5 and s6 before launch.

## Population and frame

- Lists: `bench-results/parity-lists/{QF_ABV,QF_BV,QF_DT,QF_FP,QF_IDL,QF_LIA,QF_LRA,QF_NIA,QF_NRA,QF_RDL,QF_S,QF_SLIA,QF_UF,QF_UFLIA,QF_UFLRA,UF}.txt`,
  200 corpus-relative PATHS each (the fix the 09-14 board asked for), 3,200
  distinct files. These are the parity-ledger lists (`bench-results/PARITY.md`
  pins their sha256 prefixes: QF_BV `6f873e15b191`, QF_SLIA `7d539c0182a6`,
  UF `ab432240d2f7`, …).
- **Population caveat, measured before launch:** the 09-15 board's row files
  are the 09-14 basename-reconstructed population, not these lists. They agree
  file-for-file on 12 divisions (200/200 or 199/200) but not on `QF_BV` (106 in
  common), `QF_LIA` (74 in common, and the 09-15 rows hold only 140 distinct
  paths), `QF_SLIA` (172) and `QF_UF` (180). So the A-arm level here is not
  directly comparable to the 09-15 level on those four divisions, and the
  z3/cvc5 reference totals (2,790 / 2,652) were taken on the 09-14 population.
  The A/B DIFFERENCE is unaffected: both arms see identical files.
- 4 shards, one pinned physical core (a sibling pair) each: s5 `1,9`, s5
  `3,11`, s6 `1,9`, s6 `3,11`. Both hosts idle at launch (load 0.18 / 0.02,
  `pgrep -c smtcomp` = 0). Files interleaved ACROSS divisions in each shard
  (`make-shard-lists.py`: file i of division j → shard (i + j) mod 4; 50 files
  of every division in every shard), so a partial read is a sample.
- Per run: 24 s wall (`--timeout-ms 24000`, `timeout 40`), `ulimit -v` 8 GiB,
  arms back to back on the same file, order alternating per file. Wall time
  read from `$EPOCHREALTIME` (s5's `date` is uutils); each shard self-checks a
  200 ms sleep reads 150–400 ms before its first solve, and records each
  arm's exit status per file.
- Scripts beside this README: `ab-two-bins.sh` (the 09-14 runner with the
  clock and exit-status changes), `board-ab-driver.sh`, `make-shard-lists.py`;
  movers re-checked 3× per arm with
  `bench-results/route-ownership-20260915/recheck-movers.sh`.
