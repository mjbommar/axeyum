# Budget curve, 2026-09-09 — solved count versus budget, both solvers

Raw data behind
[`docs/research/03-measurements/budget-curve-2026-09-08.md`](../../docs/research/03-measurements/budget-curve-2026-09-08.md).
Read the note for what the numbers mean; this directory records only what was
measured and how, so a re-run is possible and a mis-reading is not.

**The question:** is our remaining gap to the reference engineering (a constant
factor a longer budget would buy) or capability (something a clock cannot
reach)? **The answer: capability.** Of 135 files the reference decides at 24 s
and we do not, 12 decide with 2.5x the clock and 123 do not.

## What was run

`scripts/parity-run.sh` — the committed protocol harness, no second harness —
at `PARITY_BUDGET_S` of 6, 12, 24 and 60, `PARITY_MEM_GB=8` throughout, on the
committed 200-file lists in `../parity-lists/`. Both solvers at every budget;
the reference is whatever that script's own division table selects (cvc5 1.3.4
for QF_UFLIA / QF_LRA / QF_LIA, bitwuzla 0.9.1 for QF_ABV), with no portfolio
flags.

Solver commit `e99d08848`, one `smtcomp_cli` release binary built once and
copied to every host so no arm is confounded by a different build.

Budget order was **24 first**, then 6, 12, 60 — so an interruption still leaves
the externally comparable row — and then a **fifth pass at 24 s again**.

## Why there are two 24 s passes

The boxes got quieter during the sweep (another lane's `route_solo` oracle
sweep wound down): loads read 3.0–4.1 at 02:46 UTC and 1.0–2.0 by 04:39 UTC.
Since the 60 s pass runs last it would have run on the quietest machine, and
every file it recovered that way would have been scored *time-bound* — the
answer that says "keep optimising". So `repeat24.sh` runs a second 24 s pass
**after** the 60 s pass, as its load-matched partner. The classification uses
that repeat as its baseline.

It also gives a number we had only ever guessed at: **24 s versus 24 s repeat,
same list, same binary, same host, is the contention noise floor.** Measured:
axeyum moved **1 file out of 800**; cvc5 moved **11 on QF_LRA alone** (134
loaded, 145 quiet). The noise is real and it is **asymmetric**, which is why a
ratio measured under load is not a floor even though each count is.

## Files

| file | contents |
|---|---|
| `<div>-b6.tsv`, `-b12.tsv`, `-b24.tsv`, `-b60.tsv` | per-file sidecars exactly as `parity-run.sh` wrote them: `file`, `axeyum`, `reference`, `declared` |
| `<div>-b24r.tsv` | the load-matched 24 s repeat, run after the 60 s pass |
| `classification.tsv` | `division`, `baseline`, `class`, `file` — 135 rows, one per loss, `time-bound` or `capability-bound` |
| `analyze.py` | builds every table in the note from the sidecars. It counts; it never infers a verdict. |
| `driver.sh` | the four-budget sweep for one division, as run on each host |
| `repeat24.sh` | the load-matched repeat; waits for `driver.sh`'s `ALLDONE` so two sweeps of one division never overlap |

## Reproducing

```sh
# per host, one division each, from a clean detached worktree with the binary in place
./driver.sh QF_LRA          # 6/12/24/60, ~5.5 h for QF_LRA
./repeat24.sh QF_LRA        # blocks until driver.sh finishes, then the 24 s partner
python3 analyze.py <sidecar-dir> QF_UFLIA QF_LRA QF_LIA QF_ABV
```

Do not run two budgets of one division at once. `parity-run.sh` locks its
sidecar per worktree, but two sweeps still contend for cores and both numbers
come out depressed.

## Ledger

Twenty entries appended to [`../PARITY.md`](../PARITY.md), all `SOUND`, zero
disagreements. Note that every entry's `per-file detail` row names the same
`parity-details/<div>.tsv` path because each pass overwrote it in its own
worktree — the per-budget copies are the files in this directory.
