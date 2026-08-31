# ADR-1095: Draw 13 is declined — two held-out-safe constructions are not four families

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1060 built BOTH of draw 12's named unblocks
(`Nat.avg`/`Nat.pair`, `Max.max`/`Min.min`/`Nat.instMax`/`instMinNat`),
construction-only, deliberately leaving the `FAMILY_MODULES` edit to this
lane. Re-screened against a freshly rebuilt REAL environment (2583
declarations, eleven more than ADR-1060's own number) and both
`natural-avg-pair` and `natural-minmax` reproduce ADR-1060's clean numbers
(R9 0/10, R11 clean) exactly. The draw is refused anyway, by R5, mechanically:
`assign_partitions`'s cycle (`held-out, development, train`, restarted per
draw over the fresh family set sorted by first module name) assigns
held-out only at index `i % 3 == 0`, so 2 fresh families supply at most 1
held-out one — confirmed by running the real `guard()`, not by reading the
code. Reaching R5's 2-held-out minimum needs >= 4 fresh families. Searched
the complete un-owned-module space (`propose-nursery-refill.py`'s exhaustive
`>= 10 hygiene survivors` list, 4 modules) for 2 more; found at most 1
additional family is constructible even combined, giving 3 total, still
short of 4 — verified directly against the real guard(), which reports the
identical `R5 the refill adds 1 held-out families` refusal with all three
families present. Declined; the environment-snapshot refresh is kept (an
accurate, harmless artifact for the next lane), the `FAMILY_MODULES` edit is
not (it cannot pass `guard()` as authored).

Related: ADR-1060 (the construction lane this draw was dispatched against),
ADR-1045 (draw 12, declined; named the exact unblock ADR-1060 built and
first measured R5's two-held-out-family requirement, without deriving the
cyclic mechanism this ADR measures), ADR-0900 (draw 10 declined, the
territory-exhaustion precedent both ADR-1045 and this ADR reproduce),
ADR-0925 (draw 11, authored with exactly 4 fresh families — this ADR
explains mechanically why that number, not some other, was needed),
ADR-0830 (draw 9, "two below-floor held-out combinations, not two new
constructions" — the same n=4-for-2-held-out shape, reached independently)

## Context

`scripts/check-dispatchable-frontier.py --json` reads `4 dispatchable
mirror(s), floor 10` — unchanged from the brief. ADR-1060 built both
constructions ADR-1045 named as the unblock (`Nat.avg`/`Nat.pair`,
`Max.max`/`Min.min`/`Nat.instMax`/`instMinNat`), construction-only per
ADR-0653, and deliberately left `FAMILY_MODULES`/`FAMILY_ROUTES` and every
file under `artifacts/autogenesis/` untouched: "this lane enables a draw; it
does not author one." This lane's task is to author it.

## Step 1 — re-screen both named families against the CURRENT, freshly
rebuilt environment

Built `shape_search --release` fresh (36.2 s) and confirmed all six new
declarations present by name in the dump (`Nat.avg`, `Nat.pair`, `Max.max`,
`Min.min`, `Nat.instMax`, `instMinNat`) — 2583 declarations, eleven more than
ADR-1060's own 2572 (six more lanes landed in between). Refreshed the
committed snapshot:

    ./target/release/examples/shape_search --include-constructed --limit 999999 \
      --kind axiom --kind definition --kind theorem --kind inductive \
      --kind constructor --kind recursor > dump.txt
    python3 scripts/gen-autogenesis-nursery-refill.py --snapshot-from dump.txt
    -> KERNEL_ENVIRONMENT_SNAPSHOT|declarations=2583

Simulated adding both families (in-memory, via `importlib` against the live
module, never writing `FAMILY_MODULES` until the real edit — the same
discipline ADR-1060's own Step 1 used) and ran the real `select()`:

    natural-avg-pair: 10 candidates, R9 0/10, R11 clean,
                       env_hits=[('avg', 'Nat.avg', 1)]  (advisory, its own
                       declaration — the same non-blocking shape ADR-1060
                       recorded)
    natural-minmax:   10 candidates, R9 0/10, R11 clean, env_hits=[]

Both numbers are byte-identical to ADR-1060's own post-declaration screen,
on a tree eleven declarations larger — confirming neither family's
cleanliness was a moment-in-time artifact.

## Step 2 — R5 refuses the draw, and the refusal is measured, not assumed

Editing `FAMILY_MODULES`/`FAMILY_ROUTES` with exactly these two families and
running the real generator:

    autogenesis-nursery-refill: R5 the refill adds 1 held-out families; the
    blind population is already down to two capabilities

This is not a contamination refusal (R9/R11 both passed for both families
above) — it is `assign_partitions`'s own arithmetic. `_with_cycle` sorts the
FRESH family set by `FAMILY_MODULES[f][0]` (first module name) and assigns
`PARTITION_CYCLE = ("held-out", "development", "train")` cyclically,
restarting at `held-out` for each draw. For a fresh set of exactly 2:
`natural-avg-pair` (`Batteries.Data.Nat.Bisect`) sorts first — index 0 —
`held-out`; `natural-minmax` (`Init.Data.Nat.MinMax`) sorts second — index 1
— `development`. One held-out family, not two.

R5 requires `len(new_held_out) >= 2`. The number of held-out slots among `n`
fresh families is `ceil(n/3)` (indices `0, 3, 6, …`), so R5 is unreachable
below `n = 4` — this is why draw 11 (ADR-0925) registered exactly 4 families
and draw 9 (ADR-0830) needed two below-floor combinations to reach the same
shape. ADR-1045's own text ("R5 needs two new held-out families... a
comparably clean second was not found") described the *search* correctly
but not this mechanism; this ADR measures it directly rather than restating
it.

## Step 3 — searching for 2 more families to reach n = 4; finding at most 1

`propose-nursery-refill.py --remeasure` gives the complete, exhaustive list
of un-owned modules with `>= 10` HYGIENE-screened survivors (its own sweep
over all 85 modules-with-survivors in the pinned inventory):

    READY FAMILIES     4
          37  Mathlib.Data.Nat.Log
          22  Mathlib.Data.Nat.Fib.Basic
          21  Mathlib.Data.Int.Fib.Basic
          18  Mathlib.Data.Nat.Bitwise

Per this crate's CLAUDE.md, the hygiene screen OVERCOUNTS — it does not
apply the REAL `select()`'s additional exclusion of anything already drawn
into `nursery-v1`'s own catalog. And `nursery-v1.json` already owns
`natural-logarithm`, `natural-fibonacci`, `integer-fibonacci`, and
`natural-bitwise` as its own train/development/held-out families — so most
of each candidate module's rows are already spent, by a mechanism the
hygiene screen cannot see (it checks module identity, not source-name
overlap with the v1 catalog).

Measured against the real `select()`, standalone:

    Mathlib.Data.Nat.Log         -> 0 screened candidates
    Mathlib.Data.Nat.Fib.Basic   -> 8 screened candidates
    Mathlib.Data.Int.Fib.Basic   -> 6 screened candidates
    Mathlib.Data.Nat.Bitwise     -> 6 screened candidates

All four are individually below the `PER_FAMILY = 10` floor — the SAME
"real screen gives far fewer than the hygiene screen" finding this crate's
CLAUDE.md already records for a different session ("21 ready -> 6 real"),
reproduced here on a different draw with an even starker gap on `Log`
specifically (37 hygiene survivors, 0 real ones — every one of its 89
inventory rows is already claimed by v1's `natural-logarithm`).

Combining modules into one family (the ADR-0830/ADR-0925 "below-floor
combination" technique) was tried exhaustively over all `C(4,2)`, `C(4,3)`,
`C(4,4)` subsets:

    (log, natfib)              ->  8   (fail)
    (log, intfib)               ->  6   (fail)
    (log, bitwise)               ->  6   (fail)
    (natfib, intfib)             -> 10   (PASS)
    (natfib, bitwise)            -> 10   (PASS)
    (intfib, bitwise)            -> 10   (PASS)
    (log, natfib, intfib)        -> 10   (PASS)
    (log, natfib, bitwise)       -> 10   (PASS)
    (log, intfib, bitwise)       -> 10   (PASS)
    (natfib, intfib, bitwise)    -> 10   (PASS)
    (all four)                    -> 10   (PASS)

`Mathlib.Data.Nat.Log` contributes essentially nothing to any combination
(every combination including it scores the same as without it) — it is
already fully consumed by v1. The three PAIRWISE-passing combinations all
draw on the same two modules out of `{natfib, intfib, bitwise}`; there is no
way to partition these three modules into TWO disjoint groups that both
reach 10, because any two-module group already exhausts the real content
(`8 + 6` or similar) and the remaining single module never reaches 10 alone.
So **at most one additional family is constructible from this candidate
space**, not two.

Verified directly rather than inferred: ran the real generator with all
three families present (`natural-avg-pair`, `natural-minmax`, and a combined
`natural-fib-bitwise-combo` over `Mathlib.Data.Nat.Fib.Basic` +
`Mathlib.Data.Int.Fib.Basic` + `Mathlib.Data.Nat.Bitwise`, 10 real
candidates):

    GUARD REFUSED: R5 the refill adds 1 held-out families; the blind
    population is already down to two capabilities
      natural-avg-pair:            partition=held-out
      natural-minmax:              partition=development
      natural-fib-bitwise-combo:   partition=train

Three fresh families give the identical cycle outcome as two (`ceil(3/3) =
1`) — the refusal is unchanged. Reaching `ceil(n/3) >= 2` needs `n = 4`, and
no fourth family exists in the currently reachable statement space (the
combined filler already consumes every module scoring above zero in the
real screen; `Log` alone or in any combination adds nothing further).

## Decision

**Decline draw 13.** No held-out-safe, floor-clearing draw exists today —
not because the two built constructions are unsafe (both are confirmed
clean, twice, on two different environment snapshots), but because R5's
cyclic partition assignment structurally requires 4 fresh families to
produce 2 held-out ones, and the complete un-owned-module space (measured
exhaustively via `propose-nursery-refill.py --remeasure`'s own ready list)
supplies at most 3.

**Kept:** the environment-snapshot refresh (2552 -> 2583) — an accurate
record of the built constructions and every declaration landed since, of
independent value to the next lane's own re-screen. One measured, benign
side effect: `Max.max`/`Min.min` becoming admissible constants also makes
two previously-inadmissible rows of the ALREADY-preregistered `train` family
`natural-basic-arithmetic` newly admissible
(`Nat.add_eq_max_iff`, `Nat.add_eq_min_iff`), which sort ahead of
`Nat.add_eq_two_iff` and `Nat.add_eq_zero` in that family's `PER_FAMILY = 10`
window and displace them. Diffed `nursery-v2-extension.json`'s `entries` by
`fact_id` before/after the refresh: exactly 2 dropped, 2 added, both in
`natural-basic-arithmetic`/`train` — no other family, and no held-out or
development row, is touched. Both displaced facts
(`F:ml430-nat-add-eq-two-iff-25385c65`,
`F:ml430-nat-add-eq-zero-64233539`) are already `proved`; this generator
only ever writes a fact where none exists (ADR-0615), so their files are
untouched on disk and remain valid, proved ledger entries outside the
regenerated manifest's `entries` list. This is `train`-partition bookkeeping
churn from environment growth, not a blind-evaluation breach.

**Not kept:** the `FAMILY_MODULES`/`FAMILY_ROUTES` edit registering
`natural-avg-pair`/`natural-minmax` — it cannot pass `guard()` as authored
(R5), so it does not belong in the tree as dead, permanently-failing code.
Reverted to `HEAD`.

`check-autogenesis-holdout-isolation.py`: `held_out=146` before and after
this lane's work (identical to the value at session start, since
`artifacts/autogenesis/nursery-v1.json` was never touched).

## Consequences

- **Both built constructions remain available and clean for a future
  draw** — they need no further verification, only 2 more fresh, real
  (not combined-filler) held-out-safe families to satisfy R5 alongside
  them, or a generator change that this ADR does not propose (R5's rule is
  a deliberate blind-breadth requirement, not a bug).
- **The `>= 10 hygiene survivors` candidate space is now measured
  exhausted**, not merely searched. A future draw needs a genuinely NEW
  construction-level unblock — the same move ADR-1045/ADR-1060 already
  made once — not another sweep over `propose-nursery-refill.py`'s current
  output, which is unchanged from this ADR's own measurement until new
  modules enter the un-owned space (by a Mathlib version bump) or new
  constructions land in the kernel.
- **The below-floor combination technique (ADR-0830/ADR-0925) has a
  supply limit too**, and this ADR is the first to measure it directly:
  combining modules trades floor-clearance for a topical fingerprint no
  R11-clean held-out slot can use, and the modules available to combine are
  the same finite, mostly-already-spent set the individual screen already
  rejected.
