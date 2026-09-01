# Lane: historical-draw-rederivation — a drawn family is history

<!-- plan-section: lane-status -->

Status: COMPLETE (2026-09-01). `gen-autogenesis-nursery-refill.py --check` is
green again, adjudicated in [ADR-1445](../../research/09-decisions/adr-1445-a-drawn-family-is-history-and-is-not-re-screened.md),
with a regression control that fails without the fix and a zero-diff proof over
all 460 already-drawn rows.

## The question, and the reading adopted

`--check` re-derived every family against TODAY's screens, so the ADR-1415
divergence sweep retroactively removed rows from draws that were already
preregistered. Two readings were on the table; **"the draw is history" wins**,
and not on taste:

- The **"live invariant"** reading has no legal remedy. The only ways to green
  the floor are un-registering a true divergence (manufacturing a green gate) or
  deleting rows — **30 of the 31 are held-out**, which is the blind-population
  deletion ADR-0542 forbids. A gate whose only remedies are forbidden actions is
  a trap, and it will fire again on the next honest divergence.
- The generator **already holds the other reading everywhere except `select()`**.
  `guard()` scopes R4, R5, R9, R11 and R12 to `new_entries`, and R9's own comment
  says "an earlier draw's rows are frozen, and repairing one is an amendment, not
  a regeneration". `frozen_partitions()` (ADR-0615) freezes a drawn family's
  *partition* for exactly this reason. `select()` was the inconsistency.

## What was measured

**31 drawn rows across FOUR families, not three.** The brief and the design
review both said three; the fourth is `natural-factorial-choose-and-squarefree`,
which loses `Nat.Squarefree.ext_iff` while keeping a pool of 44 — so the
ten-candidate floor never fires for it, but the alphabetical `pool[:10]` slice
shifts and `--check` would still have reported the manifest stale. **A fix aimed
only at the floor is incomplete**, and that is now a named test case.

| family | drawn rows screened out | partition | pool today |
| --- | --- | --- | --- |
| `natural-find-greatest` | 10 of 10 | held-out | 0 |
| `natural-integer-root` | 10 of 10 | held-out | 0 |
| `natural-nth-selector` | 10 of 10 | held-out | 0 |
| `natural-factorial-choose-and-squarefree` | 1 of 10 | train | 44 |

30 held-out, 1 train, all 31 `open`. Divergence rejections over the family
modules moved **42 → 97**. Zero of the 460 drawn rows has a pinned statement that
no longer matches the inventory.

**All 31 are genuinely unclosable as mirrors, not merely hard**, and per family
the answer is the same. Every one of the five registry entries is
`class: codomain` or `class: definitional`, so the pinned statement is a
different proposition from anything we could close. `natural-find-greatest` at
pool 0 differs from the one-row family only in degree.

**ADR-0542's amendment mechanism does NOT cover this.** `amendments()` is keyed
by family and carries `from`/`to` *partitions*; it repairs a family whose blind
value was *spent*. Nothing here was spent. Its *principle* decides the ADR; its
*mechanism* is the wrong instrument.

## The fix

`drawn_freeze()` freezes a drawn family's MEMBERSHIP by the same trust route
`frozen_partitions()` uses for its PARTITION — the manifest believed only against
its own `extension_sha256`. **Content is not frozen**: every row is rebuilt from
the pinned inventory by the same `entry_for()` the fresh path uses and must agree
on all 15 pinned-source fields, so F1 (row gone), F2 (module remapped), F3
(statement or derived field moved) and F4 (wrong row count) still refuse.
`partition` and `route_hypotheses` are re-stamped, which is what keeps an
ADR-0542 amendment able to move a frozen family.

The thinning is **published, not discarded**: a `historical_draw_screen_drift`
block lists all 31 rows with counts, and every gate run prints `screen_drift=31`.
It sits outside `entries`, so no drawn row changes.

## The regression control, and that it fails without the fix

In-suite (`HistoricalDrawTests`, hermetic): register a NEW correct divergence
that screens out every candidate of an already-drawn family, assert the
re-derived entries are identical and the drift reports all ten. Its twin neuters
`drawn_freeze` and asserts the identical inputs **raise**.

Live, against the real registry and the real 460-row manifest, with a plausible
new entry for `Nat.fib` (ADR-0840's real divergence):

    drawn rows the NEW entry newly blocks: 10   natural-fibonacci-basic  development
    WITH the freeze:    select() ok, entries identical to committed = True
    drift 31 -> 41, delta 10 (expected 10)
    WITHOUT the freeze: RefillError -- family 'natural-fibonacci-basic' yields
                        0 screened candidates, fewer than the 10 the refill takes

## Zero-diff over all 460 drawn rows

    entries before=460 after=460
    entries list byte-identical: True      fact_id sets identical: True
    rows differing in ANY field: 0         rows changing partition: 0
    development 170 / held-out 170 / train 120, unchanged
    negative control (one partition flipped in a copy) detected: True
    top-level keys changed: coverage, extension_sha256,
                            historical_draw_screen_drift, screens

## Gate status

| gate | exit | note |
| --- | --- | --- |
| `gen-autogenesis-nursery-refill.py --check` | **0** | was 1; `screen_drift=31` |
| `check-autogenesis-holdout-isolation.py` | 0 | `held_out=186 settled=0 PASS` |
| `validate-facts.py` | 0 | |
| `check-merge-hygiene.sh` | 0 | |
| `check-control-registration.sh` | 0 | 51 controls, 0 orphans |
| `mutation_controls.py --check-anchors` | 0 | 57 suites, 634 anchors, 0 stale |
| `check-autogenesis-nursery.py` | **1** | **PRE-EXISTING**, partition leak over `depends_on` components. Output byte-identical before and after this lane's change. |
| `check-dispatchable-frontier.py` | **1** | **PRE-EXISTING**, G7 queue-below-floor (2 dispatchable, floor 10). Output byte-identical before and after. |
| `check-generated-artifact-ownership.py` | **1** | **PRE-EXISTING**, two multi-writer artifacts, neither touched here; this lane's diff adds zero mentions of either. |
| `test_check_autogenesis_holdout_isolation.py` | **1** | **PRE-EXISTING**, a stale `held_out=146` pin against a live 186. |
| `test_check_autogenesis_nursery.py` | **1** | **PRE-EXISTING**, the same partition leak. |

Each red was re-run against the pre-fix manifest and failed identically, which is
how they are attributed rather than assumed.

Mutation suite `nursery-refill-historical-draw`: **7 anchors, 7 killed.** Six kill
exactly one test; the seventh deletes the freeze itself and kills six, which is
the whole feature rather than a shadowing problem.

## What was NOT done, and is a hypothesis rather than a measurement

The 30 unclosable held-out rows stay in the population as dead weight, correctly
classified and undispatchable. A retire-and-replace amendment ledger would be the
principled way to reclaim them; it is deliberately not built here, because the
right time to design one is when someone has a reason to run it, not while
repairing a red gate.

## Landed changes

| commit | what |
| --- | --- |
| `21ec9d103` | ADR-1445, analysis only |
| `306470083` | the fix: `drawn_freeze`, `entry_for`, F1–F4, `screen_drift`, regenerated manifest |
| `1905630f2` | `HistoricalDrawTests` + mutation suite `nursery-refill-historical-draw` |
