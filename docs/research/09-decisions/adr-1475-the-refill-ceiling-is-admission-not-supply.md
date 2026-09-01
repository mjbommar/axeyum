# ADR-1475: The refill ceiling is admission, not supply — 1,443 dispatchable rows are already screened and structurally unreachable

Date: 2026-09-01
Status: Proposed
Lane: `refill-economics`

Index-summary: Measured the refill economics with the real machinery
(`select()`, `guard()`, `screen_family()`, `assert_draw_lawful()`,
`check-dispatchable-frontier.py`), never `propose-nursery-refill.py`. Three
findings. (1) Supply is not running out and the draw cannot reach it: 2,470
inventory rows pass every screen, 500 have been admitted in 11 draws, and
1,443 genuinely-new rows sit in already-drawn DEVELOPMENT/TRAIN families,
dispatchable at zero held-out cost, unreachable because `PER_FAMILY` is a cap
that `F4` makes unraisable. (2) New-family supply IS exhausted: 79 screened
rows in 23 undrawn modules; of 1,011 minimal bundles reaching ten rows only 17
are R11-clean held-out, 16 of them share one module, and the only disjoint
pair uses `Mathlib.Data.Nat.Count`, which `assert_draw_lawful` refuses
(ADR-1100). **No draw 19 can satisfy R5 from the current vocabulary.** (3) No
held-out row has ever been settled — 206 rows, 20 families, all `open`; all
seven ADR-0542 amendments are contamination repairs. Recommends a
dispatchable top-up into drawn dev/train families, and refuses to thin the
held-out fraction.

Index-status: Proposed

## Context

`check-dispatchable-frontier.py` sat at 2 against a floor of 10 for most of
2026-09-01. Four lanes in sequence restored it: one refused a contaminated
draw, one opened a family, one fixed three tooling blind spots, one authored
draw 18, which took the frontier to 22 (ADR-1465). Two sonnet lanes then closed
thirteen mirrors in one round and it fell below floor again within about an
hour.

That ratio — four lanes to author a draw, one round of two lanes to consume
over half of it — had never been measured. This ADR measures it.

Everything below is read-only. Nothing under `artifacts/` was written; see
"Zero-write proof".

## Method

`propose-nursery-refill.py` is deliberately not consulted: four independent
blind spots were found in it on 2026-09-01, each overstating readiness. Every
number comes from the machinery that actually gates a draw:

* `scripts/gen-autogenesis-nursery-refill.py` — `read_vocabulary`,
  `admissible`, `blockers_for`, `HYGIENE`, `CONST_RE`, `select`, `guard`,
  `drawn_freeze`, `assign_partitions`, imported rather than reimplemented.
* `scripts/check-holdout-adjacency.py` — `screen_family`, `assert_draw_lawful`,
  `resolve_families`, `load_refusals`.
* `scripts/check-dispatchable-frontier.py` — run as-is.

Reproduce the supply and per-draw halves with
`python3 scripts/measure-refill-economics.py`.

`python3 scripts/gen-autogenesis-nursery-refill.py --check` → exit 0,
`entries=500 … development=180|held-out=190|train=130|combined=714|
attested=409|unattested=305|screen_drift=31`.

## Finding 1 — supply is not running out; the draw cannot reach it

Applying `select()`'s own screens to all 9,729 pinned inventory records:

| outcome | rows |
| --- | ---: |
| screened-ok | **2,470** |
| not-statable-here | 4,830 |
| hygienic-or-generated | 2,094 |
| already-catalogued | 202 |
| divergence-registry | 118 |
| held-out-construction | 15 |

Eleven draws have admitted **500** of those 2,470. Of the 1,970 that remain
after subtracting drawn and catalogued rows, **1,922 sit inside a module
already bound to one of the 50 drawn families**, and only **79** sit in a
module no family has drawn.

Split the 1,922 by the partition of the family that owns the module:

    development 861   held-out 333   train 728

so **1,589 are dispatchable rows requiring no further held-out spend at all**,
and 1,443 of those have a Mathlib name that is not yet a kernel declaration —
genuinely new work. Twenty of the 31 dispatchable families each carry ten or
more such rows; the largest are `natural-basic-arithmetic` (381),
`integer-order` (278), `integer-gcd-algorithm` (102),
`integer-basic-arithmetic` (100).

**The residual is far less contaminated than what a draw admits.** Of the 310
dispatchable rows the eleven draws did admit, **202 (65.2%)** already had their
Mathlib name in the kernel environment; of the 1,589 residual rows, **146
(9.2%)** do. Alphabetically-first ten rows are the basic lemmas the prelude has
already covered. Admitting more rows per family would admit *more* new work per
row, not less. (Control: 0 of the 190 drawn held-out rows have their name in
the environment, which is R9 working.)

### Why the residual is unreachable

`select()` does not re-select a drawn family at all:

    recorded = drawn.get(family)
    if recorded is not None:
        entries.extend(frozen_family_entries(...))
        continue
    ...
    for cand in pool[:PER_FAMILY]:

`PER_FAMILY = 10` is a floor *and* a cap, and `frozen_family_entries` adds a
third guard:

    if len(recorded) != PER_FAMILY:
        raise RefillError(f"F4 drawn family {family!r} records {len(recorded)} rows, ...")

Measured directly, in memory, writing nothing:

* **E2** — `PER_FAMILY = 20` with the freeze intact: the generator does not
  merely ignore the change, it **refuses**:
  `F4 drawn family 'descent-and-well-ordering' records 10 rows, not the 20 a
  draw takes; the manifest has been edited`.
* **E3** — remove `integer-order` from the freeze and re-select at
  `PER_FAMILY = 10`: it returns the identical ten rows
  (`identical_to_recorded=True`, delta 0), while 293 further screened rows sit
  in its module. Re-selection is idempotent; the pool is deep; the cap is what
  binds.

So `PER_FAMILY` is not a tunable. It is wired as "every family has exactly ten
rows, forever."

## Finding 2 — new-family supply IS exhausted, and R5 is where it fails

The 79 undrawn rows span 23 modules. Exactly one reaches ten alone:
`Mathlib.Data.Nat.Count` (22).

Screened with the real `screen_family()` against all 62 published families:

* 1,011 minimal bundles of undrawn modules reach ten rows;
* **17** are R11-clean as held-out;
* sixteen of those seventeen contain `Mathlib.Data.Nat.Factorization.Basic`, so
  they pairwise intersect;
* every one of the **16 disjoint clean pairs** therefore pairs
  `candidate-count` with one of the other sixteen.

And `Mathlib.Data.Nat.Count` is barred:

    ASSERT|candidate-count HELD-OUT REFUSED|R11 1 new held-out family/families
    draw a module already recorded do-not-draw-held-out in
    holdout-adjacency-review-v1.json ... (ADR-1100, restated by ADR-1115)

**R5 requires two new held-out families per draw. No such pair exists.** Draw
19 cannot be assembled from the current vocabulary — not "is difficult",
cannot.

Controls, both required before believing that: rescoring all 20 committed
held-out families against the published set with each removed gives 20 scored /
0 refused (they are committed and clean), and a deliberately-contaminated
bundle built from a development family's own module
(`Batteries.Data.Nat.Bitwise.Lemmas`) is **refused** with 2 topic hits — so the
screen fires. Note also that `screen_family` alone reports `candidate-count`
**clean**: the module bar lives in `assert_draw_lawful`, and screening without
it is the blind spot ADR-1450 closed.

## Finding 3 — the held-out population has never been used

Across both manifests (716 rows, 206 held-out / 300 development / 208 train /
2 longitudinal):

| partition | open | proved |
| --- | ---: | ---: |
| held-out | **206** | **0** |
| development | 27 | 273 |
| train | 11 | 197 |

**Twenty held-out families, 206 rows, not one settled.** The development and
train columns are the positive control that the status lookup discriminates;
every manifest row has a fact file (0 missing).

All seven ADR-0542 amendments are contamination *repairs* —
`natural-gcd`, `natural-binomial`, `natural-logarithm`, `natural-divisibility`,
`natural-parity`, `fermat-numbers`, `natural-bit-decode`. None is a deliberate
evaluation.

This is **not** an argument to thin the held-out fraction, and this ADR
recommends against it (below). It is the measurement that the fraction has
bought an option that has never been exercised, and that ADR-0615's stated
reason for starting `PARTITION_CYCLE` at held-out — *"of twelve v1 families
exactly two are still open and blind"* — is over-satisfied tenfold and has not
been re-measured since.

## Finding 4 — the per-draw arithmetic, and why four families is the worst size

Eleven draws, 50 families, 500 rows:

| draw | date | families | rows | held-out | dispatchable |
| ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 2026-08-29 | 8 | 80 | 10 | 70 |
| 2 | 2026-08-29 | 4 | 40 | 20 | 20 |
| 3 | 2026-08-29 | 4 | 40 | 20 | 20 |
| 4 | 2026-08-29 | 4 | 40 | 20 | 20 |
| 5 | 2026-08-30 | 6 | 60 | 20 | 40 |
| 7 | 2026-08-30 | 4 | 40 | 10 | 30 |
| 9 | 2026-08-30 | 4 | 40 | 20 | 20 |
| 11 | 2026-08-30 | 4 | 40 | 10 | 30 |
| 15 | 2026-08-31 | 4 | 40 | 20 | 20 |
| 16 | 2026-08-31 | 4 | 40 | 20 | 20 |
| 18 | 2026-09-01 | 4 | 40 | 20 | 20 |

Totals: 500 rows, **310 dispatchable (62%)**, mean 4.55 families and **28.2
dispatchable rows per draw**. Rows are counted at effective partitions, so the
four amended families show as dispatchable; preregistered, the split was
held-out 23 / development 14 / train 13 families.

`PARTITION_CYCLE` restarts per draw (`_with_cycle`), which makes the held-out
cost a step function of draw size, not a third:

| families | held-out families | dispatchable rows | held-out fraction | R5 |
| ---: | ---: | ---: | ---: | --- |
| 3 | 1 | 20 | 33% | **fails** |
| **4** | **2** | **20** | **50%** | ok |
| 5 | 2 | 30 | 40% | ok |
| **6** | **2** | **40** | **33%** | ok |
| 7 | 3 | 40 | 43% | ok |
| 9 | 3 | 60 | 33% | ok |
| 12 | 4 | 80 | 33% | ok |

**Four is the worst size above three.** It pays 50% held-out — not the one
third the cycle suggests — and yields the same 20 dispatchable rows as a
three-family draw that R5 forbids. A six-family draw spends **exactly the same
two held-out families** and yields **twice** the dispatchable work. Draw 5 did
this and is the only draw in the table with 40 dispatchable rows from a
mechanical assignment.

## Finding 5 — the vocabulary lever routes into the same bottleneck

1,156 of the 4,830 unstatable rows are blocked by exactly one missing constant.
Greedily admitting the twelve highest-value constants — `instSubNat` (312 rows
alone), `Int.lcm`, `Int.bmod`, `Int.fmod`, `Int.fdiv`, `Int.tdiv`, `Int.tmod`,
`Int.sign`, `Int.instMonoid`, `Int.instMax`, `Int.instMin`, `GE.ge` — would
admit **810 further rows**.

**779 of them (96.2%) land in modules already bound to a drawn family**, and 31
in undrawn modules across 13 modules, none reaching ten. So extending the
vocabulary, on its own, buys almost nothing: it feeds the same frozen families.
It becomes the largest lever available only *after* a top-up route exists.

## Decision

### Recommended, in order of measured value

**1. Admit a second tranche into already-drawn development and train families.**
1,443 genuinely-new dispatchable rows, zero held-out spend, no partition moves,
no new family, no new construction, no lane needed to open anything. This is
~72 rounds of dispatchable work at the observed consumption rate of ~20 rows
per round, against a current supply of 15.

The change is three edits, all inside the generator, and none of them touches a
partition, a threshold, or a screen's decision:

* `select()` — for a family in the freeze, emit the recorded rows *and then*
  append further rows from the same screened pool, in the same inventory order,
  so recorded membership is a prefix and no drawn row moves.
* `F4` — from `len(recorded) != PER_FAMILY` to "the recorded rows are a prefix
  of the selection", which is the invariant F4 was protecting.
* `guard()` — re-scope R9, R11 and R12 from `entries whose FAMILY is not
  frozen` to `entries not in the drawn freeze`. Today a top-up would be
  entirely unguarded, because `new_entries` is family-keyed and R4/R5/R9/R11/R12
  are all inside `if new_entries:`. That is a hole a top-up would open and the
  re-scoping is what closes it.

R5 needs no change: with no new *family*, `new_entries` is empty and R4/R5 do
not fire, which is correct — a top-up adds no blind population and should not
be taxed with two families of one.

The binding limit is **R3**, and it is measured: attested 409, unattested 305,
**headroom 104 rows** before `unattested > attested`. The documented and
correct exit is to re-attest, not to raise the ceiling —
`scripts/provision-lean-import-toolchain.sh` (~5 min) then
`scripts/attest-nursery-surface.py` and `--ingest-surface-attestation`. So the
first top-up is capped at 104 rows and every subsequent one needs an attestation
run. That is a real cadence cost and it is the honest price of this
recommendation.

**2. Run a blind evaluation.** Twenty held-out families and 206 rows have been
preregistered and none has ever been scored. Every contamination incident spends
part of that population — seven so far — so its value decays whether or not it
is used. This is the missing step, and it is not a throughput change.

**3. Extend the vocabulary by the twelve constants in Finding 5** — but only
after (1) lands, since 96% of what it admits routes into frozen families.
`instSubNat` alone is worth 312 rows.

**4. Draw six families, not four, for any new-family draw.** Same two held-out
families, twice the dispatchable yield, and it restores the one-third fraction
the cycle is meant to give. Currently moot: Finding 2 shows no new-family draw
of any size can satisfy R5 from the present vocabulary, so this applies only
once (3) has landed.

### Refused

**Thinning the held-out fraction.** It would be the wrong trade and the
measurements do not support it. The right reading of Finding 3 is that the
population is unused, not that it is too large — and the fix for an unused
evaluation set is to run the evaluation. Note also that at the standard draw
size the cycle is already charging 50% rather than 33%; moving to six-family
draws *reduces* the held-out fraction to its intended third without touching
`PARTITION_CYCLE` at all. That is the honest way to recover the ratio.

**Lowering `PER_FAMILY` below ten.** No measurement supports it. Family supply
is deep — 20 of 31 dispatchable families carry ten or more further screened
rows — so a smaller family would shrink every evaluation population for no
throughput gain whatsoever. The floor is not what binds; the cap is.

**Construction batching as a way to make a draw a single-lane operation.** The
arithmetic kills it independently of lane count. Opening a family requires a
module with ten screened rows and no development/train adjacency, and Finding 2
shows the entire undrawn supply admits no disjoint held-out pair at all. Four
constructions in one lane would not change that; the vocabulary would have to
be extended first, which is recommendation (3).

## Consequences

* The four-lanes-per-draw cadence is not a discipline problem and cannot be
  fixed by dispatching better. New-family supply is exhausted at the current
  vocabulary, and the queue has been refilled eleven times from a pool whose
  reachable part was 20% of what had already passed every screen.
* Until a top-up route exists, each new-family draw is capped at whatever R11
  and the module bar permit, which is currently nothing.
* This ADR changes no code and no constant. Recommendations (1), (3) and (4)
  each need their own ADR and their own lane; (2) needs neither.

## Zero-write proof

No measurement in this lane wrote to `artifacts/`. Three checks, the last with
a negative control:

* `git status --porcelain --untracked-files=no -- artifacts/` → 0 lines.
* Re-deriving all 500 drawn rows through `select()` and comparing
  `(partition, family, source_name)` against `nursery-v2-extension.json`:
  **DIFF = 0** over 500 rows.
* **Negative control**: flipping one held-out row's partition to `train` in the
  re-derived set (`F:ml430-int-add-ediv-of-dvd-left-52ee6c5c`) makes the same
  comparison report **DIFF = 1**. A zero there would have meant the comparison
  cannot detect a flipped partition and the zero above meant nothing.
* Manifest digests, for the record:
  `nursery-v1.json` `d554201170123beae11278ca6a99a91b3f0c04076ddb867b6ded91deb3baf87c`;
  `nursery-v2-extension.json` `760bf3ff34d1ccea51ee8c329a1d56d5087aa83be44bbdf917128368c322982f`;
  `mathlib-nursery-split-policy-v1.json` `55b04bdff74260cf9a7bc579265ab44180cf57bfcce34cd9e1098d377b073b4f`.

## What argues the current cadence is already right

Recorded because a well-measured negative is worth more than an unfounded
optimization, and three things here do argue for the status quo:

* **The screens are working.** Draw 17's refusal of `Nat.count` was correct,
  the module bar now binds mechanically through `assert_draw_lawful`, R9 shows
  0 of 190 drawn held-out rows contaminated, and the known-bad control is
  refused. Nothing in this analysis found a screen that is too strict.
* **`PER_FAMILY = 10` as a floor is sound.** Ten is a small evaluation
  population already; the supply measurement gives no reason to go lower.
* **The membership freeze (ADR-1445) is right and must survive any top-up.**
  Its own justification — a divergence registered after a draw retroactively
  thins that draw's pool, measured at 31 rows — is exactly why the top-up must
  append rather than re-select. Recommendation (1) is written to preserve it.

The cadence problem is one constant used two ways (`PER_FAMILY` as floor and as
cap) and one guard scoped to families where it should be scoped to rows. It is
not the screens, not the partition rule, and not the held-out fraction.

## Did not run

* A top-up was not implemented or trialled. Recommendation (1) is an
  arithmetic case from the measured pool, not a demonstrated regeneration.
* `scripts/attest-nursery-surface.py` and the Lean provisioning script were not
  run, so the "~5 min" attestation cost is quoted from
  `scripts/provision-lean-import-toolchain.sh`'s own documented figure and not
  re-measured on this host.
* No aggregate gate (`just check`, `./scripts/check.sh`) was run; this lane adds
  one read-only script and one document.

## References

* [ADR-0542](adr-0542-held-out-partition-breach-repair.md)
* [ADR-0615](adr-0615-the-evaluation-envelope-is-per-cohort-and-a-draw-is-incremental.md)
* [ADR-0616](adr-0616-the-ceiling-counts-attestation-not-membership.md)
* [ADR-0653](adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md)
* [ADR-1445](adr-1445-a-drawn-family-is-history-and-is-not-re-screened.md)
* [ADR-1465](adr-1465-draw-18-clears-the-dispatchable-floor.md)
* `scripts/measure-refill-economics.py`
