# Notes: 364-holdout-amendment-2

Detail moved out of [`../status/364-holdout-amendment-2.md`](../status/364-holdout-amendment-2.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**`fermat-numbers`, 3 of 10 rows, and the cause is the DEFINITION.**
`Nat.fermatNumber` admitted 2026-08-30 06:48:10 (`0065c83b1`); draw 7
preregistered the family at 07:09:52 (`29d51bd0b`). Twenty-one minutes.
`fermatNumber 0 = 3`, `1 = 5`, `2 = 17` are closed equations between a constant
at numerals and a numeral, so each closes by `Eq.refl` the moment the
`Definition` exists. `fermat_number_evaluates_correctly` (same commit, verified
present at that SHA by reading the blob) asserts all three by `Kernel::def_eq`
— the running demonstration that the reduction fires, not the cause of the
spend. Deleting the test would not have restored blindness.

## The evaluation-test tension — ADR-0695

CLAUDE.md requires an evaluation test for every new `Definition`; ADR-0653
requires an unblocking lane to write down none of the family's mathematics.
Both appeared to bind on `fermatNumber 0 = 3`.

**The conflict is not real.** The `Definition` is admitted before any test
runs, and from that instant every closed evaluation over it is decided. So:
the evaluation test stays mandatory and unchanged, including its discriminating
arguments — steering them away from a pool is how a `Nat.lor`-shaped absorbing-
zero defect ships — and the screen moves to the draw. All three suggested
repairs are rejected in the ADR with their costs: delaying the test leaves a
definition unverified *and does not work*; evaluating outside the pool weakens
the test where it matters and is an artifact of alphabetical selection;
draw-time screening alone is blind to a construction declared after the draw.

## Detection — the most valuable part, and one half needed no new tool

**`natural-parity` was reachable by the gate we already have, pointed at the
wrong file.** `check-autogenesis-holdout-contamination.py` read `nursery-v1.json`
alone. Of 136 pre-amendment held-out rows, **16 are in v1 and 120 in the
extension** — the detector was aimed at 12% of the population it names. Six of
the 9 rows its own existing rule surfaces are extension rows it never read, one
of them matching the admitted `Int.odd_of_mul_left`.

Its rule was also equality where it should be containment, which is the parity
case exactly (`{even, iff}` against `even_iff_mod_two_eq_zero`'s six words).
Cost measured before changing it, over the 136-row population against the
committed 2,383-name snapshot:

| rule | rows flagged | (row, name) pairs |
| --- | --- | --- |
| equality (was) | 9 | 9 |
| subset (now) | 15 | 34 |

25 extra pairs of advisory `needs-review`. Worth it at 116 rows; the number to
re-measure if the population grows is the **pair** count.

**`fermat-numbers` needed a new gate**, because no theorem inventory can see a
`Definition`. `scripts/check-holdout-closed-evaluation.py` flags any held-out
row that is a binder-free equation over numerals and already-declared
constants. Three things stop it being a checker that cannot fail: it self-tests
its classifier on every run against a pinned fixture table (today's population
is clean, so it would otherwise pass vacuously); `RealPopulationTests` runs it
against the manifests read out of git at the pre-amendment commit and requires
`violations=3` naming all three Fermat facts; and it treats a constant as
declared via a source fallback, because the snapshot goes stale **fail-open**
for this screen — which is the 21-minute window itself.

Mutation run, `copytree` scratch root, `__pycache__` cleared between iterations:

```
KILLED-BY-ONE  contamination: subset -> equality
KILLED-BY-2    contamination: read v1 only
KILLED-BY-3    closed-eval: drop the numeral-side requirement
KILLED-BY-3    closed-eval: drop the single-equation requirement
KILLED-BY-ONE  isolation: rglob -> glob
KILLED-BY-ONE  closed-eval: make self_test vacuous
```

One survivor was found and fixed: `if "=" not in text` was redundant with the
later `len(sides) != 2`. Retargeting the mutation made *that* survive, because
no realistic Mathlib statement separates it from the numeral-side guard — so
the fixture table gained `Nat.foo 0 = 1 = 1`, deliberately not Mathlib syntax,
and the guard is now killed. Nothing unkillable ships.

## The out-of-scan references

Re-derived with a positive control in the same command: **18** distinct
held-out ids appear outside the gate's scan set, not eight.

- **Widening to `crates/`/`docs/`/`scripts/`/`PLAN.md`: refused.** 13 of the 18
  are in `docs/plan/generated/autogenesis-baseline.json`, whose edges come from
  the facts' own preregistered `depends_on` — it republishes population data.
  `nat_prelude/sqrt.rs:55` is an incidental mention: the row is the *quantified*
  `∀ n, sqrt (n*n) = n`, what landed is `sqrt 0 = 0` / `sqrt 1 = 1`, and the
  comment explicitly declines the general theorem. The rest is bookkeeping.
  Decisively, a widened scan fires on the audit document that found the
  contamination and on the ADR recording the repair — **a gate that reds when
  someone writes down a discovered leak punishes disclosure.**
- **One widening taken, and it is not a judgement call:** the glob was
  non-recursive, so `artifacts/autogenesis/producer-contracts/` (2 files) was
  unscanned. A producer contract is prospective dispatch, which is exactly the
  breach. `rglob`; `files_scanned` 1107 → 1109.

## `check-fast.sh`, against a measured baseline

Run at the merge base (`fab966b4c`, in a detached worktree) and in this lane,
and the failure SETS diffed — not my own diff read for plausibility.

| run | failed steps |
| --- | --- |
| merge base | 28 |
| this lane, first run | 29 |
| this lane, final | **27 — baseline minus `dispatchable-frontier`** |

Two failures were mine and are fixed. Neither was visible from the diff:

- `autogenesis-mathlib-nursery-split` — `nursery-v1.json` carries a copy of the
  ADR-0542 ledger, so two new amendments made it stale. Regenerated.
- `aggregate-scope` — the new gate was in the `justfile` only, so `check.sh`
  would not have run it. Added to both rather than recorded as an accepted
  divergence.

Then a *third* set appeared that was failing in neither earlier run —
`autogenesis-concept-coverage{,-content,-fresh}` — because the `nursery-v1.json`
regeneration moved a digest the concept-coverage projection pins. **A
propagation fix creates the next stale artifact one hop downstream**, so the
comparison has to be repeated after each fix rather than reasoned about. One
line, `nursery_sha256`.

And one baseline failure this lane REMOVED, which is worth more than either
fix: **`check-dispatchable-frontier.py` is green at 21 dispatchable.** ADR-0653
said that gate "stays RED at 6 against a floor of 10, and no draw can clear
it", because R5 refuses any family set that does not add two held-out families.
It was cleared by an *amendment* instead — the 20 released rows are ordinary
development work now, which is precisely ADR-0542's argument for moving a
family rather than deleting it.

## Pre-existing red on `main`, not from this lane

Each measured by restoring my files to HEAD and re-running.

- `check-mirror-statement-fidelity.py` — FAIL, 11 violations in
  `F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7` and
  `F:ml430-nat-totient-dvd-of-dvd-9622e44a`, whose `formal.statement` carries
  kernel rendering. The audit called this in-flight lane work; it is on `main`
  now. Same two facts make
  `gen-autogenesis-nursery-refill.py --check` exit 1 with
  `PREREGISTRATION_DRIFT` (the generator itself runs and writes correctly).
- `check-autogenesis-nursery.py` — exit 1, "declared dependency component
  crosses evaluation partitions". A v1-only check over a file this lane does
  not touch.
- `check-control-registration.sh` — 4 errors for hyphenated
  `scripts/tests/check-*-numerics.py` files, unreachable by both discovery
  routes. `orphans=0|py_orphans=0`, so this lane's controls are registered.

## Landed

| commit | what |
| --- | --- |
| `7a1e918f9` | the two ADR-0542 amendments; held-out 136 → 116 |
| `b9cb7bbf9` | both contamination shapes made detectable; 18 new controls |
| `c07c40928` | mutation fix (one unkillable guard) + `just check` registration |
| `e489a2539` | ADR-0695 |
| `0f6207a91` | `rglob` for artifact subdirectories; the wider scan refused |
| `3e8771650` | propagate into `nursery-v1.json` and `check.sh` |
| `e49b4c315` | re-pin the concept-coverage projection |

## Not done

- Audit item 7 (`nursery-v2-extension.json` still declares itself
  `preregistered-before-target-outcomes` after amendment;
  `gen-autogenesis-nursery-refill.py:1407` hard-codes the pristine string) is
  untouched. It is a one-line generator change but it belongs with whoever owns
  that generator's `--check` contract, and this lane's edits to the manifest go
  through the ledger rather than around it.
- Audit item 8 (the R9 environment snapshot is stale and fail-OPEN) is
  mitigated only inside the new gate, via its source fallback. R9 itself still
  reads the stale snapshot.
