# ADR-0624: A fully-constrained artifact is generated, not maintained

Status: accepted
Date: 2026-08-30
Index-summary: S2/S3/S4 pin every field of the statable vocabulary to one value, so it is derived by a generator; repairing the 9-row drift changed the bridge by ZERO constants, and a constants cache keeps the routine repair runnable off-NAS

Related: ADR-0619 (the queue refills from the kernel, not from the bridge),
ADR-0542 (held-out isolation), ADR-0615 (evaluation envelope), ADR-0601
(three producers, one trust anchor)

## Context

`artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` is the positive
screen deciding which Mathlib propositions are *statable in this kernel*. Four
scripts read it — `check-dispatchable-frontier.py`,
`check-autogenesis-holdout-isolation.py`, `gen-autogenesis-nursery-refill.py`,
`propose-nursery-refill.py` — and **none generated it**. It was hand-maintained.

On 2026-08-30 it went red. Nine settled `Nat.clog_*` / `Nat.log_*` mirrors had
no row in it at all, and `check-dispatchable-frontier.py`'s S4 fired:

    FAIL: S4 vocabulary-status-drift: 9 settled mirror(s) are missing from the
    vocabulary (Nat.clog_mono_right, Nat.clog_monotone, Nat.clog_one_left), so
    the false-positive control would run against a narrower population than the
    ledger has.

This is the flywheel outrunning its own bookkeeping, and it recurs by
construction: every batch of closed mirrors reddens it, and every repair was a
hand edit to a file four gates trust.

## The finding: nothing in the artifact was ever a free choice

Measured against the committed file before anything was changed.

`check-dispatchable-frontier.py`'s guards constrain the artifact from both
directions at once, and the two bounds meet:

- **S2** requires every `bridge` constant to be witnessed by a settled row and
  absent from `env` — so `bridge ⊆ witnessed − env`.
- **S3**, the false-positive control, requires every settled row's constants to
  be admissible — so `witnessed − env ⊆ bridge`.
- Together: **`bridge` has exactly one legal value.** Confirmed on the
  committed file, 70 of 70 constants, zero either way.
- **S4** pins the row SET to the fact ledger in both directions.

The only field no gate touches is a row's `constants` list, and that is
precisely the field derived from the pinned Mathlib inventory's `type_repr`.
Re-deriving it reproduced **162 of 162 rows exactly**.

So the artifact is 100% determined by (fact ledger, catalog, environment
snapshot, pinned inventory), and it was being maintained by hand for a value
that is entirely computed. That is the whole reason it drifted.

**And the one unconstrained field is the one that matters.** A row's constants
being unchecked is not a gap in bookkeeping, it is a soundness-shaped hole in
the screen: a hand-appended row with *invented* constants passes S2, S3 and S4
whenever another row redundantly witnesses them, because **no gate compares a
row's constants against the source**. A narrowed constants list makes the
false-positive control easier to satisfy — the same class of weakening S4
explicitly guards against for a *dropped row*, arriving through a door nobody
had shut.

## The repair did not widen the screen, and that is the load-bearing measurement

The reasonable worry about automating this is that regenerating after a closure
silently relaxes admissibility. It does not, and the numbers say so:

| | before | after |
| --- | --- | --- |
| settled rows | 162 | 171 |
| rows **changed** | — | **0** |
| rows removed | — | **0** |
| `bridge` constants | 70 | **70** |
| bridge added / removed | — | **0 / 0** |

Every constant the nine new rows name was already admissible.
`Nat.clog` and `Nat.log` are in the **environment** — the kernel declares them,
because we proved the theorems — not in the bridge. That is ADR-0619's rule
observed rather than asserted: *the pool grows by DECLARING constants, not by
widening the screen.*

Independently confirmed downstream. `propose-nursery-refill.py`'s R2 correctly
fired on the changed vocabulary digest; re-measuring changed **exactly one leaf**
of the headroom snapshot:

    /input_digests/vocabulary  e06ad2f216ea… -> 016287da2e49…

Every measured number is identical — 5,399 not-statable-here, 2,235 survivors
across 89 modules, 15 ready families with the same per-module counts. Adding the
nine rows changed which propositions we have CLOSED, not which are statable.

Nine needed a new row; **zero needed a corrected flag**. The artifact has no
per-row boolean at all (the gate docstring's "per-row `settled` flag" describes
list membership), and nothing was listed that the ledger does not settle. The
drift was entirely one-directional.

## Decision

1. **The artifact is derived, not maintained.**
   `scripts/gen-autogenesis-statable-vocabulary.py --write` rebuilds it from the
   ledger, the catalog, the environment snapshot and a constants cache. The
   derivation is unchanged from the one the artifact already documented; only
   the authorship moves.

2. **The screen is not widened, and this generator cannot widen it.** ADR-0619's
   decision 1 stands verbatim: `env` is read from the kernel and `bridge` is
   derived from closures, never asserted. A row's constants come from the pinned
   inventory, so closing a mirror admits the constants of a proposition we
   *proved*; it never admits a constant on the strength of an assertion.

3. **The routine repair must be runnable without `/nas3`.** The inventory is a
   39 MB NDJSON on a share that is not mounted fleet-wide, and *a repair nobody
   can run is how the file drifted*. So the constants of every CATALOGUED
   proposition — settled and open alike — are snapshotted into
   `artifacts/autogenesis/mathlib-statement-constants-v1.json`, digest-bound to
   the pinned inventory. Closing a mirror then needs only `--write`.
   `--refresh-cache` is the only NAS-dependent mode, needed only for a genuinely
   new catalogued proposition (a nursery refill draw), and `--write` **FAILS
   naming it** rather than emitting a row it could not derive.

4. **The new checker does not re-implement S4.** S4 already fails on drift in
   both directions and duplicating it would buy a second thing to keep in sync.
   `--check` covers what no existing gate reads:

   - **V1** the rows must hash to the recorded `row_digest` — this is what makes
     the generator the only way a row gets in, and it closes the fabricated-
     constants hole above.
   - **V2** the `coverage` block must agree with the artifact's own contents. It
     was **stale on the committed file** when this was written
     (`open_propositions` read 40 against a real 31) and nothing noticed,
     because no gate read it.
   - **V3** the source pin must equal the generator's compiled-in pins.
   - **V4** `environment_snapshot` must name a readable file inside the
     repository.

5. **S4's two directions carry different remedies.** A gate that fails on every
   landed batch with a manual repair is a gate people edit to make green, so the
   MISSING direction now names `--write` and says why regenerating cannot widen
   the screen, while the EXTRA direction says explicitly that regenerating
   cannot produce such a row and to investigate first. Messages only; the logic
   is untouched and the gate's 35 controls pass unchanged.

## What was rejected

**A narrower gate alone**, distinguishing drift from widening without a
generator. It makes the failure legible and leaves the repair manual — a human
still hand-writes rows with hand-copied constants, which is exactly the
unguarded field. It fixes the confusion, not the risk.

**An enforced rule about when a row may be added.** This is the status quo: the
artifact's own `derivation` string *is* that rule, stated in prose, and it is
what drifted. A rule requiring a human to run a procedure correctly, every time,
is the thing this repository has repeatedly measured as failing.

**Deriving constants from the fact ledger's `formal.statement`.** The facts
carry the Lean *surface* spelling, not the elaborated constant list;
reconstructing one from the other is re-implementing elaboration. Checked, and
the tracked alternative does not exist either: `nursery-v2-extension.json` does
carry per-entry `constants`, but for 260 **open** candidates with **zero**
overlap with the settled population. (That zero overlap also makes the
"disagreements: 0" between the two sources vacuous — reported here so it is not
mistaken for corroboration.)

## What V1 does not do

`row_digest` binds the rows to what `--write` produced, and someone who
recomputes it by hand can defeat it. It catches carelessness, not forgery — and
carelessness is the measured failure mode; the nine rows would have been
hand-appended. The binding to Mathlib itself is `--refresh-cache` on a host with
the pinned inventory, and that is the only place the inventory's authority
enters. This is the same level of binding as `source_catalog_sha256` and
`split_policy_sha256` in `nursery-v1.json`.

## Evidence

Controls: `scripts/tests/test-gen-autogenesis-statable-vocabulary.sh`, 19 cases,
one per guard plus the boundary cases, each asserting both that its own guard
fired and that no other did.

The suite found a real defect in V4 on its first run: `ROOT / "/etc/hostname"`
DISCARDS the left operand in pathlib, so the first draft's
`(ROOT / named).is_file()` resolved outside the repository and returned PASS.

Mutation testing, all eight mutants, kill sets as measured. Each guard deleted —
the four kill sets are **disjoint**, and none touches the false-positive control
or the boundary cases:

| mutant | cases killed |
| --- | --- |
| `V1-deleted` | 3 (all `V1-*`) |
| `V2-deleted` | 6 (all `V2-*`) |
| `V3-deleted` | 2 (all `V3-*`) |
| `V4-deleted` | 2 (all `V4-*`) |

This is *exactly one guard* dies, not *exactly one test*: several cases per
guard is deliberate (one per coverage counter, one per pin field), and it is
stronger, not weaker.

Each guard weakened to its plausible wrong version:

| mutant | cases killed |
| --- | --- |
| `V2-weakened-to-key-count` | 5 — the value cases; the missing-block case correctly survives, since a popped key changes the length |
| `V3-weakened-to-commit-only` | 2 |
| `V4-weakened-to-existence-only` | 1 — exactly the absolute-path case |
| `V1-weakened-to-names-only` | 13 — **not an informative result**, reported as measured: changing the hash function invalidates the committed digest, so V1 fires on the healthy tree and the false-positive control dies with everything downstream. What it does show is that case 0 is what catches a digest-function change. |

**One survivor was found and resolved by deleting code, not by adding a test.**
Weakening V4's `is_absolute()` test killed nothing, because `is_relative_to`
already rejects the escape on its own — the branch was unreachable. Removed; a
branch no test can kill is dead weight, and keeping it would have left a
permanent unexplained survivor.

Gate lines at the close:

    check-dispatchable-frontier.py             exit 0
    test-dispatchable-frontier.sh              35/35 pass (unchanged)
    gen-autogenesis-statable-vocabulary.py     rows=171|bridge=70|cached=202|PASS
    test-gen-autogenesis-statable-vocabulary   cases=19|failures=0|PASS
    check-autogenesis-holdout-isolation.py     held_out=116|settled=0|references=0|PASS
    propose-nursery-refill.py                  15 ready families, exit 0
    check-aggregate-scope.sh                   407/463, 66 recorded, PASS
    check-control-registration.sh              controls=31|orphans=0|py_orphans=0

No held-out row was touched: the artifact is keyed by Mathlib `source_name` and
never by `fact_id`, deliberately, and the holdout gate reports the same
`held_out=116|settled=0|references=0` it did before this work.
