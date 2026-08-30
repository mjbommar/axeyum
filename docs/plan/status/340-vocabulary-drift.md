# Lane 340 — vocabulary drift (S4)

<!-- plan-section: lane-status -->

## Status

DONE. `check-dispatchable-frontier.py` is green; the statable vocabulary is now
derived rather than hand-maintained (ADR-0624).

## What the vocabulary decides

`artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` is the positive
screen for *statable in this kernel*:

    admissible = env      2,207 names read from kernel.environment()
               | bridge   70 constants of SETTLED ml430 mirrors, minus env

A candidate passes iff every Lean constant in its pinned `type_repr` is
admissible. It rejects 5,399 of the 9,729-record pinned pool, so it is not
vacuous.

**It has no per-row boolean `settled` flag**, despite the gate docstring's
wording. `settled` is a LIST of `{source_name, constants}` rows, and membership
is what promotes a row's constants into `bridge`.

## Nothing in the artifact was a free choice

S2 bounds `bridge` from below (every entry must be witnessed), S3 bounds it from
above (every settled row must be admissible) — together they pin it to ONE
value. S4 pins the row set to the ledger both ways. Verified on the committed
file: `bridge == witnessed − env` exactly, 70/70; and each row's `constants`
re-derive from the pinned inventory's `type_repr`, **162/162**.

The one field no gate touches is a row's `constants` — and that is the field
that matters. A hand-appended row with invented constants passes S2, S3 and S4
whenever another row redundantly witnesses them.

## The 9: all new rows, zero corrected flags

All nine are `proved`; nothing was listed-but-not-settled, so the drift was
entirely one-directional.

    Nat.clog_mono_right   Nat.clog_monotone   Nat.clog_one_left
    Nat.clog_one_right    Nat.clog_pos        Nat.log_mono_right
    Nat.log_monotone      Nat.log_one_left    Nat.log_one_right

**The repair did not widen the screen**, which is the measurement that matters:

    rows    162 -> 171    0 removed, 0 CHANGED, 9 added
    bridge   70 ->  70    0 added, 0 removed

`Nat.clog` / `Nat.log` are in the ENVIRONMENT, not the bridge — the pool grew
because the kernel DECLARED them, exactly ADR-0619's rule.

Confirmed downstream: `propose-nursery-refill.py`'s R2 fired on the changed
digest, and re-measuring changed **exactly one leaf** of the headroom snapshot
(`/input_digests/vocabulary`). All 5,399 / 2,235 / 15 counts identical.

## Holdout gate

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1107|settled=0|references=0|verdict=PASS

Identical to the pre-change baseline except `files_scanned` 1106 -> 1107 (the
new constants cache). No held-out row was touched; the artifact is keyed by
Mathlib `source_name` and never by `fact_id`.

## What was built so this does not recur

Detail moved to [`../notes/340-vocabulary-drift.md`](../notes/340-vocabulary-drift.md).

