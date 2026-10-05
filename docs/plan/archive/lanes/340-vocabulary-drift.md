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

`scripts/gen-autogenesis-statable-vocabulary.py`:

    --refresh-cache   needs /nas3     rebuild the constants cache
    --write           tree only       rebuild the vocabulary from the cache
    --check (default) tree only       V1-V4 over the committed artifact

The cache (`artifacts/autogenesis/mathlib-statement-constants-v1.json`, 202
propositions, digest-bound to the pinned inventory) is what makes the ROUTINE
repair runnable off-NAS — a repair nobody can run is how the file drifted. Only
a nursery refill draw needs `--refresh-cache`, and `--write` fails naming it
rather than emitting a row it could not derive.

`--check` deliberately does not re-implement S4. V1 row digest, V2 coverage
block (**stale on the committed file**, `open_propositions` 40 vs a real 31, and
unread by any gate), V3 source pin, V4 environment-snapshot pointer.

S4's messages now split the two directions: MISSING names `--write` as the
routine remedy; EXTRA says regenerating cannot produce such a row and to
investigate. Logic untouched, 35/35 frontier controls unchanged.

## Mutation kill sets, as measured

Each guard deleted — four **disjoint** kill sets, none touching the
false-positive control:

| mutant | killed |
| --- | --- |
| `V1-deleted` | 3 (all `V1-*`) |
| `V2-deleted` | 6 (all `V2-*`) |
| `V3-deleted` | 2 (all `V3-*`) |
| `V4-deleted` | 2 (all `V4-*`) |

Weakened: `V2-weakened-to-key-count` 5, `V3-weakened-to-commit-only` 2,
`V4-weakened-to-existence-only` 1 (exactly its case).
`V1-weakened-to-names-only` killed 13 and is **not informative** — changing the
hash invalidates the committed digest, so the false-positive control dies with
everything downstream; reported as measured.

**One survivor, resolved by deleting code.** V4's `is_absolute()` test could not
be killed because `is_relative_to` already rejects the escape. The branch was
unreachable; removed rather than excused.

The suite itself found a real V4 defect on its first run: `ROOT / "/etc/foo"`
discards the left operand in pathlib, so the first draft returned PASS for an
artifact naming `/etc/hostname` as its environment snapshot.

## Landed

| commit | what |
| --- | --- |
| `ba34fbb16` | early commit, S4 triage |
| `5f89896dc` | generator + cache + repaired artifact |
| `a8e6581ca` | remeasured refill headroom |
| `b02b0463e` | 19-case controls suite; V4 defect fixed |
| `000e89ee8` | V4 dead branch removed (mutation survivor) |
| `27232aae5` | registration in check.sh + justfile; S4 remedy messages |

## Next

Nothing blocking. The next lane to close a batch of `ml430` mirrors runs
`python3 scripts/gen-autogenesis-statable-vocabulary.py --write` and commits the
artifact; S4 now tells them so by name.
