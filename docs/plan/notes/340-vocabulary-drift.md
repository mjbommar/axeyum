# Notes: 340-vocabulary-drift

Detail moved out of [`../status/340-vocabulary-drift.md`](../status/340-vocabulary-drift.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
