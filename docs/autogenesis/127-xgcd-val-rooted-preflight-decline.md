# Rooted xgcd projection preflight decline

Date: 2026-08-21

## Result

Execution did not start. A full `git status` on the pinned Mathlib checkout
found three pre-existing untracked autogenesis sources, while the preregistered
plan required zero status entries. The planned xgcd source, olean, and ilean
names were all absent.

Only the three paths, sizes, modes, and SHA-256 identities were recorded. Their
contents were not opened, changed, or removed. The earlier `-uno` fingerprint
had hidden them; this preflight corrects that evidence without claiming the
checkout is clean.

No source copy, compilation, export, importer read, theorem submission, or
ledger mutation occurred.

## Correct next boundary

The next plan may bind these exact three entries as an unchanged baseline. It
must require the same ordered path/size/mode/hash set both before our copy and
after removal of only our three exact temporary files. Any change in that
baseline fails closed.

## Durable evidence

The immutable preflight pack is
`/nas3/data/axeyum/autogenesis/reference-packs/9f135d4f0-xgcd-val-rooted-v1/`.
Its mode-`0444` manifest has SHA-256
`33ae1f917c4156741b408be52faeac070f99814db47275f2ca521b7ff665f788`;
the directory is mode `0555`.

## Verification

```sh
python3 scripts/check-autogenesis-xgcd-val-rooted-reconstruction-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_xgcd_val_rooted_reconstruction_result
```
