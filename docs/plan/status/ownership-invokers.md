# Lane: ownership-invokers

## Status

**Working** — adding an `invokes` classification to
`scripts/check-generated-artifact-ownership.py`.

`scripts/check-generated-artifact-ownership.py` is red on `main`: the KNOWN
arm demands that every script naming a GUARDED artifact be classified, and
`scripts/lane-merge-land.sh` names
`artifacts/autogenesis/frontier-shape-census-v1.json` in its `GENERATED=(...)`
list. Neither existing category is honest for it. `runs` would execute a merge
script in the ownership sandbox, which is meaningless; `reads` is false because
the script writes (redirections, `git add`). The script names the artifact only
to clear a merge conflict on it and `git add` it, and then regenerates it by
invoking the OWNER, `scripts/frontier-shape-census.py`.

The third classification `invokes` closes the gap, verified BY INSPECTION of the
script's source rather than by execution: every line naming the artifact must be
a `git add`/conflict-clearing shape, and the owner's path must appear in the
script. Any other write route to the artifact (a redirection into it, a Python
`open(path, "w")`, a `cp`/`mv` onto it) fails the arm.

## Landed changes

_(none yet)_
