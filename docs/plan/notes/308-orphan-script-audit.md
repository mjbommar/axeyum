# Notes: 308-orphan-script-audit

Detail moved out of [`../status/308-orphan-script-audit.md`](../status/308-orphan-script-audit.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| source | orphans (of 504/503) | method |
| --- | --- | --- |
| coordinator's cruder query | 398 | not re-derived here, but see the bug below — almost certainly the same one |
| this lane, first pass | 387 | full graph, basename substring only |
| the 2026-08-29 retrospective | 352 (of 503) | not re-derived independently; this lane's fixed pass reproduces it |
| **this lane, fixed** | **349** | full graph + dotted-module matching |

**The bug that separated 387 from 349, and almost certainly explains 398
too.** `scripts/check.sh` invokes most Python controls as
`python3 -m unittest scripts.tests.test_X` — dotted module form, no `.py`, no
`/`. That string does not contain the substring `test_X.py`, so a census that
matches only literal basenames concludes `scripts/tests/test_X.py` is
un-invoked, which then breaks the chain to every `check-*.py` subject that
control in turn references (most controls literally read/exec their subject
script). Fixed by also matching `scripts.tests.NAME` for any
`scripts/tests/NAME.py` file — the same dual-form logic
`check-control-registration.sh` already uses for exactly this reason (its own
header notes discovering the same gap on 2026-08-27: "counting only the
module form reported 217 orphans against a true 199"). Confirmed with a
fix-validation control: `check-theorem-inventory-completeness.py` — orphan
before the fix, live after, because its own control uses the dotted form —
must land in the live set post-fix, and does.

Applying the same fix moved this lane from 387 -> 349 orphans (155 live).
That is a 38-script swing from ONE bug, comparable in size to the 46-script
gap between the retrospective's 352 and the coordinator's 398 — strong
circumstantial evidence the "398" query has the identical blind spot, though
this was not independently re-derived (nobody handed over that query's exact
form to check).

**Verdict: the retrospective's 352 was right (to within the 1-2 file corpus
drift and edge cases expected over 8+ days); trust the fixed method (349) as
current.**

## Classification of the 349 orphans

| group | count | disposition |
| --- | --- | --- |
| `check-autogenesis-*` (the 2026-08-21/22 capsule burst) | 346 | **archived** |
| general-purpose, well-documented, never wired up | 3 | **registered** |

**346 `check-autogenesis-*` scripts.** 333 of the 349 orphans (95%) have their
last commit on exactly 2026-08-21 or 2026-08-22. Read a random sample of 12
plus a full-repo grep for each (positive control: the grep finds their
matching `docs/autogenesis/*.md` plan doc and `artifacts/autogenesis/*.json`
input every time, so the method isn't silently missing hits): each is a
single-use verifier, typically under 2 KB, hard-coding a SHA-256 of one
capsule's artifact and — in the sampled files — a `pathlib.Path` under a
host-local `/nas3/...` mount that does not exist in this checkout. Not a
reusable gate by any reading; this is the "operation registry where every
entry names one target is a dispatch table, not a producer" pattern CLAUDE.md
already documents for the same era. 92 of the 346 have a matching
`scripts/tests/test_check_autogenesis_*.py` control that ran only via
`run-python-controls.py`'s catch-all (verified: none of the 92 is separately
named by a root — if it were, its subject would already be live, not
orphan).

**3 genuinely useful, never-wired-up scripts** (the "interesting group" the
brief called out) — all mentioned only in a doc, never in a gate:
  - `check-shared-index.sh` — detects the staged-revert-of-landed-work bug
    CLAUDE.md's multi-agent section spends several incidents on.
  - `check-sos-negative-controls.sh` — 36 assertions over 21 fixtures proving
    the SOS certificate checker actually rejects false certificates. Exactly
    the "a checker that cannot fail is worse than no checker" case this repo
    audits elsewhere, just never itself gated.
  - `check-evidence-portability.sh` — re-validates CERTIFIED certificates
    against a fresh parse; guards the exact defect class that shipped once
    and had to be reverted (2026-08-17, per its own header).

All three were run standalone before registering (`check-shared-index.sh`:
instant, OK; `check-sos-negative-controls.sh`: ~1s, 36/36 passed;
`check-evidence-portability.sh --limit 5`: needs `smtcomp_cli` built first,
~a few minutes cold, then OK) and exited 0.

## What landed

- **Archived** (git mv, history preserved) 346 `check-autogenesis-*.{sh,py}`
  subjects to `scripts/archive/`, and their 92 matching
  `scripts/tests/test_check_autogenesis_*.py` controls to
  `scripts/archive/tests/`. Moving the controls out of `scripts/tests/` is
  what actually stops them running — `run-python-controls.py`'s catch-all
  globs `scripts/tests/test_*.py`, so they fall out of discovery the moment
  they leave that directory.
- **Registered** the 3 useful orphans as new steps: `scripts/check.sh` gained
  three `step` lines right before the step-count summary; the `justfile`
  gained matching recipes (`shared-index`, `sos-negative-controls`,
  `evidence-portability`) wired into the `check:` dependency list.
- **Repaired** 3 `scripts/control-optout.tsv` entries that named controls now
  living under `scripts/archive/tests/` — `check-control-registration.sh`
  correctly flagged them as "names a file that no longer exists" the moment
  the archival landed. Removed the 3 entries (and the now-empty "(d)" section
  header they were the sole occupant of), lowered `OPTOUT_CEILING` 18 -> 15
  to match (a falling count is a result per that gate's own G6 comment), and
  fixed a stale "19 suites" count in the file's header.
- **Left everything else alone.** No non-autogenesis, non-listed script was
  touched. The 3 registrations are the only additions to what runs.

## Checks run (foreground, per the brief)

- `scripts/check-control-registration.sh` — RED immediately after the
  archival (3 stale opt-out entries), GREEN after the repair commit:
  `controls=26|orphans=0|py_controls=295|py_orphans=0|py_named=194|py_catchall=86|py_optout=15|py_optout_ceiling=15`.
- `python3 scripts/validate-facts.py` — `2114 facts checked, 0 errors`. No
  fact's `checker_command` named an archived script.
- `python3 scripts/gen-plan.py --check` — clean.
- `scripts/check-aggregate-scope.sh` — **RED, pre-existing, not from this
  lane.** 11 divergences reported (a `check-test-attribute-integrity.py` path
  prefix mismatch, 9 python-binding `uv run`/`maturin`/`ruff` steps that only
  exist in the justfile, one `test-creal-prelude-build-ratio.sh` control only
  in `check.sh`). Diffed each against parent commit `aa74979ae`: all 11
  existed before this lane touched anything (`git show
  aa74979ae:justfile | grep -c "uv run\|maturin"` -> 40;
  `git show aa74979ae:scripts/check.sh | grep -c check-test-attribute-integrity`
  -> 2). The 3 newly-registered steps appear symmetrically in both
  `scripts/check.sh` and the `justfile`'s `check:` list, so they add zero new
  divergence. Not fixed here — it is a pre-existing, unrelated gap between
  the python-bindings tooling and `check.sh`, outside this task's scope.

## Left for later

The retrospective's R5 also proposed "the symmetric half of
`check-control-registration.sh`" — a ratchet asserting every `check-*`
SUBJECT (not just its control) has a caller, so a new orphan is red at
commit time instead of accumulating for two years. Not built in this pass:
it is a real, separately-sized piece of work (design the CALLERS set,
decide whether transitive script-to-script calls count or only direct
mentions like the existing control gate, handle the fact-`checker_command`
case, write mutation-verified controls for each guard). The 349-orphan
number this lane produced is exactly the baseline such a gate would need to
start from zero.

Also worth flagging for whoever picks this up: `scripts/archive/` now holds
346 scripts that are pure archaeology by design (host-specific paths,
one-shot SHA-256 pins). If disk/clutter ever becomes a concern, they are safe
to delete outright (git history preserves them) — moving rather than
deleting was the more conservative choice for this pass, per the brief's "the
cost of keeping one uncertain script is far below the cost of deleting a real
check," even though these three are about as certain-orphan as it gets.

Commits: `98d17aeef` (census + archive + register), `810ef0807` (opt-out
repair).
