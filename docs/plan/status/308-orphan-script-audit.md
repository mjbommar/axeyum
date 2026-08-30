# Lane: orphan-script-audit — census and clean up `scripts/check-*` orphans

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, orphan-script-audit, 2026-08-29).**
Re-measured the 2026-08-29 process retrospective's "352 of 503" orphan-script
claim from scratch, found the correct number (349 of 504, reproducing the
retrospective within corpus drift), diagnosed why an independent cruder query
landed at 398, archived the 346 dead one-off capsule checkers plus their 92
orphan controls, registered the 3 genuinely useful never-wired-up scripts as
new gate steps, and repaired the opt-out fallout the archival caused. Nothing
left half-done; no further action required from the next lane on this
specific audit, though the retrospective's suggested "subject registration"
ratchet (mirroring `check-control-registration.sh` for `check-*` SUBJECTS,
not just their controls) remains unbuilt — see "Left for later" below.

## The census: method, numbers, and why they disagree

**Universe.** `scripts/check-*.{sh,py}` at the top level of `scripts/` (not
recursive — nothing matching lives in a subdirectory): **504** files. (The
retrospective's snapshot was 503; two scripts — `check-fast.sh`,
`check-mirror-statement-fidelity.py` — landed between its snapshot and this
one, both live.)

**Method.** A file X "references" script Y if Y's basename (or, for
`scripts/tests/test_*.py`, its dotted-module form `scripts.tests.NAME` too —
see below) is a substring of X's text. Roots: `scripts/check.sh`, `justfile`,
`hooks/*`, `.github/workflows/*`, and every `artifacts/facts/*.json`
`checker_command`. Compute the full reference graph over every file under
`scripts/` (not just `check-*` ones — an intermediate helper like
`run-python-controls.py` can itself be named by a root and then name further
scripts), BFS from the roots, and a `check-*` script is LIVE iff it is in the
closure. Two built-in controls run every time: **positive** —
`check-aggregate-scope.sh` must classify as live (it does); **negative** — a
fabricated name `check-zzz-nonexistent.sh` must get zero hits anywhere (it
does).

**Three numbers, and only one survives scrutiny:**

Detail moved to [`../notes/308-orphan-script-audit.md`](../notes/308-orphan-script-audit.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | orphan-script-audit | `98d17aeef` census + archive 346 dead `check-autogenesis-*` scripts (+ 92 controls) to `scripts/archive/`; register `check-shared-index.sh`, `check-sos-negative-controls.sh`, `check-evidence-portability.sh` as new gate steps |
| 2026-08-29 | orphan-script-audit | `810ef0807` fix 3 `scripts/control-optout.tsv` entries left stale by the archival; lower `OPTOUT_CEILING` 18 -> 15 |
