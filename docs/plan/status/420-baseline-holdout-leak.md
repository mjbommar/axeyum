# Lane: baseline-holdout-leak — digest held-out endpoints out of the partition-edge baseline

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, baseline-holdout-leak, 2026-09-02).** ADR-1550's
`partition-edge-baseline-v1.json` wrote six crossing edges' held-out endpoint
as a plain-text fact id, so `check-autogenesis-holdout-isolation.py` was red
on `main` (`references=6`). Lane `nursery-repartition` verified this on a
clean snapshot and it stays the guard that measures it. Fixed the baseline
FORMAT, not the finding: an endpoint whose partition is `held-out` is now a
salted SHA-256 digest, tagged `held_out_endpoint: true`; the salt is
committed beside it (`held_out_salt`); non-held-out endpoints stay plain.
`--baseline`'s live comparison digests the current crossing edge with the
committed salt before testing membership, and `--record-baseline` reuses that
salt whenever the edge set is unchanged, so an unperturbed re-record stays
byte-identical. Edge set unchanged: still 198, `crossing=198|baselined=198
|violations=0|PASS`. Isolation gate: `references=6` -> `references=0`,
`verdict=FAIL` -> `verdict=PASS`.

Second, independent finding from the same brief: `MANIFEST_GLOB =
"nursery*.json"` in both `check-partition-edges.py` and
`nursery-components.py` went `Unanswerable` against ANY unrelated file
matching that glob dropped into `artifacts/autogenesis/`. Narrowed both to
`nursery-v1.json` plus `nursery-v*-extension.json`; a decoy control in each
suite drops `nursery-zzz-notes.json` and asserts the tool still answers.

Blocking, not assigned, fixed as a prerequisite:
`scripts/check-generated-artifact-ownership.py` did not `py_compile` on
`main` -- a prior merge had silently dropped the closing/opening boundary
between two `GUARDED` `Artifact(...)` entries and separately duplicated and
garbled a third entry's `runs=` block with text copied from the first. Not
this lane's defect (present before this lane's first commit; confirmed
against `main`'s tip directly), but it blocks verifying "ownership gate
passes for the baseline" at all, so reconstructed both entries verbatim from
their two originating commits (`6af4e162a`, `43b16059f`) rather than working
around it.

Mutation table: ten pre-existing single kills (M1-M10) preserved (two of
their `old_string` anchors had to move with the surrounding code but the
guard and its one kill are unchanged), plus **M11** ("a held-out endpoint is
redacted before it is written to the baseline") — deleting the digesting
kills exactly one test. `python3 scripts/tests/mutation_controls.py
partition-edges`: 11 mutants, 11 single kills, exit 0.

ADR-1550 amended (dated section) with the format change and both findings.

Did not run: `cargo` in any form, `just check`, `./scripts/check.sh`. No
`.rs` file touched. `scripts/check-generated-artifact-ownership.py` (full,
all `GUARDED` artifacts) run to completion, foreground, after the syntax fix
above -- see this lane's commit for the exit/summary line.

<!-- plan-section: landed-changes -->

| 2026-09-02 | baseline-holdout-leak | `check-partition-edges.py`: held-out baseline endpoints are salted-SHA-256 digests (`held_out_salt`, `held_out_endpoint: true`), not plain fact ids; `--baseline`/`--record-baseline` digest the live id the same way before comparing (ADR-1550 amendment) |
| 2026-09-02 | baseline-holdout-leak | `check-autogenesis-holdout-isolation.py`: `references=6` -> `references=0`, `verdict=FAIL` -> `verdict=PASS`; `check-partition-edges.py --baseline` unchanged at `crossing=198|baselined=198|violations=0|PASS` |
| 2026-09-02 | baseline-holdout-leak | `check-partition-edges.py` + `nursery-components.py`: `MANIFEST_GLOB` narrowed from `nursery*.json` to `nursery-v1.json` + `nursery-v*-extension.json`; both were `Unanswerable` against an unrelated matching file, both now pass with one committed |
| 2026-09-02 | baseline-holdout-leak | mutation table: M11 added ("a held-out id is never written in plain text"), M1-M10 preserved as single kills; 11/11, exit 0 |
| 2026-09-02 | baseline-holdout-leak | fixed a pre-existing (not this lane's) syntax defect in `check-generated-artifact-ownership.py` from a prior bad merge, blocking verification of the ownership gate; `held_out_salt` added to the baseline artifact's `required_keys` |
