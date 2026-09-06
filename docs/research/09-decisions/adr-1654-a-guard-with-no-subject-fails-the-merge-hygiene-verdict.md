# ADR-1654: A guard with no subject fails the merge-hygiene verdict

Status: accepted
Date: 2026-09-05
Index-summary: `check-merge-hygiene.sh` could print `PASS`, exit 0, while a
guard's field read `skipped(tool-failed)` -- the shape_search binary
panicking, not merely being absent. `tool-failed` (a present, non-stale
binary that still produced nothing) now fails the aggregate; `no-binary` and
`stale-binary` (host facts about an unbuilt or outdated `target/`) stay
PASS-compatible, and the pinned-inventory `n/a` field is relabelled
`n/a-empty` so a proven-zero population can never be misread as the same
thing as an unanswerable one.
Index-status: accepted

- **Lane**: `hygiene-verdict`
- **Amends**: `scripts/check-merge-hygiene.sh` (landed 2026-08-30, amended by
  ADR-1511, ADR-1546/1550, and lane `kernel-projection-regen` on 2026-09-05).
  Closes the finding recorded in
  [evidence-and-checker-discipline.md](../../contributor-guide/evidence-and-checker-discipline.md),
  "A green summary line with a guard that has no subject".

## Context

`check-merge-hygiene.sh` is the coordinator's ~20-second post-merge gate. Four
of its guards (the frontier shape census, the duplicate-declaration check, the
partition-edge check, and the kernel-dependency-projection staleness check)
are deliberately three-outcome: `ok`/current, a real failure, or "cannot
answer" -- because reading an absent subject as a failure has itself shipped
wrong red gates in this repository before (a missing `target/` binary, a
census with no frontier facts, a partition manifest that does not exist yet
are all legitimate states on a fresh or early checkout, not defects).

That design has a blind spot the 2026-08-30 audit did not anticipate: "cannot
answer" and "the tool is broken" print through the *same* field value. On
2026-09-05 (lane `incidence-geometry`) the gate printed

```
...|shape_duplicates=skipped(tool-failed)|kernel_projection=not-answerable|PASS
```

with exit 0, while `target/release/examples/shape_search
--include-constructed --duplicates` was panicking on a real coverage
assertion (a prelude group indexed but not declared). `check-shape-duplicates.py
--prebuilt` reports that crash under the SAME `UNAVAILABLE tool-failed` token
it uses for "the subprocess did not run" -- and `check-merge-hygiene.sh` reads
every `UNAVAILABLE` token identically to `no-binary` (never built here) and
`stale-binary` (built before a kernel source changed), which really are host
facts that must not block a merge. `kernel_projection`, fed no live
declaration count because guard 7 gave it nothing, then reported its own
`not-answerable` downstream. Two guards had no subject; neither could fail;
the aggregate inherited their silence and printed `PASS`.

The lane caught it by reading the summary fields by hand, not from the exit
status -- exactly the failure mode CLAUDE.md's checker-discipline section
warns about: *a checker that cannot fail is worse than no checker*, because it
manufactures an unfalsifiable claim at the speed the flywheel runs.

## Decision

### 1. `tool-failed` is not a host fact, and now fails the aggregate

`scripts/check-shape-duplicates.py --prebuilt` raises `PrebuiltUnavailable`
with one of three tokens: `no-binary` (never built here), `stale-binary`
(older than a kernel source), or `tool-failed` (the binary is present and not
stale and still produced nothing usable -- it crashed, timed out, or exited
nonzero for a reason other than staleness). The first two describe the
*environment*: a fact about this host's `target/` that a future build will
resolve on its own, exactly like a missing `rustfmt` for the Python
prelude-field guard. `tool-failed` describes the *tool*: something that was
supposed to answer, ran, and did not -- which is precisely "a guard with no
subject" in the sense the finding names.

`check-merge-hygiene.sh` now distinguishes them: `no-binary` and
`stale-binary` remain `skipped(<token>)`, PASS-compatible, unchanged. When the
token is `tool-failed`, the gate sets `fail=1`, prints
`FAIL: check-shape-duplicates.py --prebuilt (tool-failed: no subject)` with
the captured output and a remedy (rebuild the binary and re-run it directly
to see the real failure), and the aggregate line is never printed for that run
-- it exits with `MERGE_HYGIENE|FAILED` instead of `PASS`.

This is deliberately narrow. The other three-outcome guards (frontier shape
census, partition-crossing edges, kernel-dependency-projection staleness, and
the Python prelude-field table's missing-`rustfmt` case) keep their existing,
separately-argued "cannot answer is not a failure" semantics; none of their
own `not-answerable` or `skipped` paths changed. Widening this rule to every
occurrence of those two words in the script was considered and rejected here:
each of those guards' non-failing paths is independently defended by its own
years-old incident (a missing `just`/`lean`/`cargo-deny` on one fleet host of
five; a census with genuinely no frontier facts; a partition manifest that
does not exist before the first re-partition), and collapsing them into one
blanket rule would re-introduce the exact defect class CLAUDE.md warns
against for the *opposite* reason -- a gate that turns "I don't know" into
"you are wrong" on a routine, expected absence trains a coordinator to stop
trusting or to bypass it. The fix here targets exactly the state the incident
exposed: a subject that WAS present and STILL had nothing to say.

### 2. `n/a-empty` replaces the unlabelled `n/a` for a proven-zero population

The pinned-inventory field's value was `n/a (no live pin sites; see the note
above)`. That is not "cannot answer" -- there being no live pinned-inventory
array in the tree today is itself the (checked, by-hand) finding, a KNOWN
population of size zero, not a gap in the checking. Relabelling it
`n/a-empty` makes that read unambiguous next to `not-answerable`, which now
names a strictly different thing elsewhere in the same summary line: "the
guard could not tell." A future guard revival (`nat_prelude_tests.rs` is the
likely site, per the guard's own note) that returns a genuine
`recount-pinned-inventory.py --check` exit 2 must use `not-answerable`, never
`n/a-empty` -- the two are not interchangeable spellings of the same state.

## Consequences

- A `shape_search --include-constructed --duplicates` crash now blocks a
  merge through `check-merge-hygiene.sh` directly, rather than only showing up
  hours later in `scripts/check.sh` / `just check` (or not at all, if nobody
  happened to read the summary fields).
- `no-binary` and `stale-binary` are unaffected: a fresh checkout with no
  `target/` yet, or one whose `shape_search` predates a kernel-source change,
  still passes the gate and is told to build/rebuild -- consistent with every
  other "not built here yet" guard in this script.
- `pinned_inventories=n/a-empty` and `pinned_inventories=not-answerable` are
  now two different, non-interchangeable field values a future patch to that
  guard must choose between correctly.
- The census, partition-edge, and kernel-projection guards' `not-answerable`
  paths, and the Python prelude-field guard's missing-`rustfmt` `skipped`
  path, are unchanged; each remains a documented, separately-justified
  non-failure.

## Evidence

- `scripts/check-merge-hygiene.sh` (guard 7 and guard 5 blocks).
- `scripts/tests/test_check_merge_hygiene.py`:
  `test_a_tool_failed_shape_duplicates_binary_fails_the_gate`,
  `test_a_healthy_shape_duplicates_binary_still_passes`,
  `test_no_binary_and_stale_binary_remain_skip_not_fail`,
  `test_pinned_inventories_reports_n_a_empty_not_not_answerable`; the 26
  pre-existing controls in that file all still pass unchanged, confirming the
  four other three-outcome guards' semantics were not touched.
- `scripts/tests/mutation_controls.py`, suite `merge-hygiene`, mutant M18:
  removing the new `tool-failed` branch (`if [ "$shape_dupes_token" =
  "tool-failed" ]; then` -> `if false; then`) kills exactly
  `test_a_tool_failed_shape_duplicates_binary_fails_the_gate` and no other
  test in the 30-test suite (measured: `killed 1`).
