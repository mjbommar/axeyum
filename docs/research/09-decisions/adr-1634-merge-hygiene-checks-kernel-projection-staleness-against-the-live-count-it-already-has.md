# ADR-1634: merge hygiene checks kernel-projection staleness against the live count it already has

Status: accepted
Date: 2026-09-05
Lane: `kernel-projection-regen`

Index-summary: `scripts/check-merge-hygiene.sh` gained a tenth enforced
guard comparing `artifacts/autogenesis/kernel-dependency-projection-v1.json`'s
committed declaration count against the live count `shape_search` already
computes for the duplicate-declaration guard, closing a ten-day drift
(1,644 vs 4,260 declarations) that no gate had ever compared.

## Context

`gen-autogenesis-kernel-dependency-projection.py --check` is the real
freshness check for the kernel dependency projection, and it had been failing
on `main` since 2026-08-26 (measured by lane `hall-counting`): the committed
projection indexed 1,644 declarations against ~3,050 live at the time (4,260
by 2026-09-05), missing every `Nat.Finset.*`, `Nat.Hall.*`, `Nat.Subsets.*`,
`CatS.*`, and `IntSpace.*` declaration entirely. `scripts/check-merge-hygiene.sh`
reported `generated=current` on every merge across that whole window, because
it never invoked the real check at all — the real `--check` needs a debug
kernel build that runs for tens of minutes (`kernel_declaration_projection`,
built via `cargo run` with no `--release`), which cannot live in a
gate CLAUDE.md documents as costing "a few seconds."

This is the same shape of defect `docs/contributor-guide/evidence-and-checker-discipline.md`
already catalogues under "a generated artifact nobody compared against its
source": an expensive real check exists, drifts silently because nothing cheap
stands in for it at merge time, and the cheap gate's summary line
(`generated=current`) actively asserts freshness it never measured.

## Decision

Regenerate the projection now (1,644 → 4,260 declarations, 7,677 → new count
theorem-dependency edges; see the regeneration commit for exact numbers), and
add a tenth enforced guard to `scripts/check-merge-hygiene.sh` that compares
the committed projection's `census.declarations` against a live count —
without paying for a second kernel build.

The live count comes from `shape_search`'s own `coverage: … declarations=N …`
line, which the merge-hygiene gate's guard 7 (`check-shape-duplicates.py
--prebuilt`) already produces by running the prebuilt `shape_search` binary.
Previously that line was computed and then discarded inside
`check-shape-duplicates.py` — its own stdout only ever printed `OK: N
duplicate group(s)…` or a `FAIL:`. This ADR's change also makes
`check-shape-duplicates.py` forward `shape_search`'s coverage line verbatim to
its own stdout (`parse_coverage_line`, unconditional once the tool's output is
in hand), so `check-merge-hygiene.sh` can read the live declaration count from
`shape_dupes_out` with a `grep`, at effectively zero additional cost. This is
a small, backward-compatible contract change to an existing checker's stdout:
no existing assertion in `scripts/tests/test_check_shape_duplicates.py`
depends on stdout being exactly the `OK:`/`FAIL:` line (verified: the whole
suite, 24 tests, passes unchanged after the edit).

The new guard tolerates a small difference (5 declarations) between the two
counts, since the projection and the `shape_search` binary can each be built
from a slightly different HEAD; a gap larger than that is drift nobody is
watching, exactly like the ten-day incident this closes. Like guards 4, 8 and
9, it has three outcomes: `ok`, `stale` (fails the gate), and `not-answerable`
(guard 7 was skipped, unavailable, or produced no coverage line — reported,
never a failure, per the standing rule that a gate must not report "stale"
when it could not measure).

## Evidence

- Regeneration: `python3 scripts/gen-autogenesis-kernel-dependency-projection.py`
  then `--check` (exit 0) and
  `python3 scripts/validate-autogenesis-kernel-dependency-projection.py`
  (exit 0) — exact before/after counts recorded in the regeneration commit
  message.
- New guard controls: `scripts/tests/test_check_merge_hygiene.py` gained
  `test_a_stale_kernel_projection_fails_the_gate`,
  `test_a_current_kernel_projection_passes_within_tolerance`, and
  `test_no_live_count_on_hand_is_not_answerable_not_a_failure`. Full suite:
  26 tests, all pass.
- Mutation: `scripts/tests/mutation_controls.py merge-hygiene`, mutant M17
  (removing the staleness comparison) kills exactly
  `test_a_stale_kernel_projection_fails_the_gate` (1 test), leaving all other
  25 tests green — including the two new accept-path controls, which never
  reach that branch either way.
- `check-shape-duplicates.py`'s own suite
  (`scripts/tests/test_check_shape_duplicates.py`, 24 tests) is unaffected by
  the coverage-line forwarding change.

## Alternatives

- **Run the real `--check` in the merge-hygiene gate.** Rejected: it costs
  tens of minutes (a debug kernel build), an order of magnitude past every
  other guard in this gate, for the same reason the duplicate-declaration
  check moved to a prebuilt-binary route in ADR-1511's amendment rather than
  living in `check.sh` alone.
- **Re-run `shape_search` a second time just for this guard.** Rejected: a
  second invocation pays the whole ~130s index build again (measured
  2026-09-05), which defeats the point of a "cheap" guard; reusing guard 7's
  already-paid-for output costs a `grep`.
- **Leave the projection's staleness entirely unchecked at merge time**
  (the status quo). Rejected: this is the exact defect being fixed, already
  measured at ten days and 2,616 missing declarations.

## Consequences

- A projection this stale cannot land again without the merge-hygiene gate
  saying so, at effectively zero added cost to a gate already documented as
  "cheap."
- The comparison is a NECESSARY, not sufficient, freshness check — like guard
  6's theorem-ledger cross-consistency, two stale artifacts built from the
  same drifted kernel snapshot would still agree with each other. The real
  freshness check remains `gen-autogenesis-kernel-dependency-projection.py
  --check` in `scripts/check.sh` / `just check`.
- `check-shape-duplicates.py`'s stdout now always carries the coverage line
  when it has one, which any other future caller reading that script's output
  can also rely on.
