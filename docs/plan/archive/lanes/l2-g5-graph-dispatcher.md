# Lane: l2-g5-graph-dispatcher — L2 phase G5, graph selection as the ordinary dispatcher

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, l2-g5-graph-dispatcher, 2026-08-30).** Built the
three-layer composition the G5 spec asks for, scoped its authority to
exactly what ADR-0865 measured, and made proposing a held-out fact
structurally impossible (proven, not asserted). ADR-0885 records the
decision. See it for the full design rationale; this file is the pulse.

## What landed

- `scripts/lib/graph_dispatcher.py` — the composition. Curriculum
  (`docs/curriculum/curriculum.toml`) picks the destination; the
  infrastructure frontier (`artifacts/infrastructure-frontier/*.frontier.json`,
  ADR-0845, read-only) picks the capability; `check-dispatchable-frontier.py
  --json` (invoked as a subprocess, never edited) picks the legal target,
  restricted to its `dispatchable` list only.
- `scripts/gen-graph-dispatcher.py` — writes
  `artifacts/graph-dispatcher/{recommendation.json,dashboard.md}`; supports
  `--override-legal-target FACT_ID --evidence-note-file PATH` (refuses
  without a note, refuses a held-out/mutation/blocked/unknown target, no
  ledger write on refusal) and `--check` (drift check, no writes).
- `scripts/check-graph-dispatcher.py` — the gate. Ten guards, each
  mutation-verified to be killed by exactly one fixture
  (`scripts/tests/test-graph-dispatcher-mutations.sh`, full kill table at
  the end of the run, every guard present IN the table).
- `scripts/tests/test-graph-dispatcher.py` — functional tests, including the
  held-out-refused-by-name demonstration and a spurious-token-match
  negative control (`"left"` must not link `and_or_distrib_left` to
  `mul_left_cancel`).
- ADR-0885, this file, `justfile`/`scripts/check.sh` registration (one line
  each, appended, not restructured).

## Worked example (current tree)

```
destination:  groups (docs/curriculum/02-structures/groups.md), 3 supporting rows
capability:   IF-LANG-4f071ea9a3 -- CommMagma/mul_comm [authoritative]
              (population mathlib-group-defs-v1, queue language-infrastructure
              -- exactly ADR-0865's tested scope)
legal target: F:ml430-nat-and-div-two-1a2f7c33 [advisory, match_kind=fallback]
              -- no dispatchable fact links to CommMagma/mul_comm by
              identifier; the two populations are largely disjoint, per
              ADR-0845's own cross-check finding.
```

Every curriculum destination other than `groups` has zero supporting
infrastructure-frontier rows today and is reported as unserved, not
silently dropped (`destination.candidates_considered` in
`artifacts/graph-dispatcher/recommendation.json` carries the full ranked
list).

## Authority scope (do not extend without a new ADR)

`"authoritative"` appears ONLY for `population_id ==
"mathlib-group-defs-v1"` and `queue in {"language-infrastructure",
"proof-producers"}` -- literally ADR-0865's tested (population, queue)
pair. A "fallback"-matched legal target is NEVER authoritative regardless of
the capability's own scope (`AUTHORITY_SCOPE` guard). Every other
combination -- a future population, `theorem-dominators`,
`dependency-ready-leaves`, or a destination-bridge population once one
exists -- is advisory: visible, ranked, overridable, never binding.

## Held-out proof (not just a claim)

`python3 scripts/gen-graph-dispatcher.py --override-legal-target
F:ml430-int-add-ediv-of-dvd-left-52ee6c5c --evidence-note-file <note>`
(a real held-out fact, 2026-08-30 population) was run against the live
tree and printed:

```
REFUSED: 'F:ml430-int-add-ediv-of-dvd-left-52ee6c5c' is held-out (blind
evaluation population, ADR-0542) and cannot be dispatched, override or not.
```

exit 1, no write to `overrides.jsonl`. `HELD_OUT_NEVER_PROPOSED` in
`check-graph-dispatcher.py` independently re-checks this on every gate run
against a freshly computed held-out/mutation/blocked set, for both the
committed recommendation and every override-ledger entry.

## Override mechanism

`overrides.jsonl` is append-only and currently EMPTY (no lane has used it
yet). A note under 20 characters, one not naming the fact it overrides, or
one for a fact that is held-out/mutation/blocked/not-dispatchable is
refused synchronously with no ledger write -- "usable only with an evidence
note" is enforced at the point of use, not audited after the fact.
`OVERRIDE_LEDGER_COMPLETE` independently re-validates every ledger entry
(note length, names its target, has an identified lane) so a hand-edited
entry bypassing the CLI is still caught by the gate.

## Autogenesis isolation (never touched, checked anyway)

`artifacts/autogenesis/` was not read or written by this lane at any point.
`python3 scripts/check-autogenesis-holdout-isolation.py` — run before
starting this lane's edits and again after finishing —
both report `AUTOGENESIS_HOLDOUT_ISOLATION|held_out=136|files_scanned=1110|
settled=0|references=0|verdict=PASS` (unchanged; this lane's edits are
entirely outside that tree).

## Absence check (rule 5)

`build_recommendation()` raises `DispatcherError` naming the failing layer
if: curriculum.toml or every frontier document is missing/unreadable; no
curriculum destination has a supporting row; the chosen destination has
zero capability rows; `check-dispatchable-frontier.py` itself fails (nonzero
exit or non-empty `guard_failures`); or the dispatchable set is empty.
`gen-graph-dispatcher.py` and `check-graph-dispatcher.py` both propagate
this as a nonzero exit with the reason printed — there is no code path that
silently produces a recommendation with a missing layer.

## What would make me trust this dispatcher less

If a future population's infrastructure frontier and the `ml430` dispatchable
set stopped being disjoint and `match_legal_target` started returning
"linked" matches routinely — the identifier-matching design has only ever
been exercised against genuinely disjoint data plus one synthetic fixture,
so its behavior under real, frequent links is unverified, and a
loosely-specified `subject_declarations` field (a capability row author
free-typing a common word) could produce a technically-exact but
substantively spurious link that the current guards would wave through as
"authoritative" if the capability also happened to be in scope.

## Left for the next lane / a future ADR

- Extending `PILOTED_POPULATION`/`PILOTED_QUEUES` requires a new ADR that
  measures the extension the way ADR-0865 measured this one — not a source
  edit alone.
- A second joined population on a genuine destination-bridge module
  (linear algebra / polynomials / analysis) would give `select_destination`
  more than one servable destination to rank, and is the prerequisite for
  ever testing category 3.
