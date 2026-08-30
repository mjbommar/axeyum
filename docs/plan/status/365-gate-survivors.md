# Lane 365 — gate survivors

<!-- plan-section: lane-status -->

## Status

**LANDED.** All five gates named in
[the 2026-08-30 session audit](../../research/11-design-review/2026-08-30-session-audit.md)
§5b now have controls that die when the guard dies. Every kill set below is as
measured by `scripts/tests/mutation_controls.py`, survivors included.

The standing rule this lane worked to: **a gate is not made green by making it
blind.** Two gates gained new failure modes (a ratchet, a scope assertion) and
both were driven to red on purpose before being recorded green.

### 1. `check-merge-hygiene.sh` — zero controls, and its exemption covered every control suite

It landed the same day with **no registered controls**, so every guard in it was
a survivor by definition. Ten scenarios now drive the shipped script against a
throwaway git tree (`AXEYUM_MERGE_HYGIENE_ROOT`, the `AXEYUM_KERNEL_SUITES_ROOT`
device); nothing is re-implemented.

Two defects fixed alongside, both reported by the audit:

- the conflict-marker pathspec excluded `scripts/tests/*` — **every control
  suite in the repository** — from the marker guard. Narrowed to
  `scripts/tests/fixtures/*`. Measured before narrowing: zero tracked files
  under `scripts/tests/` contain a marker, so it cost nothing. The new suite
  therefore *builds* its marker text from repeated characters rather than
  writing it literally, so it is scanned by the guard it tests.
- the header said "the four things" while the body gives a reasoned explanation
  for enforcing three.

| mutant | killed |
| --- | --- |
| M1 conflict-marker branch | 4 |
| M2 bare `=======` alternative | 1 |
| M3 `fixtures/` exemption, not the whole directory | 1 |
| M4 ADR-index branch | 3 |
| M5 the ADR checker's own output is reported | 1 |
| M6 `gen-plan` branch | 2 |

No survivors. M1/M4/M6 kill more than one because each is **one** `if` reached
by several scenarios; a suite in which they died separately would be testing
branches that do not exist.

### 2. `check-aggregate-scope.sh` — an untested failure path and a live phantom class

`if [ -s "$new" ]; then` → `if false; then` left the registered suite green
(`AGGREGATE_SCOPE_CONTROLS|guards=5|negative_controls=2|PASS`, exit 0), because
all five registered controls test the **normalizer**.

`test-check-aggregate-scope.sh` keeps that job. The new suite drives the gate
end to end on a synthetic tree via `AXEYUM_AGGREGATE_SCOPE_ROOT` — hermetic,
because the real tree costs 413 + 469 steps to enumerate and because the
zero-side refusal cannot be reached on it at all.

The phantom: `strip_wrappers` *tested* for a leading environment assignment with
a quote-aware regex and *stripped* it with `line.split(" ", 1)`, which cuts at
the first space — inside the quotes.

Detail moved to [`../notes/365-gate-survivors.md`](../notes/365-gate-survivors.md).

