# Lane: agent-decouple-math-education — reference-only was a wish; now it is a gate

<!-- plan-section: lane-status -->

**The data coupling to `../math-education` is removed and
`scripts/check-external-coupling.py` refuses its return** (`WIP`,
agent-decouple-math-education, 2026-08-24). The owner's constraint is that the
sibling is REFERENCE ONLY — read it for calibration, never depend on it,
integrate with it, or point at it in data. It was stated and never gated, and by
today it had been violated in **five places at once**, with every validator
involved exiting 0:

- the knowledge overlay (an `external-repository` source, an `external-pinned`
  namespace, **24 of 33 links** pinned to that repo's SHA);
- the family-concept crosswalk (`path_hint: ../math-education/graph/concepts`,
  and a validator that hardcoded the SHA and *required* the file to match);
- `tactic-catalog.schema.json`, where `uses_technique` is required on every
  tactic and required `source: {const: "math-education"}` plus a `revision` —
  so no tactic could be declared here without naming that checkout;
- **all 104 claims**, each carrying `provenance.graph_pin` and 438
  `resolved: true` refs, with the schema making `concept_refs` mandatory and
  `graph` a one-value enum;
- `python/axeyum/knowledge/math_education.py`, 777 lines that resolved
  `Path("..") / "math-education"`, ran `git rev-parse HEAD` against it, and put
  the resulting `file://` prefix **into the agent's fetch allowlist**.

Four validators reached outside the checkout in code, one of them defaulting to
`~/projects/personal/math-education/graph` — an absolute path into one machine's
home directory, in a tracked file.

Detail moved to [`../notes/118-external-coupling.md`](../notes/118-external-coupling.md).

<!-- plan-section: landed-changes -->

| 2026-08-24 | `da1701d97` | The knowledge overlay may not name a sibling repository: source, namespace, 24 links and three unreachable relation types removed; schema tightened so the vocabulary cannot come back; the validator no longer reads `ROOT.parent`. |
| 2026-08-24 | `94f3beb0c` | The crosswalk and the tactic catalog, plus the two projections that went structurally empty with them. `uses_technique` no longer mandates an external source on every tactic. 13 tactic guards, each killed by exactly one test. |
| 2026-08-24 | `70aaccb38` | `scripts/check-external-coupling.py` — 4 rules, 8 guards, 25 controls, each guard killed by exactly one test; wired into both aggregates with `--self-test` first. `graph_pin` and `resolved` removed from all 104 claims; the 777-line Python integration and the agent's `file://` allowlist entry deleted. |
