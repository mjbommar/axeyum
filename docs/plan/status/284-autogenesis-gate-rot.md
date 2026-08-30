# Lane: autogenesis-gate-rot — six autogenesis gates reported RED, four fixed with evidence, two given precise accounts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (4/6 fixed, 2 precisely diagnosed and left open — see
below for why)`, autogenesis-gate-rot, 2026-08-29).**

Assigned six gates from a stale (pre-merge) `scripts/check.sh` run. Reproduced
every one directly before touching anything. Verdicts:

1. **`autogenesis-mathlib-facts` — BROKEN by design, fixed.** `verify_outputs`
   compared every catalog fact byte-for-byte against a freshly regenerated
   `epistemic_status: open, evidence: []` stub. That invariant broke the moment
   ANY of 214 catalogued facts left `open` — which happened the same day the
   gate was added (`b9daf91a5`, 2026-08-18) — so it has been red for anyone who
   ran `--check` for 11 days; nobody had. Measured the diff set across all 156
   now-proved facts: only `provenance`, `notes`, `epistemic_status`,
   `proof_route`, `axiom_footprint`, `evidence`, `depends_on`, `concept_refs`,
   and `formal` (replaced wholesale on proof, per ADR-0601) ever diverge;
   `id`/`title`/`statement`/`external_status`/`schema_version` never do across
   all 156. Fixed `verify_outputs` to require byte-exact equality only while a
   fact is still `open`; for a settled fact, only those five invariant fields.
   Added 3 tests (settled-diverges-ok, settled-identity-corruption-still-fails,
   open-mutation-still-fails). Commit `64ae9166e`.

Detail moved to [`../notes/284-autogenesis-gate-rot.md`](../notes/284-autogenesis-gate-rot.md).

