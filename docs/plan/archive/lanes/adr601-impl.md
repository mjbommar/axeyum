# Lane: adr601-impl — ADR-0601 routes 2 and 3 (validator split, import backlog artifact)

<!-- plan-section: lane-status -->

**ADR-0601 SS2+SS3 landed (`WIP`, adr601-impl, 2026-08-27).**
`scripts/validate-facts.py` now classifies every `cas-certificate` fact's
evidence by what its `checker_command` actually executes
(`classify_cas_certificate_checker`/`classify_cas_certificate_fact`):
`kernel-reconstructed` (a `cargo test`/`cargo run` segment names
`axeyum-lean-kernel`) vs `cas-internal` (only `axeyum-cas`). An unclassifiable
checker on a `cas-certificate` fact is now a validation error — the
checker-that-cannot-fail defect one level up. Measured on the current ledger:
`cas-certificate: 23 total -- kernel-reconstructed 0, cas-internal 23`,
printed in both the summary's per-route line and its own dedicated line.
`python3 scripts/validate-facts.py` stays green: 776 facts, 0 errors.

`scripts/gen-import-backlog.py` (new) turns the validator's bare "164 settled
elsewhere but not here" count into a produced, deterministic artifact,
`artifacts/import-backlog.json`: 164 rows, 117 `dependency_ready`, 1
`curriculum_node`-mapped (the curriculum-mapping is an EXACT match on
`concept_refs[].graph == "math-education"` against a `curriculum.toml` node
id — see `docs/autogenesis/289-import-backlog-artifact.md` for why this is
exact rather than fuzzy, and why the mapped count is small and honest).
`--check` mode mirrors `gen-plan.py --check`'s convention; registered in
`scripts/check.sh` and the `justfile` next to `gen-adr-index.py --check`.
`scripts/fact-frontier.py` was NOT touched (owned by a concurrent lane).

Both new classifiers are mutation-tested via
`scripts/tests/mutation_controls.py` (`fact-cas-certificate-classification`,
`import-backlog-classification`), each guard confirmed to kill exactly one
test.

Not done: no attempt was made to extend the `math-education`↔`curriculum.toml`
crosswalk beyond the 4 ids that already coincide exactly — that would need a
maintained mapping table this task's scope did not include, and a fuzzier
matcher would manufacture edges nobody asserted.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `14a6484d3` | `scripts/validate-facts.py`: classify `cas-certificate` evidence as `kernel-reconstructed` vs `cas-internal`, reject an unclassifiable checker_command on that route (ADR-0601 SS2). Mutation-tested. |
| 2026-08-27 | `17e91d839` | `scripts/gen-import-backlog.py` (new): produce `artifacts/import-backlog.json`, the 164-row import backlog, deterministic and ordered by dependency-readiness then curriculum-DAG position (ADR-0601 SS3). `--check` wired into `scripts/check.sh` and the `justfile`. Mutation-tested. |
