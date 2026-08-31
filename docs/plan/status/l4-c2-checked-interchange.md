# L4 phase C2 — universal checked interchange for credited roots

Lane: `l4-c2-checked-interchange`. Owns `artifacts/checked-interchange/`,
`scripts/gen-checked-interchange.py`, `scripts/check-checked-interchange.py`,
`scripts/tests/test-checked-interchange*`, this file, ADR-0915.

Status: IN PROGRESS (initial commit; population defined, exporter/importer/
replay pipeline and generator/checker not yet built).

## Credited-root population

Defined as the 9 declarations in ADR-0835's graph join
(`artifacts/graph-join/mathlib-group-defs-v1.join.json`) whose
`trust_footprints` dimension resolved: a Mathlib mirror fact exists, that
fact's kernel theorem exists in this kernel's checked environment, and its
axiom footprint is empty. Snapshot committed at
`artifacts/checked-interchange/populations/credited-roots-v1.json`; the
checker cross-validates it against a fresh read of the live join file.

9 of 446 declarations in the underlying population are credited roots by this
definition. 437 are not covered by C2 and this is stated, not hidden.

## Remaining work (this section will be updated as it lands)

- [ ] Rust test: export each credited root's closure, fresh-reimport
      independently, submit to pinned Lean's kernel, grade by name + type
      identity.
- [ ] `scripts/gen-checked-interchange.py`: drive the above, write the credit
      census artifact.
- [ ] `scripts/check-checked-interchange.py`: independent re-validator,
      fails on missing/absent/vacuous.
- [ ] Mutation-verify every guard 1:1.
- [ ] ADR-0915.
- [ ] Register gate in `justfile` and `scripts/check.sh`.
