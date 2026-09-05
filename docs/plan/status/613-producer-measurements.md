# Lane: producer-measurements — W1-12 (exact-real cost) and W1-13 (cas-internal residue)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, producer-measurements, 2026-09-04).** Measurement-only
lane (ADR-1617 reserved), no kernel declarations. Starting work: reading
`docs/math-department/11-applied-and-computational.md`, `CLAUDE.md`,
`docs/contributor-guide/measurement-hazards.md`, and ADR-0601, then measuring
(A) the exact-real (`CReal`) evaluation cost envelope for pi/e/sqrt2/exp(1),
and (B) the `cas-internal` vs `kernel-reconstructed` residue in
`artifacts/facts/*.json` `cas-certificate` facts, per `scripts/validate-facts.py`'s
own classifier. Will update this row-by-row as each deliverable lands.

<!-- plan-section: landed-changes -->

| 2026-09-04 | producer-measurements | lane started: W1-12/W1-13, ADR-1617 reserved |
