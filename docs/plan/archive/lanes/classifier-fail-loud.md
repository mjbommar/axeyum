# Lane: classifier-fail-loud — make a curriculum-bucket mis-attribution loud

<!-- plan-section: lane-status -->

**A bucket MIS-attribution is now loud, not just an unattributed one** (`COMPLETE`, classifier-fail-loud, 2026-08-31). ADR-1215.

`scripts/measure-curriculum-kernel-coverage.py`'s residual counter catches a
declaration attributed to NOTHING and structurally cannot catch one attributed
to the wrong REAL bucket — the node's pinned count stays unchanged and wrong.
That happened twice in two days (ADR-1140 `det2|det3`, ADR-1205
`gauss_fold_injective`), both times because a pattern named INSTANCES and the
family grew past it.

Three ratcheted guards over name FAMILIES (first word of the local name,
camelCase and snake_case folded, trailing digits stripped) against
`artifacts/curriculum/bucket-cohesion-pin.tsv`:

- **G1 SPLIT** — a family attributing to an unpinned node SET. Both incidents.
- **G2 FAMILY** — a family of >= 8 declarations entirely inside a catch-all,
  unpinned. The case G1 cannot see: a family with no partial match never splits.
- **G3 STALE** — a pinned row matching no measured family, so the pin cannot rot.

Plus two input refusals: a projection under 2,500 declarations is refused
(a short index makes a new family look like it was always in the catch-all),
and `--require-pin` refuses a missing pin before the projection is even read.

### What was measured

- **The projection does NOT carry a source module.** It emits
  `kernel.environment()`, which stores no provenance. Recovering the module by
  scanning Rust source reaches **76.7%** (2,022 of 2,636) and needs a hand-kept
  table of which per-prelude helper DECLARES vs CONSUMES — I got `.lemma` wrong
  in one command (57.3% with 628 spurious ambiguities). And module cohesion
  would have missed ADR-1140 anyway: `Rat.det2` is in `matrix.rs` and `Rat.det`
  in `matrix_det.rs`, so each module was internally cohesive and wrong.
- **Both incidents replay RED** against a 124-row slice of the real projection
  with the pattern tables `git show`n at `d2bb38a1e^` and `bd382566b^`, each
  naming the affected declarations; the same slice with the shipped table gives
  0 findings.
- **Mutation sweep: 9 mutations, all KILLED, 0 survivors.** The first run had
  three survivors, each a real hole (a floor test that read the constant it was
  testing; a `--require-pin` test passing on a different refusal; one equivalent
  mutant).
- **False positives on the current tree: ZERO, measured.** The pin was cut from
  2,636 declarations; a projection built from `main` an hour later carries
  2,675 — 39 new declarations of ordinary lane work — and the gate reports 0
  findings on it.
- **The classifier was registered in NEITHER gate.** Now both, as the CHECKER
  and not only its tests.

### Handed on, not fixed here

- `docs/curriculum/curriculum.toml`'s `kernel_decls` pins are not a snapshot of
  any single tree state: `naturals` 518 matches, `rationals` is pinned 206
  against a measured 221 and `linear-algebra` 90 against 96. Left alone because
  the `curriculum-spines` lane is actively editing that file;
  `--expect-node-counts docs/curriculum/curriculum.toml` re-derives it.
- `artifacts/autogenesis/kernel-dependency-projection-v1.json` is badly stale:
  1,644 declarations against a live 2,675, missing `Rat.det`, `Nat.gaussFold`
  and `CReal.integral`. It cannot be used as a cheap gate input by anything.

## Landed changes

| change | files |
| --- | --- |
| the three cohesion guards, the projection floor, `--require-pin`, `--run-projection`, `--expect-node-counts` | `scripts/measure-curriculum-kernel-coverage.py` |
| the pin (27 splits + 59 catch-all families) | `artifacts/curriculum/bucket-cohesion-pin.tsv` |
| controls, incl. both historical replays against real data | `scripts/tests/test_curriculum_bucket_cohesion.py`, `scripts/tests/fixtures/curriculum-projection-slice.tsv` |
| mutation sweep `curriculum-bucket-cohesion` | `scripts/tests/mutation_controls.py` |
| the CHECKER registered, not only its tests | `scripts/check.sh`, `justfile` |
| the decision | `docs/research/09-decisions/adr-1215-…md` |
