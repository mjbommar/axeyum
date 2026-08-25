# Lane: agent-portable-evidence — artifacts an external checker can read

<!-- plan-section: lane-status -->

**Gap #5: the rule vocabulary was fixed and it was never the binding constraint
(`WIP`, agent-portable-evidence, 2026-08-21).**
[Gap analysis](../gap-analysis-smt-solvers-2026-08-21.md) §9 row 5 / §6.2.

**Carcara was built here for the first time.** No host in this repository had a
Carcara binary — not in `references/`, not on `$PATH`, not on any fleet host —
so every test in `tests/carcara_crosscheck.rs` had been passing by returning
early for as long as the file has existed. `references/carcara` now carries a
built `target/release/carcara` (Carcara 1.1.0, `6624ea80`). Building it needs
`m4`, which is not installed on this box but ships inside a snap
(`/snap/gnome-46-2404/153/usr/bin/m4`); no host package was installed.

**The central claim of the array-proof design note is false.**
`docs/research/07-verification/array-elimination-alethe-proofs.md` records
"Alethe/Carcara has NO array theory rules", quoted from there into six doc
comments, into `check_alethe`'s dispatch, and into the design of two emitters.
Carcara 1.1.0 registers `arrays_idx`, `arrays_row`, `arrays_row_contra` and
`arrays_ext`, and `arrays_idx` **is** axeyum's `read_over_write_same`, shape for
shape. Same problem, same proof, one identifier changed:
`read_over_write_same` → `unknown rule` / `invalid`; `arrays_idx` → `valid`.

Detail moved to [`../notes/121-portable-evidence.md`](../notes/121-portable-evidence.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | `3a509de54` | Carcara HAS array rules: `check_alethe` gains `arrays_idx`/`arrays_row` under Carcara's semantics, `prove_qf_abv_unsat_alethe` emits `arrays_idx` instead of a name Carcara rejects, and `portable_artifact` decides Alethe portability from the artifact's rule vocabulary rather than its variant. Six guards, each deletion killing exactly one test. |
| 2026-08-21 | `4b0f001c7` | Built Carcara for the first time and ran the crosscheck suite: **5 of 79 tests failed**. Four hand-wrote stale `!fn_app_*` ids into the problem (fixed by reading them from the proof); the fifth found `bv_poly_simp` checked by neither checker. Adds the shipped ROW-same proof's Carcara acceptance, its negative control, and tamper rejection in both checkers. |
| 2026-08-21 | `f9ccdcb9d` | `alethe_portability_probe`: the first committed tool behind the "externally checkable" figure, plus the per-`ArrayAxiomKind` census showing the array-axiom family unreachable at every rung and why. |
