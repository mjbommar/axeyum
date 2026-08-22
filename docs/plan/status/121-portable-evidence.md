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

That mattered to a published number: `Evidence::portable_artifact` reported
*every* `UnsatAletheProof` as externally checkable, so a proof Carcara answers
`invalid` counted toward the "artifact an external checker can read" figure —
the `lia_generic` defect that function's own comment warns about, one level
down. Portability is now decided from the artifact's **rule vocabulary**
(`axeyum_cnf::non_carcara_checked_rules` against a pinned 179-rule list that
excludes `hole`, `lia_generic` and `rare_rewrite`), not from the variant.

**The number did not move, and the measurement says why.** 44 of 281 (15.7%)
before and after: all 44 currently-claimed instances name only rules Carcara
checks, so the published figure was right and is now defensible by a test rather
than by a reading. The 85-instance `unsat-array-axiom` family — 30% of certified
`unsat`, the target this lane was pointed at — is unreachable at every rung, per
instance (`alethe_portability_probe --array-shapes`):

| `ArrayAxiomKind` | instances | share |
|---|---:|---:|
| `ReadCongruence` | 70 | 82.4% |
| `ReadOverWrite` | 8 | 9.4% |
| `StoreShadowing` | 5 | 5.9% |
| `SelectIte` | 1 | 1.2% |
| `StoreIteSelect` | 1 | 1.2% |

- `arrays_idx` reaches **1 of 85**: one certificate is the ROW-same shape, and
  its disequality is inside a BTOR bv1 encoding rather than asserted at top
  level, so the `assume` a proof needs is not a problem assertion. 67 of the 70
  `ReadCongruence` instances share that bv1 head.
- The whole zero-trust Alethe ladder reaches **0 of 85**.
- `eliminate_arrays` then bit-blast reaches **0 of 85**, structurally: array
  elimination rewrites every select-of-store to an `ite` and
  `prove_qf_bv_unsat_alethe`'s fragment has no `Op::Ite` arm. Carcara has no
  `bitblast_ite` either.

So the next real slices, in the order their cost was measured, are: **`Op::Ite`
in the bit-blast Alethe emitter** (unblocks elim→bitblast for the whole family
but needs a Carcara-checkable `ite` treatment — the case split over
`arrays_idx`/`arrays_row`, since Carcara has both branches); **clausification
rules** `not_implies1`/`not_implies2` plus the existing `eq_congruent`, worth the
3 pure-Boolean `ReadCongruence` instances (`arr1.smt2` and two siblings) but
carrying a Lean-column regression risk, since 81 of these 85 currently produce
Lean *reasoning* modules through `UnsatArrayAxiom` and a route change would swap
that for an Alethe cert. Neither is a rule-name fix.

**Open, found and not fixed here.** `bv_poly_simp` (Route 2) is checked by
neither Carcara (`unknown rule`) nor `check_alethe`
(`UnsupportedRule`) — Route 2 is the one Alethe emitter that does not
re-validate its own output, which is why three doc comments could call the rule
"Carcara-valid" unchallenged. It is not on the evidence path.
`PortableArtifact` is not re-exported from `axeyum_solver`, so a consumer can
call `portable_artifact` and cannot name its return type.

QF_ABV dominance audit re-run from a clean `lane-snapshot` tree (`dirty=false`,
sha `35d3fd6b1`): 169/169 audited decided, **85 certified, 85 checked, 85
Lean-checked (81 reasoning / 4 attestation)**, 0 mismatches, 0 audit errors —
per-instance identical to the committed artifact.

<!-- plan-section: landed-changes -->

| 2026-08-21 | `3a509de54` | Carcara HAS array rules: `check_alethe` gains `arrays_idx`/`arrays_row` under Carcara's semantics, `prove_qf_abv_unsat_alethe` emits `arrays_idx` instead of a name Carcara rejects, and `portable_artifact` decides Alethe portability from the artifact's rule vocabulary rather than its variant. Six guards, each deletion killing exactly one test. |
| 2026-08-21 | `4b0f001c7` | Built Carcara for the first time and ran the crosscheck suite: **5 of 79 tests failed**. Four hand-wrote stale `!fn_app_*` ids into the problem (fixed by reading them from the proof); the fifth found `bv_poly_simp` checked by neither checker. Adds the shipped ROW-same proof's Carcara acceptance, its negative control, and tamper rejection in both checkers. |
| 2026-08-21 | `f9ccdcb9d` | `alethe_portability_probe`: the first committed tool behind the "externally checkable" figure, plus the per-`ArrayAxiomKind` census showing the array-axiom family unreachable at every rung and why. |
