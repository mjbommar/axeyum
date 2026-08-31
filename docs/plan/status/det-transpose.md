# Lane: det-transpose

<!-- plan-section: lane-status -->

Status: **done** (2026-08-31). `Rat.det_transpose` — `det (matTranspose A) n =
det A n` at a symbolic dimension — is admitted axiom-free, together with
cofactor expansion along the first COLUMN. Five declarations, all admitted on
the first attempt. Three of ADR-1120's four determinant laws are now proved;
only multiplicativity remains, and ADR-1135 established that it is blocked on
an aggregate type this kernel does not have rather than on effort.

**ADR-1185's closing sizing is corrected.** It said transpose invariance was
"strictly downstream" of `Rat.det_row_expansion`. The row law is not used and
cannot be: expansion along a column of `A` IS expansion along a row of `Aᵀ`, so
reaching for it is circular. What it constrains is one summand at a time — the
`p`-th column summand is the `c = 0` slice of the row-`p` expansion — so it
relates each summand to its siblings across `c` and never the sum across `p`.

The column law is nevertheless **cheaper** than the row law, not merely
independent of it: five declarations against twenty. Because one expansion
deletes a row and the other a column, the two exchanges never compete for one
index space, so `matMinor_row_col_comm` is `matSkip_succ_succ` once per axis
with **no `Nat.ble` hypothesis and no case split**. The route has no
`laplaceSummand`, no `unskip`, no `Nat.beq` diagonal guard and no
`sumRange_congr_lt`, and declares no new `Definition` at all.

## Landed changes

| change | where |
| --- | --- |
| `Rat.matMinor_row_col_comm`, `Rat.det_minor_row_col_comm`, `Rat.det_col_expansion`, `Rat.matMinor_transpose`, `Rat.det_transpose` | `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs` |
| the five names, in both inventories | `crates/axeyum-lean-kernel/src/rat_prelude.rs`, `.../rat_prelude_tests.rs` |
| `det_transpose_and_the_column_expansion_evaluate_and_pin_the_sign`, `the_transpose_and_column_statements_quantify_over_matrix_and_dimension` | `.../rat_prelude_tests.rs` |
| `F:rat-det-col-expansion`, `F:rat-det-transpose` | `artifacts/facts/` |
| the route checks, re-runnable | `docs/research/09-decisions/adr-1210-det-transpose-checks.py` |
| ADR-1210 | `docs/research/09-decisions/adr-1210-transpose-invariance-needs-the-column-law-not-the-row-law.md` |

## Measurements

- `cargo test -p axeyum-lean-kernel --lib rat_prelude::` — **156 passed, 0
  failed, 213.70 s**.
- `rat` prelude build, A/B by disabling exactly these five declarations on the
  same machine minutes apart: **14.19 s → 14.57 s**. Four runs on the identical
  tree ranged 13.96–14.57 s, so 0.38 s is an **upper bound within run-to-run
  spread**, not a resolved effect.
- `python3 docs/research/09-decisions/adr-1210-det-transpose-checks.py` — 0
  failures, 22 checks, six negative controls each measured rather than
  asserted.
- `python3 scripts/validate-facts.py` — 2,449 facts, 0 errors.
- `scripts/check-settled-fact-statements.py` — PASS, `unpinned=0`.

## Mutation, both columns

Under the `matSkip` branch swap, **four of the five declarations report
`UnknownConst`** (confounded by `matSkip_succ_succ` failing upstream), so that
probe says nothing about them on the declaration axis — it does falsify four of
the five statements. A second probe was designed: transposing the column
summand's entry index refuses exactly `det_col_expansion` and `det_transpose`,
both naming their own type error, with all 41 other declarations in the file
correctly admitted. But it leaves `det_transpose`'s **statement** true, so its
rejection there is a broken proof rather than a false theorem. Neither probe
covers both declarations on both axes; the pair does.

## Not done, and deliberately

`the_determinant_toolkit_is_axiom_free` still iterates its own hand-maintained
list, so it cannot see a declaration nobody added to it — the defect `CLAUDE.md`
records for `every_creal_declaration_is_checked_and_axiom_free`. Fixing it needs
an environment-derived filter for the names this one file owns, and the `Rat.`
namespace is shared by the whole prelude, so it is a separate task.
