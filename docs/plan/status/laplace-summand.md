# Lane: laplace-summand

<!-- plan-section: lane-status -->

**Closed.** `Rat.det_row_expansion` — cofactor expansion along a **general**
row, at symbolic dimension — is admitted axiom-free. That is the second of the
four laws [ADR-1120](../../research/09-decisions/adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md)
named over `Rat.det`, and the one
[ADR-1135](../../research/09-decisions/adr-1135-a-determinant-congruence-is-what-the-absence-of-funext-costs.md)
declined to size.
[ADR-1155](../../research/09-decisions/adr-1155-general-row-expansion-is-one-fubini-once-the-range-is-full.md)
sized it and landed the index and range layers; this lane landed the twenty
declarations of the summand layer and the assembly.
Reasoning: [ADR-1185](../../research/09-decisions/adr-1185-general-row-expansion-closes-and-the-guard-had-to-be-a-recursion.md).

ADR-1155's central prediction held exactly: **no adjacent-swap ladder and no
row antisymmetry.** The proof is ONE induction on the dimension whose step
splits on the row, because the two double sums are the two orders of summation
of one function on the square (`Rat.laplaceSummand`) and `Rat.sumRange_swap` is
the whole reindexing step.

The shape finding worth carrying past this lane: **an index helper a proof will
case-split on must be a structural recursion, not a `Nat.ble` closed form.**
ADR-1155 names `unskip p q := if ble (succ p) q then pred q else q`. That
computes the right function and is unreachable by `Bool.rec`, because reducing
`ble (succ p) (succ c)` **re-creates** `ble p c` — the very scrutinee the split
abstracted away. Declared as a double `Nat.rec` instead, all three rows hold by
ι and the row-`0` identification needs no case split at all.

**Transpose invariance is now strictly downstream.** It expands along a column
of `A`, its inner sums are `matSkip`-reindexed, and filling them to the full
range is the same move — and a column of `A` is a row of `Aᵀ`, which is what
this law now supplies.

## Landed changes

| what | where |
| --- | --- |
| `Rat.unskip` + its three defining equations, `unskip_matSkip`, `beq_matSkip`, `beq_matSkip_left`, `altSign_succ_add` — the summand's index layer | `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs` |
| `Rat.ble_flip_of_false`, `unskip_le`, `unskip_gt`, `matMinor_double_comm_lo/hi`, `det_double_comm_lo/hi`, `mul_perm4` | same file |
| `Rat.laplaceSummand`, `laplaceSummand_rowZero`, `laplaceSummand_rowI`, `laplaceSummand_diag` — ADR-1155's named bulk | same file |
| **`Rat.det_row_expansion`** — the law | same file |
| `the_laplace_summand_layer_computes` (evaluation for the two new `Definition`s) and `det_row_expansion_evaluates_at_every_row_and_pins_the_sign` (the only check here that separates a sign) | `crates/axeyum-lean-kernel/src/rat_prelude/rat_prelude_tests.rs` |
| 20 new names registered in both environment-derived inventories, so kind and axiom footprint are read from the kernel | same file |
| `F:rat-det-row-expansion`, `F:rat-laplace-summand-row-i`, `F:rat-unskip-mat-skip` | `artifacts/facts/` |
| ADR-1185 and its re-runnable numeric checks, including the mutation table's statement column | `docs/research/09-decisions/` |
| `F:rat-int-right-distrib` — a PRE-EXISTING missing `depends_on` edge (`Int.add_mul`), not this lane's, found red by `validate-facts.py` and repaired with `check-fact-depends-derived.py --fix` | `artifacts/facts/` |

## Checks run

- `cargo test -p axeyum-lean-kernel --lib rat_prelude::` — **154 passed, 0
  failed, 224.83 s** (`env -u RUST_MIN_STACK`, so no ambient stack setting is
  carrying it).
- `python3 docs/research/09-decisions/adr-1155-laplace-route-checks.py` — 0
  failures, **re-run rather than inherited**, before any work started.
- `python3 docs/research/09-decisions/adr-1185-laplace-summand-checks.py` — 0
  failures; verified to fail (10 of its 13 checks, exit 1) under the `matSkip`
  branch swap.
- `python3 scripts/validate-facts.py` — exit 0.
- `python3 scripts/check-settled-fact-statements.py` — exit 0, three new pins.
- `python3 scripts/gen-adr-index.py --check` — exit 0, 712 rows.
- Mutation table, **both columns**, in ADR-1185: two mutations
  (`matSkip` branch swap; `unskip`'s `succ` row dropping its `succ`) run in
  this lane's own worktree with `declare_matrix_det` rewritten to REPORT each
  rejection instead of short-circuiting, plus the statement column
  re-simulated in Python.

## What the controls do NOT catch

- **Nine of this lane's twenty declarations are ADMITTED under the `matSkip`
  branch swap with their statements still true**, so that mutation says nothing
  about them. It is the wrong probe for the `unskip` and `Rat`-algebra half of
  the work; mutation B (`unskip`'s `succ` row) covers those, and four
  declarations — `altSign_succ_add`, `ble_flip_of_false`, `mul_perm4`,
  `laplaceSummand_diag` — are untouched by either, correctly, since none
  mentions either definition.
- **No index-layer statement in `matrix_det.rs` separates a sign error**,
  because no sign appears in any of them — ADR-1155 recorded this about its own
  seven. `det_row_expansion_evaluates_at_every_row_and_pins_the_sign` is the
  new one that does.
- Neither mutation probes `Nat.ble`'s guard ORDER inside `matSkip`;
  `Rat.det_eq_det2` remains that discriminator.

## Cost

The `rat` prelude build went **13.15 s → 14.37 s** across the twenty
declarations. ADR-1155's status note records 31.8 s for its own seven; measured
here on the same commit it is 13.15 s, so **that figure was taken under lane
contention and should not be used as a baseline**.
