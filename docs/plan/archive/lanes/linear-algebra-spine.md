# Lane: linear-algebra-spine — deepen the ADR-0603 linear-algebra spine over the constructed rationals

<!-- plan-section: lane-status -->

**`WIP`, linear-algebra-spine, 2026-08-31.** Step 0 (mandatory before
building) found that the task brief's three candidate rungs — determinant
multiplicativity, invertibility, `Ax=b` solvability, all at fixed small `n`
— were ALREADY LANDED at `n = 2` in `rat_prelude/matrix.rs` (`det2_mul`,
`inv2_*`, `cramer2_*`), before this lane touched anything. The genuine gap:
`matrix.rs`'s inverse family used four raw `Rat` scalars, never
`matrix_n.rs`'s general `Nat → Nat → Rat` `matMul`/`matId` encoding — two
disconnected islands — and only ONE direction of invertibility (`A⁻¹·A = I`)
was proven at all; `A·A⁻¹ = I` was not, only its unscaled cousin
`A·adj(A) = det(A)·I`.

Landed: `Rat.matInv2` (`rat_prelude/matrix_invertible.rs`, new module, 11
declarations) — a genuine `Definition` over the general matrix encoding, plus
BOTH directions of invertibility stated through `Rat.matMul`/`Rat.matId` at
every `(i,j)` entry. `Rat.matInv2_matMul_*` (A⁻¹·A = I) bridges the existing
`inv2_*` family into the general encoding; `Rat.matMul_matInv2_*` (A·A⁻¹ = I)
is the genuinely new direction, built by pulling `invD` out of each product
term to match the existing (unscaled) `mul_adj2_*` family, then scaling by
`mul_inv_cancel_of_ne_zero` (diagonal) or `mul_zero` (off-diagonal). Row 2:
none (ADR-0716). Row 3: the ADR-0825 collapse, `Rat.matInv2_example`. All 11
declarations measured axiom-free from the kernel.

A bug (two `rsymm` calls with reversed `(a,b)` arguments) was found and fixed
by the mandatory bisect-by-toggling-declarations method — isolated to exactly
one of the eight entry theorems before the fix, by rebuilding the whole `rat`
prelude and testing after each toggle.

New: ADR-1040
(`docs/research/09-decisions/adr-1040-both-sided-2x2-invertibility-bridges-the-fixed-size-and-symbolic-matrix-families.md`),
two facts (`F:rat-matinv2-matmul-top-left`, `F:rat-matmul-matinv2-top-left`),
a curriculum-doc update (LA-1 section), and a new test file
(`matrix_invertible_tests.rs`: axiom-footprint sweep, a statement-shape
check, a discriminating eval-example control, and a negative control showing
the `det ≠ 0` hypothesis is load-bearing — the unrestricted claim is FALSE,
not merely unprovable, at a singular matrix).

`unnamed_but_live_declarations` in the shared `rat_prelude_tests.rs` was
updated in the same commit as the 11 new declarations, per the standing rule
`every_rat_declaration_is_checked_and_axiom_free` enforces.

Holdout isolation: `scripts/check-autogenesis-holdout-isolation.py` run
before starting and after landing — `held_out=146, references=0,
verdict=PASS` both times (this lane never touched `artifacts/autogenesis/`).

Not attempted: general-`n` determinant, invertibility, or `Ax=b` solvability
(remain open, `docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
LA-1/LA-2/LA-3). A Mathlib reader would correctly say this lane covers one
fixed dimension (`n = 2`) of invertibility, not general linear algebra.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `961e65b80` | `Rat.matInv2` and both-sided 2×2 invertibility, bridged into `matMul`/`matId` (ADR-1040). |
