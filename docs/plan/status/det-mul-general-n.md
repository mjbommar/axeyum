# Lane: det-mul-general-n

<!-- plan-section: lane-status -->

**Status:** in progress — the product law `det (A·B) n = det A n * det B n` at
symbolic `n`, axiom-free, over `Rat.det` (ADR-1120).

Target: `Rat.det_mul`. The product law exists today only at dimension 2
(`Rat.det2_mul`, fact `F:determinant-multiplicative-over-constructed-rationals`).
Route (a) from the brief: multilinearity + alternating in the rows of `A·B`
viewed as combinations of rows of `B`, expanding over a sum indexed by a
function space and killing non-injective index maps with
`Rat.det_row_selection_of_duplicate`. Route (b), Leibniz via permutations, is
not attempted — this kernel has no `Finset`/`List`.

## What landed

(nothing yet — this is the early stub required by the lane protocol)

<!-- plan-section: landed-changes -->

| 2026-09-02 | `docs/plan/status/det-mul-general-n.md` | lane opened |
