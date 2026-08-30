# Notes: 182-supon-r6

Detail moved out of [`../status/182-supon-r6.md`](../status/182-supon-r6.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The real difficulty is a statement choice, not a technique.** The obvious
invariant — "every fine point is within one coarse width of some coarse
point", `le (P L i') (add (P j i) (D j))` — does *not* close the induction:
each odd step adds a fine width, and that statement cannot see that the widths
halve. Carrying the **fine width on the left** instead,
`le (add (P L i') (D L)) (add (P j i) (D j))`, makes every step exact.

**What rung 6 still owes, precisely.** `meshMax_le_add_of_step_close` takes
`hclose : forall x y, x,y in [a,b] -> le x y -> le y (add x (D j)) ->
le (F y) (add (F x) eps)` as a hypothesis. Instantiating it from `uc_spec` at
the accuracy `expOfModulus` selects is arithmetic about the modulus with **no
mesh geometry left in it**: it compares `D j` (an arbitrary `CReal` width over
`2^j`) against `1/(m k + 1)`, which is where `Nat.lt_pow_size` and an
Archimedean bound on `b - a` enter. Rungs 6b (telescope) and 7
(`regular_of_scaled_cauchy`) are unchanged.

**Not verified by this lane** (they were never exercised, and remain as the
module doc left them): the "constant-multiple corollary already exists in
substance" claim, and the `cauchy_of_abs_diff_le` raw-`(K, proof)`-pair claim.

`creal_prelude_builds`, same box, minutes apart: **103.66 s on `main`**
(snapshot) vs **104.51 s here** — +0.8%, noise, inside the 94–123 band.
