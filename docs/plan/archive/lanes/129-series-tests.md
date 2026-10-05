# Lane: series-tests — Spivak Ch 22–23 convergence tests (`creal/series.rs` etc.)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, series-tests, 2026-08-27).** Assessed the
22–23 curriculum row against the theorem inventory before adding anything:
comparison test, dominated convergence, telescoping, and `geomCauchy` were all
already landed and accurately described. **Landed absolute convergence implies
convergence** — `CReal.sumRange_cauchy_of_abs_cauchy` and
`CReal.sumRange_converges_of_abs_converges`, both pure corollaries of the
already-proved `sumRange_cauchy_of_dominated` at `g := abs ∘ f`, kernel-checked
(`creal_prelude_builds`, 17.5s, healthy) and covered by
`every_creal_declaration_is_checked_and_axiom_free`'s environment scan.
Added a soundness-negative control confirming the trusted checker rejects the
reversed (classically false) direction using the real theorem's own proof
value.

Found and corrected two stale curriculum claims: row 22–23's "`CReal.inv`
contained to exactly two declarations" undercounted — the true count along
`geomCauchy`'s dependency chain is **six** (four pre-existing in
`geometric.rs` plus the two in `exponential.rs`); and row 18's "`2 ≤ e ≤ 3`
open" was stale — `CReal.two_le_e`/`CReal.e_le_three`/`CReal.e_le_four` are
already proved. Both corrected in `docs/curriculum/foundational-books/spivak.md`.

Assessed and declined, with reasons sized precisely in the curriculum doc's
new "Postscript III": the **ratio test** (needs a `PosBound`-witnessed
multiplicative form to stay `inv`-free — new construction, not a corollary)
and **`e` irrational** (needs an `n!·e`-integrality argument this development
has no machinery for at all).

Next open goal: build the multiplicative ratio test
(`∀n, le (mul r (f n)) (f (succ n))) → …`, comparison against an `r`-scaled
geometric series) as a genuinely new construction over `geom_sum_bounded`'s
existing shape.

<!-- plan-section: landed-changes -->

| 2026-08-27 | (uncommitted at status-file write time) | `CReal.sumRange_cauchy_of_abs_cauchy` / `CReal.sumRange_converges_of_abs_converges` (absolute convergence implies convergence) plus a soundness-negative control; curriculum rows 18 and 22–23 corrected. |
