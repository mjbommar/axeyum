# Lane: handelman — the QF_NRA refutations that need a COMBINATION

<!-- plan-section: lane-status -->

**The three `QF_NRA` corpus rows that `nra_product_cert` explicitly declined now
carry a re-derivable certificate, including the one whose exact refutation does
not fit in `i128`** (`DONE`, agent-handelman, 2026-08-20).

`cli__regress1__nl__coeff-unsat`, `cli__regress1__nl__combine` and
`cli__regress1__nl__approx-sqrt-unsat` all shipped as bare `Evidence::Unsat(None)`
— decided, unfalsifiable. Each needs more than one product term, which is
exactly what the two-factor route was written to refuse rather than guess at.
All three now report `real-handelman-unsat certified=true checked=true`.

The producer does not implement a Positivstellensatz search from scratch: it
abstracts every monomial to a fresh real variable and hands the resulting linear
system to the exact Fourier–Motzkin/Farkas engine already in `lra.rs`, then reads
the multipliers back. The checker never runs an LP — it binds each carried atom
to something the query literally asserts and multiplies the polynomials out — so
producer and checker can disagree, which is the property a `fresh == certificate`
re-run does not have.

The interesting one is `approx-sqrt-unsat`'s third disjunct, whose constant is
`2.0000000000000000000000000001`. Its exact refutation needs `(2+k)²`, numerator
`1.6·10^57`, and `Rational` is an `i128` fraction — so no exact `i128` derivation
of that refutation exists and an approximate one is not a certificate. A
certificate atom may therefore carry a **relaxation** `r ≥ 0` and the derivation
uses `nonneg_form(atom) + r`: still implied by the atom, still something the
query licenses, and rounding the constant up to `2.000000000001` puts every
product back inside `i128` with margin. The relaxation is carried and re-derived,
never assumed; only the one disjunct that needs it has a nonzero one, and a test
pins that.

Next on this axis: the equality multiplier basis is degree ≤ 1 and products are
pairwise, which is what the committed corpus needs and no more. A shape needing a
degree-2 multiplier or a triple product will decline rather than approximate.

<!-- plan-section: landed-changes -->

| 2026-08-20 | (pending) | `Evidence::UnsatRealHandelman`: multi-term Handelman/Positivstellensatz refutations for `QF_NRA`, with case splitting over a top-level disjunction and polynomial multipliers on asserted equalities. Certifies the three corpus rows `nra_product_cert` declined by design. 15 guards mutation-checked; 14 kill at least one test, and the fifteenth (the producer's own self-check) kills nothing and is documented as such at the function rather than pretended to be a guard. Three checks that provably could not fail were deleted instead of kept. `NamedPoly` is now shared with `nra_product_cert` rather than reimplemented — two name-keyed polynomial types would be two chances to disagree about what `a*b` means. |
