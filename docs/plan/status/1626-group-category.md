# Lane: group-category — the `Sigma` residue of W3-3 (ADR-1620's three blocked items)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, group-category, 2026-09-05).** ADR-1620 recorded
three things as blocked on one missing kernel feature, and named the feature:
a dependent pair. ADR-1613 landed `Sigma`, `PSigma` and `Subtype` with an
empty axiom footprint. This lane discharges the residue —

1. `CatS.grp`, the category of `AlgS.Group` objects with **bundled** morphisms;
2. a forgetful functor as an actual functor value with its laws proved;
3. `Nat.Peano.initial` recovered as a `CatS.IsInitial` instance in a category
   of pointed unary algebras whose objects are `Sigma` triples.

Status: WIP.

<!-- plan-section: landed-changes -->

| 2026-09-05 | group-category | lane opened for W3-3's `Sigma` residue (ADR-1626) |
