# Lane: group-category — the `Sigma` residue of W3-3 (ADR-1620's three blocked items)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, group-category, 2026-09-05).** ADR-1620 ended with
one sentence — "the layer this kernel is missing is Σ, not universes and not
`Quot.sound`" — and named three constructions it blocked. ADR-1613 landed
`Sigma`, `PSigma` and `Subtype`. **All three came back**, 25 declarations, every
one with an empty `Kernel::axiom_footprint` ([ADR-1626](../../research/09-decisions/adr-1626-the-layer-that-was-missing-was-sigma-and-three-blocked-constructions-came-back-together.md)):

1. `CatS.grp : CatS.CategoryLarge` — objects `AlgS.Group`, hom-family
   `Subtype (G.carrier -> H.carrier) (CatS.IsGrpHom G H)`. `CatS.mon` beside it.
2. `CatS.forgetGrpMon : CatS.FunctorLarge` over `AlgS.Group.toMonoidS`, with
   `CatS.forgetGrpMon_isFunctor`.
3. `CatS.natPtAlg_isInitial : CatS.IsInitialLarge CatS.ptAlg CatS.natPtAlg
   CatS.natMed` — ℕ initial among pointed unary algebras, whose objects are the
   `Sigma` triple `(N, z, s)`.

**Which half of the ADR-1613 family each site needs is decided by LEVELS, not
taste.** A hom must be `Sort 1`; `Subtype.{1}` lands at `Sort (max 1 1) = Sort 1`
and `Sigma.{u,v}` at `Sort (max u v + 1)`, one universe too high. An object's
second component is data, not a proof, so there it must be `Sigma`, and that is
what puts the objects at `Sort 2`.

**Setoid cost per bundled-hom category: ONE new proof and three one-line
liftings.** `compCongr` is `equivTrans` of the carried congruence with the
hypothesis — the exact step ADR-1620 measured as impossible for an unbundled
hom-family. `idL`, `idR` and `assoc` are **free**, because
`Subtype.val (Subtype.mk f h)` ι-reduces so both sides of each law are the same
function. The `Eq`-flavoured counterfactual does not exist at all: it would need
`Eq` between functions, i.e. `funext`. No evidence to reopen ADR-1595.

**Universe findings.** All three new categories need `CategoryLarge`, not
`Category` (objects at `Sort 2`), pinned in both directions.
`CatS.FunctorLarge` is a **fourth** record at `Sort 3` — the same seven-field
list at `l1 := 2`, `l2 := 3`, because `CatS.Functor`'s `src`/`tgt` are
`CatS.Category`-typed and a record's field types are fixed at declaration. The
ADR-1495 guard fired exactly once, on the `Sort 2` control for that record, with
its positive twin at `Sort 3` in the same test. **Nothing here was blocked by
the guard.**

**Did not land.** `Int.Characterization.initial` is still not a `CatS.IsInitial`
instance, and the reason has changed: a ℤ-structure is a quadruple subject to
two laws, so its object type needs a `PSigma`/`Subtype` mixture over a `Sigma`
at a level nobody has measured. Scoped, not blocked. The discrete category also
did not land, for ADR-1620's unchanged reason (`Eq` is `Prop`, no cumulativity,
needs a `Sort 1` identity inductive); it stays cheap and out of scope.

Gates run, each with a nonzero count: `category_setoid` 29 passed (14 pre-existing
+ 15 new), `structures_setoid` 18, `first_iso` 6, `sigma` 11, all exit 0. The
three pre-existing `F:cats-*` facts pinned a count of 14 and were **recounted**
from the suite's own output, not incremented.

<!-- plan-section: landed-changes -->

| 2026-09-05 | group-category | `CatS.grp` and `CatS.mon`: the category of groups, morphisms bundled through `Subtype` (ADR-1626) |
| 2026-09-05 | group-category | `CatS.forgetGrpMon`: the forgetful functor `Grp → Mon` as a `CatS.FunctorLarge`, laws proved |
| 2026-09-05 | group-category | `CatS.natPtAlg_isInitial`: ℕ is initial among pointed unary algebras, objects a `Sigma` triple |
