# Lane: categories-setoid — roadmap W3-3, the setoid-enriched category layer

<!-- plan-section: lane-status -->

**Lane block (`landed`, categories-setoid, 2026-09-04).** `CatS.*` lands
roadmap W3-3 (ADR-1620): **61 declarations**, every one with an empty
`Kernel::axiom_footprint`, no `funext`, no `Quot.sound`. Three records
(`CatS.Category` at `Sort 2`, `CatS.CategoryLarge` at `Sort 3`,
`CatS.Functor`), four category instances, two functor instances, five
predicates, ten checked theorems.

**The setoid cost is zero, by construction.** `CatS.ofMonoid` — a monoid
delooped into a category — is filled by twelve of `M`'s own fields under dummy
object binders (`compCongr` by `M.opCongr`, `idL`/`idR`/`assoc` by
`M.identL`/`identR`/`assoc`), with no new proof term. The five fields the
setoid enrichment adds are the five `AlgS` already carries, so they arrive
pre-discharged. Over `Eq` the instance would not exist for a monoid whose
equality is a defined relation. No evidence to reopen ADR-1595.

**Two universe findings, both correcting earlier phrasing.** (1) ADR-1609's
"no record can hold another record" is about **levels per `FieldKind`**, not
records: `CatS.Functor` holds two `CatS.Category` fields and admits, because
`CatS.Category : Sort 2` is exactly the level `FieldKind::CarrierSort`
eliminates at. (2) **Universes are not what blocks the category of groups** —
`CatS.grpIndiscrete.obj` reduces to `AlgS.Group`, read from the kernel. The
ADR-1495 guard's rejection at `Sort 1` is
`ConstructorFieldUniverseTooBig { field_index: 0 }`, with the same field list
admitting at `Sort 2`.

**Sized negatives.** The hom-family of the category of groups needs `Sigma`: a
morphism is a function plus two proofs, and there is no `Sigma`/`Subtype`
(ADR-1595, re-verified). Two escapes were checked and both fail — all
functions makes `compCongr` false, and the respectful relation is only a
partial equivalence, so `homRefl` cannot be a field. The honest content landed
unbundled (`CatS.IsGrpHom`, `isGrpHom_id`, `isGrpHom_comp`). For the same
reason — not universes — `Nat.Peano.initial` and `Int.Characterization.initial`
are **not** recovered as `CatS.IsInitial` instances: their objects are triples
and quadruples. The forgetful projections are still not functors, blocked on
the same one thing. A **discrete** category did not land: `hom` must be
`Sort 1`-valued, `Eq` is `Prop`, and there is no cumulativity, so it needs a
new `Sort 1` identity inductive — cheap, out of scope.

**Next.** W3-4 (products and coproducts) is now scoped rather than blocked: a
product is an object plus two projections plus a mediating map given as data,
the shape `CatS.IsInitial` already has and expressible with no `Sigma`. A
PER-enriched record is the route to the category of groups before `Sigma`, and
should be measured against the `Sigma` route rather than assumed cheaper.

<!-- plan-section: landed-changes -->

| 2026-09-04 | categories-setoid | `CatS.*`: 61 axiom-free declarations — setoid-enriched categories, functors, naturality, initial objects; setoid cost zero; the category of groups blocked on `Sigma`, not universes (ADR-1620) |
