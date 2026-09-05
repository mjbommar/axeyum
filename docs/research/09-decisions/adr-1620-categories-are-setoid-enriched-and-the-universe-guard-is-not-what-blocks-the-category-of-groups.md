# ADR-1620: categories are setoid-enriched, and the universe guard is not what blocks the category of groups

Status: proposed
Date: 2026-09-04
Lane: `categories-setoid`
Roadmap: W3-3 (categories, functors, natural transformations — reviewer 09.4)

Index-summary: `CatS.*` lands roadmap W3-3 — **61 declarations**
(three records, four category instances, two functor instances, five
predicates, ten theorems, and their constructors/recursors/selectors), every
one with an empty `Kernel::axiom_footprint`, no `funext`, no `Quot.sound`. The
setoid cost is again **zero, and this time it is exactly zero by
construction**: `CatS.ofMonoid` — a monoid delooped to a one-hom-family
category — is filled by *twelve of `M`'s own fields under dummy object
binders*, `compCongr` by `M.opCongr` and `idL`/`idR`/`assoc` by
`M.identL`/`identR`/`assoc`, with **not one new proof obligation**. Two
universe findings correct earlier phrasing. (1) ADR-1609's "no record can hold
another record" is a statement about **levels per `FieldKind`**, not about
records: `CatS.Functor` holds two `CatS.Category` fields and admits, because
`CatS.Category : Sort 2` is exactly the level `FieldKind::CarrierSort`
eliminates at. (2) **The universe layer is not what blocks the category of
groups.** `CatS.CategoryLarge` — the SAME twelve-field list at objects
`Sort 2`, record `Sort 3`, with exactly one `FieldKind` flipped — takes
`AlgS.Group` as its `obj`, read from the kernel by
`CatS.grpIndiscrete.obj ≡ AlgS.Group`. What blocks it is the **hom-family**:
a morphism of groups is a function *plus* two proofs, and there is no `Sigma`
and no `Subtype` (ADR-1595). The honest content lands unbundled
(`CatS.IsGrpHom` + `isGrpHom_id` + `isGrpHom_comp`), one `Sigma` from the
bundle. Likewise `Nat.Peano.initial` and `Int.Characterization.initial` are
**not** recovered as `CatS.IsInitial` instances, for the same reason and not a
universe one: their objects are triples and quadruples.
Index-status: proposed

## Context

The 09 (category theory) persona review
([`docs/math-department/09-category-theory.md`](../../math-department/09-category-theory.md))
found "no category theory as a subject" and "quite a lot of category theory
here", and set five items in priority order. Items 1–3 landed on 2026-09-04:
item 3 (the morphism-equality discipline) was answered by
[ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) —
setoid-enriched, decided by measurement — and items 1–2 by
[ADR-1610](adr-1610-name-the-universal-properties.md), which named
`Nat.Peano.initial` and `Int.Characterization.initial` and wrote the
four-part
[universal-property template](../08-planning/universal-property-template.md).

ADR-1610 deliberately built **no** `Category`/`Functor` layer, and gave a
reason with a revisit condition: "without a settled morphism-equality
discipline across *every* future category … an abstraction built now would be
re-derived once that discipline is chosen". ADR-1595 settled the discipline.
This ADR is the report from building the layer over it.

## Decision

**Build the category layer setoid-enriched, mirroring `AlgS` one level up, and
keep the bundled record and the unbundled predicate as two separate things.**

A `CatS.Category` is a twelve-field record:

| field | index | what it is |
|---|---|---|
| `obj` | 0 | the objects, a `Sort 1` |
| `hom` | 1 | `obj -> obj -> Sort 1` |
| `homEquiv` | 2 | `forall a b, hom a b -> hom a b -> Prop` |
| `homRefl` / `homSymm` / `homTrans` | 3–5 | the hom-setoid's three laws |
| `id` | 6 | `forall a, hom a a` |
| `comp` | 7 | `forall a b c, hom b c -> hom a b -> hom a c` |
| `compCongr` | 8 | **the one congruence**, the analogue of `AlgS.Magma.opCongr` |
| `idL` / `idR` | 9–10 | the unit laws, up to `homEquiv` |
| `assoc` | 11 | `(h∘g)∘f ~ h∘(g∘f)`, up to `homEquiv` |

This is the `AlgS.*` discipline verbatim, one level up: four
equivalence-infrastructure fields plus one congruence per operation, and every
law stated with the record's own relation in place of `Eq`. The
`FieldSpec`/`declare_record` machinery `Alg.*` and `AlgS.*` already share
builds it unchanged — **nothing was added to `structures.rs`.**

The associativity orientation is `(h∘g)∘f ~ h∘(g∘f)` and not its mirror,
because that is the orientation `AlgS.Monoid.assoc` already has, which is what
lets `CatS.ofMonoid` supply it verbatim. The composition order is
`comp a b c g f = op g f` for the same reason (`identL`/`identR` then fill
`idL`/`idR` with no work). Both are pinned by evaluation tests that refuse the
swapped twin.

## Measurement 1: the setoid cost is zero, and this time by construction

Every algebra lane since ADR-1595 has reported the setoid cost, because
ADR-1595 is reversible on that evidence. ADR-1588 measured seven extra fields
at `CommRing`; ADR-1595 measured three one-line obligations for the first
isomorphism theorem; ADR-1609 measured one field per structure for modules and
subgroups, and found the polynomial ring *unreachable* over `Eq`. This lane's
number is **zero**, and it is zero for a reason worth stating.

`CatS.ofMonoid A M` deloops an `AlgS.Monoid` into a category with objects `A`
and hom-family constantly `M.carrier`. Its twelve constructor arguments:

| category field | supplied by |
|---|---|
| `obj` | the parameter `A` |
| `hom` | `fun _ _ => M.carrier` |
| `homEquiv` | `M.equiv` |
| `homRefl` / `homSymm` / `homTrans` | `M.equivRefl` / `M.equivSymm` / `M.equivTrans` |
| `id` | `M.e` |
| `comp` | `M.op` |
| `compCongr` | **`M.opCongr`** |
| `idL` / `idR` | `M.identL` / `M.identR` |
| `assoc` | `M.assoc` |

Eight of the twelve are a bare selector under two, three or four dummy object
binders. **Not one new proof term was built for this instance.** The five
fields a setoid-enriched category carries that an `Eq`-flavored one would get
free — `homEquiv`, its three laws, and `compCongr` — are precisely the five
`AlgS` already carries, so they arrive pre-discharged at the first instance.

The counterfactual runs the way ADR-1609's polynomial ring did: over `Eq`,
`CatS.ofMonoid` would need `Eq (comp (id b) f) f` for the unit law, and a
monoid whose equality is a *defined* relation (`CReal`, `AlgS.Hom.quotient`'s
coarsened `equiv`, `AlgS.Poly.equiv`) has no such theorem. The `Eq`-flavored
delooping does not exist for the monoids this library actually has.

**No evidence to reopen ADR-1595.**

## Measurement 2: what the one-universe-per-`FieldKind` rule does and does not forbid

`declare_record` assigns each field's selector an elimination level by its
`FieldKind` — `CarrierSort → l2`, `Data → l1`, `Law → l0` — and ADR-1609
recorded the consequence as "no record can hold another record (`FieldSpec`
fixes one universe per `FieldKind`)". Both halves of that were measured here,
and the phrasing is too strong.

### 2a. A record CAN hold a record

`CatS.Functor` has fields `src : CatS.Category` and `tgt : CatS.Category`.
`CatS.Category : Sort 2`, and `Sort 2` is exactly `l2` — the level
`FieldKind::CarrierSort` already eliminates at. Tagging those two fields
`CarrierSort` gives their selectors the right motive level and the record
admits at `Sort 2`, with the `Sort 1` control refused as usual. Rendered from
the kernel:

```text
CatS.functor_isFunctor :
  (F : CatS.Functor) ->
    CatS.IsFunctor (CatS.Functor.src F) (CatS.Functor.tgt F)
                   (CatS.Functor.obj F) (CatS.Functor.map F)
```

What is actually fixed is the level **per kind**, not "records cannot nest". A
record-typed field lands on the kind that already eliminates at `l2`. ADR-1609's
module obstruction was real for the shape it hit, but the general statement
does not follow from it, and a future lane should re-measure rather than
inherit it. (This is the standing rule from the Gotchas: *verify a blocker
still exists before treating it as one, including a blocker this repository's
own documents name*.)

### 2b. The same field list builds two categories at two levels

`CatS.CategoryLarge` is `category_fields` again with `l1 := 2`, `l2 := 3` and
**one `FieldKind` flipped**:

| record | `obj` field | its type's level | kind | `hom` field | its type's level | kind | record at |
|---|---|---|---|---|---|---|---|
| `CatS.Category` | `Sort 1` | 2 | `CarrierSort` | `obj -> obj -> Sort 1` | 2 | `CarrierSort` | `Sort 2` |
| `CatS.CategoryLarge` | `Sort 2` | 3 | `CarrierSort` | `obj -> obj -> Sort 1` | 2 | `Data` | `Sort 3` |

The `hom` field's type sits at level 2 in both records; what moves is the
object level, so the *same* type changes which kind it belongs to. Both levels
are read back from the kernel by `def_eq` against `Sort 2` / `Sort 3` **in
both directions** (each must be the one and not the other), so a level drift
fails the gate rather than passing quietly.

### 2c. The guard's rejection, verbatim

The ADR-1495 constructor-field guard fires on field 0 and is captured with a
positive twin in the same test:

```text
rejection at Sort 1: ConstructorFieldUniverseTooBig {
    inductive: NameId(…), ctor: NameId(…), field_index: 0 }
```

`obj : Sort 1` is a field whose *type* lives at level 2, so a record at `Sort 1`
would make `Sort 1` a retract of an inhabitant of `Sort 1`. The same twelve
fields at `Sort 2` admit. This is the guard working exactly as ADR-1495
intended, and it is not what blocks anything below.

## Measurement 3: what actually blocks the category of `AlgS.Group`s

Not universes. `CatS.grpIndiscrete : CatS.CategoryLarge` has `obj` reducing to
`AlgS.Group`, read from the kernel:

```text
CatS.grpIndiscrete.obj  ==  AlgS.Group        (def_eq holds)
CatS.grpIndiscrete.obj  ==  AlgS.Monoid       (def_eq REFUSED)
```

So the objects of the category of groups are expressible today. The
obstruction is the **hom-family**. A morphism `G ⟶ H` is a function
`G.carrier -> H.carrier` **together with** a proof it respects the two
`equiv`s and a proof it carries `G.op` to `H.op`; `hom G H` must be a *type*,
and this kernel has no `Sigma` and no `Subtype` (both verified ABSENT in
ADR-1595, and re-verified here — the logic prelude has `Exists` but no
`Sigma`, `Subtype`, `Prod`, `Unit` or `Empty`).

Two escapes were checked and both fail, for reasons worth recording so the
next lane does not re-derive them:

1. **`hom G H := G.carrier -> H.carrier` (all functions).** `compCongr` is then
   *false*: from `g ~ g'` and `f ~ f'` pointwise, deriving
   `g (f a) ~ g' (f' a)` needs `g'` to respect `G.equiv`, which an arbitrary
   function does not. The congruence field is exactly the one the setoid
   enrichment adds, and it is exactly the one that fails.
2. **`homEquiv f g := forall a b, G.equiv a b -> H.equiv (f a) (g b)`** (the
   respectful relation, whose *diagonal* is "f is congruent"). This is a
   partial equivalence: symmetric and transitive, but `homRefl` is precisely
   the property being encoded, so it cannot be a field. A PER-enriched record
   — dropping `homRefl` and requiring `id` and `comp` to preserve totality —
   would work and is the standard constructive treatment; it is deferred, not
   refuted (see Consequences).

So the category of groups lands **unbundled**, in the style ADR-1609 chose for
`AlgS.Module.IsModule`:

```text
CatS.IsGrpHom : (G H : AlgS.Group) -> (G.carrier -> H.carrier) -> Prop
CatS.isGrpHom_id   : (G : AlgS.Group) -> CatS.IsGrpHom G G (fun a => a)
CatS.isGrpHom_comp : … -> CatS.IsGrpHom G H f -> CatS.IsGrpHom H K g
                        -> CatS.IsGrpHom G K (fun a => g (f a))
```

Those two theorems *are* the identity and composition laws of the category of
groups. Everything except the bundling is here; the bundling is one `Sigma`
away, and `Sigma` is a kernel-surface decision of its own, not this ADR's.

## Measurement 4: universal properties, and why ADR-1610's two instances are not recovered

`CatS.IsInitial` follows the universal-property template exactly: the
mediating map is **given** as data (`med : forall b, C.hom a b`), not
extracted from an `Exists` — template part 2, "computed, not extracted" — and
uniqueness is stated up to the category's own `homEquiv`, which is the
strongest form available without `funext`:

```text
CatS.IsInitial C a med  :=  forall b (g : C.hom a b), C.homEquiv a b (med b) g
```

`CatS.initial_unique` is then the argument ADR-1610's two carriers each make
by hand, made once:

```text
CatS.initial_unique :
  (C : CatS.Category) -> (a : C.obj) -> (medA : ∀ x, C.hom a x) ->
  (b : C.obj) -> (medB : ∀ x, C.hom b x) ->
  CatS.IsInitial C a medA -> CatS.IsInitial C b medB ->
    And (C.homEquiv a a (C.comp a b a (medB a) (medA b)) (C.id a))
        (C.homEquiv b b (C.comp b a b (medA b) (medB a)) (C.id b))
```

**`Nat.Peano.initial` and `Int.Characterization.initial` are not instances of
it**, and the reason is not the universe guard. An object of "pointed unary
algebras" is a triple `(N, z, s)` and an object of `ℤ`-structures a quadruple
`(R, e, up, down)`; `CatS.Category.obj` and `CatS.CategoryLarge.obj` are each a
single `Sort`, and forming the type of such tuples needs the same missing
`Sigma` as the hom-family above. `CatS.CategoryLarge` would take the *carriers*
`N` as objects, but not the algebra structures.

This is the honest answer to the reviewer's item 5, and it is the same answer
twice: **the layer this kernel is missing is Σ, not universes and not
`Quot.sound`.**

## What landed

61 declarations under `CatS`, all with an empty `Kernel::axiom_footprint`:

| group | declarations |
|---|---|
| records | `CatS.Category` (12 fields), `CatS.CategoryLarge` (12), `CatS.Functor` (7), with `mk`/`rec`/selectors |
| category instances | `indiscrete`, `ofMonoid`, `largeIndiscrete`, `grpIndiscrete` |
| functor instances | `idFunctor`, `ofMonoidHom` |
| predicates | `IsFunctor`, `IsNat`, `IsInitial`, `IsTerminal`, `IsGrpHom` |
| theorems | `functor_isFunctor`, `isFunctor_id`, `isFunctor_comp`, `isNat_id`, `isNat_ofMonoid`, `initial_unique`, `indiscrete_isInitial`, `indiscrete_isTerminal`, `isGrpHom_id`, `isGrpHom_comp` |

Three of the instances are worth a sentence each.

- **`CatS.indiscrete A`** is the trivial/indiscrete control: exactly one
  morphism between any two objects — *up to the hom-equivalence*, since
  `homEquiv` is constantly `True`. That is a quotient statement made with no
  quotient, which is what ADR-1595's route buys.
- **`CatS.ofMonoid`** is the delooping and the cost measurement above. Its
  functoriality partner `CatS.ofMonoidHom` turns a monoid homomorphism into a
  `CatS.Functor` whose three functoriality laws *are* the homomorphism's three
  laws. This is the shape a forgetful functor would take.
- **`CatS.isNat_ofMonoid`** is the one non-trivial natural transformation: a
  natural transformation between two deloopings is exactly an **intertwiner**
  `n` with `n · h x ~ h' x · n`, and the naturality square is that condition,
  so the theorem is the hypothesis applied.

A **discrete** category (only identities) did NOT land, and the reason is
recorded rather than glossed: `hom a b` must be `Sort 1`-valued, `Eq a b` is
`Prop = Sort 0`, and this kernel has no cumulativity, so the discrete category
needs a `Sort 1` identity family declared as a new inductive. That is cheap and
was left out of scope; the indiscrete category is the control that landed.

## The forgetful projections are still not functors, and why

The reviewer's item 4 asks for "the existing forgetful projections
`AlgS.CommRing.toCommGroupS` etc. as the first functors". They cannot be, and
the reason is measurement 3 rather than anything about functors:
`toCommGroupS : AlgS.CommRing -> AlgS.CommGroup` is a map of *objects*, and a
functor needs a source and target **category** whose hom-families are the
homomorphisms. Those hom-families are the ones that need `Sigma`. So this ADR
delivers the functor *shape* over categories that do exist
(`CatS.ofMonoidHom`, `CatS.idFunctor`, `CatS.isFunctor_comp`) and records the
forgetful functors as blocked on the same one thing.

## Consequences

- **The layer is stated over `AlgS.Monoid` and `AlgS.Group` only**, so it lands
  at the `AlgS` build position in `build_nat_prelude_uncached`, alongside
  `AlgS.Poly.*`, `AlgS.Module.*` and `AlgS.Subgroup.*`. Its names are
  deliberately not threaded into `NatPrelude`, for the reason `AlgS.Poly.*`
  gives: widening `StructuresSExtraNames` changes a struct `axeyum-py`'s
  generated field registry mirrors.
- **`CatS.IsFunctor` exists as a predicate alongside the `CatS.Functor`
  record** because composing two records would require `F.tgt` and `G.src` to
  be *propositionally equal categories* and then transporting along an `Eq` at
  `Sort 2`. `CatS.functor_isFunctor` joins the two. Any future lane adding a
  second bundled layer should expect the same fork.
- **Products and coproducts (roadmap W3-4, reviewer item 5) are now scoped, not
  blocked.** A product of two objects is a third object plus two projections
  plus a mediating map given as data — the same shape `CatS.IsInitial` already
  has and expressible with no `Sigma`, since the object is a *value* of
  `C.obj`, not a tuple type. The concrete instances the reviewer wants
  recovered (`CPoint` as ℝ×ℝ, list append as a free monoid) will each need
  their own category first.
- **A PER-enriched variant is the next thing to try** if the category of groups
  is wanted before `Sigma`: drop `homRefl`, take
  `homEquiv f g := ∀ a b, G.equiv a b → H.equiv (f a) (g b)` conjoined with the
  two `op`-preservation directions (symmetric by construction, transitive
  through `opCongr`), and add totality obligations on `id` and `comp`. That is
  a *different record*, not a change to this one, and it should be measured
  against the `Sigma` route rather than assumed cheaper.
- **ADR-1609's "no record can hold a record" should be read as scoped to the
  shape it measured.** This ADR does not supersede it — the module obstruction
  it reports is real — but the general phrasing is corrected here.

## Alternatives considered

- **Wait for `funext`.** Rejected by ADR-1595 on measurement, and this lane
  adds a fourth data point: the layer is not merely reachable over setoids, its
  first instance costs nothing, and the `Eq`-flavored delooping would not exist
  for the monoids this library has.
- **One record with a universe parameter instead of `Category` and
  `CategoryLarge`.** `declare_record` takes its levels as arguments, so the
  two records share one field list and cost one extra `FieldKind` argument.
  A universe-polymorphic record would need `declare_record` to thread `uparams`
  through every selector, which is a change to a file three other spines share
  — deferred until a third level is actually wanted.
- **Bundle the natural transformation as a record.** Rejected for the same
  reason `IsFunctor` is a predicate: it would need equality of categories and
  of functors.
- **Name the namespace `AlgS.Cat`** rather than a new `CatS` root, to avoid
  registering a namespace in `scripts/validate-facts.py`'s
  `KERNEL_THEOREM_RE`. Rejected: burying category theory inside the algebra
  namespace is the reviewer's original complaint (results stated concretely and
  not connected), and registering a root is a one-token change that the regex
  exists to make deliberate.

## Evidence

| what | where |
|---|---|
| the layer | `crates/axeyum-lean-kernel/src/nat_prelude/category_setoid.rs` |
| build position | `crates/axeyum-lean-kernel/src/nat_prelude.rs`, at the `AlgS` position |
| tests (14) | `nat_prelude::category_setoid::category_setoid_tests::*` |
| facts | `F:cats-initial-unique`, `F:cats-isfunctor-comp`, `F:cats-isnat-ofmonoid` |

The suite reads the kernel for every claim: admission, `axiom_footprint`,
`Declaration` kind, rendered types, both universe levels **in both
directions**, the `ConstructorFieldUniverseTooBig` refusal with its positive
twin, evaluation of every definition against a discriminating negative twin,
and a four-entry mutation table:

| # | mutation (a small term) | expected | positive twin in the same test |
|---|---|---|---|
| M1 | the functor's morphism map becomes a constant `fun a b f => n` | REFUSED | `fun a b f => f` admits |
| M2 | the initial-object round trip is built twice from `medA b` | REFUSED | the `medB a ∘ medA b` round trip admits |
| M3 | the naturality square's right-hand side becomes `id b` | REFUSED | `f ∘ id a` admits |
| M4 | the composite homomorphism becomes `f₁ ∘ f₁` | REFUSED | `f₂ ∘ f₁` admits |

## Related

- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) — the
  discipline this layer is built over, and the standing reversal condition it
  set (still unmet).
- [ADR-1610](adr-1610-name-the-universal-properties.md) — named the two
  universal properties and deferred this layer; the deferral's condition is
  what this ADR discharges.
- [ADR-1609](adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md)
  — the three obstructions it reported, one of which is corrected in
  measurement 2a.
- [ADR-1495](adr-1495-abstraction-over-structures-is-already-expressible-the-gap-is-surface.md)
  — the constructor-field universe guard measured verbatim here.
- [ADR-1588](adr-1588-a-setoid-flavored-alg-spine-for-creal.md) — the `AlgS`
  spine whose field discipline this mirrors.
- [universal-property template](../08-planning/universal-property-template.md)
  — parts 1, 2 and 4 are what `CatS.IsInitial` and `CatS.initial_unique`
  implement generically.
