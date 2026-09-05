# ADR-1626: the layer that was missing was Σ, and the three blocked constructions came back together

Status: proposed
Date: 2026-09-05
Lane: `group-category`
Roadmap: W3-3 residue (categories, functors, natural transformations — reviewer 09.4), unblocked by W0-5

Index-summary: ADR-1620 ended with one sentence — "**the layer this kernel is
missing is Σ, not universes and not `Quot.sound`**" — and named three
constructions it blocked. ADR-1613 landed `Sigma`, `PSigma` and `Subtype` with
an empty footprint. This ADR is the receipt: **3 of 3 came back**, in one lane,
with **25 new declarations** and an empty `Kernel::axiom_footprint` on every
one. `CatS.grp : CatS.CategoryLarge` has objects `AlgS.Group` and hom-family
`Subtype (G.carrier -> H.carrier) (CatS.IsGrpHom G H)`; `CatS.forgetGrpMon :
CatS.FunctorLarge` is the forgetful functor `Grp → Mon` with its three laws
proved; `CatS.natPtAlg_isInitial` recovers `Nat.Peano.initial` as a
`CatS.IsInitialLarge` instance over a category whose objects are the `Sigma`
triple `(N, z, s)`. **Which half of the family each site needs is decided by
LEVELS, not taste**: a hom-family must be `Sort 1`, `Subtype.{1}` lands at
`Sort (max 1 1) = Sort 1` and `Sigma.{u,v}` at `Sort (max u v + 1)`, one
universe too high — so the morphisms are `Subtype` and the objects, whose
second component is data rather than a proof, are `Sigma`. The setoid cost of a
bundled-hom category is **one new proof and three one-line liftings**:
`compCongr` is `equivTrans` of the bundled congruence with the hypothesis, and
`idL`/`idR`/`assoc` are **free**, because `Subtype.val (Subtype.mk f h)`
ι-reduces so both sides of each law are the same function — the mechanism
ADR-1613 measured at the image group. Two universe findings: every category
here needs `CategoryLarge` (objects at `Sort 2`) and none of them is near the
ADR-1495 guard, and `CatS.FunctorLarge` is a **fourth** record at `Sort 3`
because a record's field types are fixed at declaration — ADR-1620's
measurement 2a one level up, with the `Sort 2` control refused verbatim.
Int.Characterization.initial is NOT recovered, and the reason is now a
quadruple with two laws rather than a missing kernel feature.
Index-status: proposed

## Context

[ADR-1620](adr-1620-categories-are-setoid-enriched-and-the-universe-guard-is-not-what-blocks-the-category-of-groups.md)
built the `CatS.*` layer — 61 declarations, setoid-enriched, axiom-free — and
then spent four measurements establishing what it could *not* build and why.
Its answer was unusually specific, and it named the same cause three times:

1. **The category of groups.** `CatS.grpIndiscrete : CatS.CategoryLarge`
   already had `obj ≡ AlgS.Group`, read from the kernel, so the universe layer
   was not the obstruction. The hom-family was: "a morphism `G ⟶ H` is a
   function `G.carrier -> H.carrier` **together with** a proof …; `hom G H`
   must be a *type*, and this kernel has no `Sigma` and no `Subtype`."
2. **The forgetful functors.** "`toCommGroupS : AlgS.CommRing ->
   AlgS.CommGroup` is a map of *objects*, and a functor needs a source and
   target **category** whose hom-families are the homomorphisms. Those
   hom-families are the ones that need `Sigma`."
3. **`Nat.Peano.initial` as a `CatS.IsInitial` instance.** "An object of
   pointed unary algebras is a triple `(N, z, s)` … forming the type of such
   tuples needs the same missing `Sigma` as the hom-family above."

ADR-1620 checked two escapes from (1) and recorded why each fails, which is the
part that mattered most for this lane:

- **`hom G H := G.carrier -> H.carrier`** (all functions) makes `compCongr`
  *false*: from `g ~ g'` and `f ~ f'` pointwise, `g (f a) ~ g' (f' a)` needs
  `g'` to respect `G.equiv`, which an arbitrary function does not.
- **The respectful relation** `f ~ g := ∀ a b, G.equiv a b → H.equiv (f a) (g b)`
  is only a *partial* equivalence — `homRefl` is precisely the property being
  encoded, so it cannot be a field.

[ADR-1613](adr-1613-dependent-pairs-are-an-ordinary-inductive-and-the-guard-never-refused-them.md)
then landed `Sigma`, `PSigma` and `Subtype` through the ordinary
`add_inductive` gate with zero axioms, and re-tested three *other* blocked
sites, 3 of 3. This ADR re-tests ADR-1620's three, and the count is again
**3 of 3**.

## Decision

**Bundle the morphisms with `Subtype`, bundle the objects with `Sigma`, and let
the levels decide which.** Concretely:

```text
CatS.GrpHom G H := Subtype.{1} (G.carrier -> H.carrier) (CatS.IsGrpHom G H)
CatS.MonHom M N := Subtype.{1} (M.carrier -> N.carrier) (CatS.IsMonHom M N)
CatS.PtAlg      := Sigma.{1,0} (Sort 1) (fun N => Sigma.{0,0} N (fun _ => N -> N))
CatS.PtHom P Q  := Subtype.{1} (P.carrier -> Q.carrier) (CatS.IsPtHom P Q)
```

The choice between the two halves of the ADR-1613 family is **forced, and the
forcing is arithmetic**:

| site | what the pair holds | family | its result level | what the field demands |
|---|---|---|---|---|
| a hom | a function `Sort 1` + a `Prop` | `Subtype.{1}` | `Sort (max 1 1) = Sort 1` | `CategoryLarge.hom : obj -> obj -> Sort 1` ✓ |
| a hom, hypothetically | the same | `Sigma.{0,?}` | `Sort (max u v + 1) ≥ Sort 1`, and the second component is a `Prop`, i.e. `Sort 0`, which `Sigma`'s `β : α → Type v` cannot take | ✗ |
| an object | a carrier `Sort 1` + data | `Sigma.{1,0}` | `Sort (max 1 0 + 1) = Sort 2` | `CategoryLarge.obj : Sort 2` ✓ |

`Subtype` is the *proof-carrying* half and `Sigma` the *data-carrying* half, and
each site has exactly one of those shapes. There was no design freedom here to
spend, which is worth recording because the next lane will face the same fork.

## Measurement 1: the setoid cost, and the counterfactual that does not exist

Every algebra lane since
[ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) reports
this, because ADR-1595 is reversible on the evidence. ADR-1588 measured seven
extra fields at `CommRing`; ADR-1609 measured one field per structure and found
the polynomial ring unreachable over `Eq`; ADR-1620 measured **zero** for the
delooping. This lane's number is **one real proof and three one-line liftings
per bundled-hom category**, and the twelve fields split cleanly:

| field | filled by | new proof? |
|---|---|---|
| `obj` | the `AlgS` record's own type | — |
| `hom` | `CatS.GrpHom` / `CatS.MonHom` | — |
| `homEquiv` | pointwise `B.equiv` on `Subtype.val`, **ignoring the proof component** | — (data) |
| `homRefl` / `homSymm` / `homTrans` | `B.equivRefl` / `Symm` / `Trans` under one binder | **3 liftings** |
| `id` | `Subtype.mk (fun a => a) (isXHom_id A)` | — |
| `comp` | `Subtype.mk (fun x => v (u x)) (isXHom_comp …)` | — |
| `compCongr` | `B.equivTrans (vCongr (val u x) (val u' x) (hu x)) (hv (val u' x))` | **1** |
| `idL` / `idR` / `assoc` | `B.equivRefl` | — |

Two of those rows carry the whole story.

**`compCongr` is where the bundling is spent, and it is the exact step ADR-1620
measured as impossible.** The chain is `v (u x) ~ v (u' x) ~ v' (u' x)`. The
second step is the hypothesis `hv` at `u' x`. The first step needs `v` to
respect `H.equiv` — and `v`, being a `Subtype` inhabitant, *carries that proof*
(`CatS.isGrpHom_congr H K (val v) (property v)`). An unbundled `v` does not.
One `equivTrans`, one projection.

**`idL`, `idR` and `assoc` are free, and the mechanism is ι-reduction.**
`Subtype.val (Subtype.mk f h)` reduces to `f`, so
`val (comp (id b) u) x ≡ val (id b) (val u x) ≡ val u x`: both sides of the
unit law are the *same function*, and the law is `B.equivRefl` applied
pointwise. This is the same free-fields effect ADR-1613 measured at the image
group (fourteen of fifteen fields free); it is not a coincidence but the
defining property of a `Subtype` carrier.

**The `Eq`-flavoured counterfactual does not exist at all**, and it fails
harder than ADR-1609's polynomial ring did. Over `Eq`, `homEquiv` would be
`Eq (hom G H) u v`, an equality of `Subtype` inhabitants, and the unit law
would then need `Eq` between *functions* — which is `funext`, still out by
ADR-1595. There is no `Eq`-flavoured category of groups in this kernel.
**No evidence to reopen ADR-1595.**

### The one category here that is NOT setoid-enriched

`CatS.ptAlg` states everything with `Eq`, and that is deliberate rather than an
inconsistency: **a pointed unary algebra carries no equivalence of its own**.
There is nothing for a morphism to respect, so `IsPtHom` is two `Eq`s and
`homEquiv` is pointwise `Eq`. The `compCongr` proof there is
`Eq.trans (congrArg (val v) (hu x)) (hv (val u' x))` — structurally identical
to the setoid one with `congrArg` in place of the carried congruence. That
correspondence is the honest statement of what setoid enrichment buys: it is
`congrArg` for a relation that is not `Eq`.

`congr_arg_across` is new because
`nat_prelude::structures::congr_arg` fixes ONE carrier for both sides of its
conclusion — right for an algebraic identity `f : α → α`, wrong for a morphism
`f : α → β`. Both carriers here live at level 1, so only the type argument
moves.

## Measurement 2: three universe findings, and the guard did not block anything

**2a. Every category in this layer is `CatS.CategoryLarge`, and `CatS.Category`
cannot hold any of them.** `AlgS.Group`, `AlgS.Monoid` and `CatS.PtAlg` are all
`Sort 2`; `CatS.Category.obj` is a `Sort 1`. Read from the kernel, in both
directions, for all three:

```text
CatS.grp   : CatS.CategoryLarge   (def_eq holds) ; : CatS.Category  (REFUSED)
CatS.mon   : CatS.CategoryLarge   (def_eq holds) ; : CatS.Category  (REFUSED)
CatS.ptAlg : CatS.CategoryLarge   (def_eq holds) ; : CatS.Category  (REFUSED)
CatS.PtAlg : Sort 2 (holds) ; Sort 1 (REFUSED) ; Sort 3 (REFUSED)
```

This is a level fact and not the ADR-1495 guard: the small record simply is not
tall enough. ADR-1620 already established the object level was never the
obstruction, and nothing here contradicts it.

**2b. `CatS.FunctorLarge` is a FOURTH record, at `Sort 3`.** `CatS.Functor`'s
`src` and `tgt` fields are typed `CatS.Category`, and a record's field types
are fixed at declaration, so a functor between two `CategoryLarge`s cannot be a
`CatS.Functor` value. `CatS.FunctorLarge` is the **same seven-field list**
(`functor_fields`, unchanged) at `l1 := 2`, `l2 := 3`:

| record | `src`/`tgt` field's type | its level | record at |
|---|---|---|---|
| `CatS.Functor` | `CatS.Category` | 2 | `Sort 2` |
| `CatS.FunctorLarge` | `CatS.CategoryLarge` | 3 | `Sort 3` |

It admits. This is ADR-1620's measurement 2a — "a record CAN hold a record,
because a record-typed field lands on the kind that already eliminates at `l2`"
— applied one level up, and it is now measured at two levels rather than one.

**2c. The guard's rejection, verbatim, and it blocked nothing.** The only
ADR-1495 interaction in this layer is `declare_record`'s own control, which
demands the same field list one level *down* be refused. Captured with a
positive twin in the same test:

```text
FunctorLarge rejection at Sort 2: ConstructorFieldUniverseTooBig {
    inductive: NameId(…), ctor: NameId(…), field_index: 0 }
```

and the same seven fields at `Sort 3` admit. **No construction in this ADR was
blocked by the universe guard.** That is the third consecutive ADR to reach
that conclusion after starting from the opposite hypothesis (ADR-1613's whole
question was whether the guard was what kept `Sigma` out; it was not), and the
general lesson is the one already in the repository's Gotchas: *verify a
blocker still exists before treating it as one, including a blocker this
repository's own documents name.*

**A fourth, smaller finding.** `Subtype.{1}`'s result universe is
`Sort (max 1 1)`, and the kernel's level machinery normalizes that to `Sort 1`
where the `hom` field demands one. No `max`-idempotence workaround was needed.

## Measurement 3: the forgetful functor, and what it actually cost

`AlgS.Group.toMonoidS : AlgS.Group -> AlgS.Monoid` is free but is **not a
prefix projection**, unlike `AlgS.CommGroup.toGroupS`. The two field lists
diverge at index 8:

| index | `AlgS.Monoid` | `AlgS.Group` |
|---|---|---|
| 0–7 | carrier, equiv, refl, symm, trans, op, opCongr, e | the same |
| 8 | `assoc` | `inv` |
| 9 | `identL` | `invCongr` |
| 10 | `identR` | `assoc` |
| 11–14 | — | `identL`, `identR`, `invL`, `invR` |

So `toMonoidS` gathers group indices 0–7, 10, 11, 12, and the three law fields
land at different indices while stating literally the same thing (the field
*specs* are the same closures, and `carrier`/`equiv`/`op` are carried across
unchanged). All eleven are checked against the group's own selector with a
*different group* as the discriminating negative twin.

The functor's real content is in the morphism map, and it is one theorem:

- `mapCongr` is `fun G H u v h => h` — the hypothesis IS the conclusion,
  because `Subtype.val (map u)` ι-reduces back to `Subtype.val u`;
- `mapId` and `mapComp` are `equivRefl`, for the same reason;
- the morphism map itself must produce an `IsMonHom`, whose first two conjuncts
  are `And.left`/`And.right` of the `IsGrpHom` and whose **third** —
  `H.equiv (f G.e) H.e` — is `AlgS.Hom.mapOne`, already proved.

**A monoid morphism carries a conjunct a group morphism does not**, and the
suite refuses the shape without it (`IsMonHom` is `congr ∧ (op ∧ unit)` and is
NOT def-eq to `congr ∧ op`, which would be a semigroup morphism). That single
conjunct is the reason this layer takes `AlgS.Hom.mapOne` as a dependency at
all; everything else it needs, it builds.

`Grp → Mon` was chosen over `CommRing → CommGroup` because the reviewer named
the monoid direction and because it is the one where the forgetting is *real*:
`toGroupS` and `toCommGroupS` are prefix projections whose morphism maps are
literally the identity, so a functor over them would be true by ι-reduction
alone and would exercise nothing.

## Measurement 4: ℕ as an initial object, and what "re-proved" means

`CatS.PtAlg` is the object ADR-1620 could not form. Its three accessors are
`Sigma.fst`/`Sigma.snd` compositions, and at `CatS.natPtAlg` they reduce, read
from the kernel:

```text
CatS.PtAlg.carrier CatS.natPtAlg  ==  Nat        (Prop REFUSED)
CatS.PtAlg.zero    CatS.natPtAlg  ==  Nat.zero   (Nat.succ Nat.zero REFUSED)
CatS.PtAlg.succ    CatS.natPtAlg Nat.zero == Nat.succ Nat.zero (Nat.zero REFUSED)
```

`CatS.natMed` follows the universal-property template exactly: the mediating
map is **given as data**, not extracted from an `Exists` (template part 2,
*computed, not extracted*). It is `Nat.rec` at the constant motive
`fun _ => Q.carrier`, and both structure equations are `Eq.refl` because both
sides ι-reduce. The suite checks it by **computation**, not only by type:
`med 0` reduces to `0` and not `1`, `med 2` reduces to `2` and not `1`.

Uniqueness is `Nat.rec` induction in exactly two steps:

- zero: `Eq.symm` of the morphism's own zero law (`med 0` and `g 0` are both
  `zero Q` up to ι);
- successor: `congrArg (succ Q)` on the induction hypothesis, then `Eq.trans`
  against `Eq.symm` of the morphism's successor law.

**This is `Nat.Peano.initial` RE-PROVED, not cited, and the reason is build
order rather than mathematics.** `Nat.Peano.iter` and `Nat.Peano.initial` live
in the `characterization` package, which is built ON TOP of this prelude, while
`CatS.*` lands at the `AlgS` position inside it. The mediating map here is
definitionally the same map. A future lane that wants the citation rather than
the re-proof has two options — move `CatS.*` later in the build, or state a
bridge in the `characterization` package — and neither is free, so the honest
record is that the *content* of ADR-1610's universal property is now available
categorically and the *name* is not shared.

**`Int.Characterization.initial` is NOT recovered**, and the reason has changed.
It is no longer "there is no `Sigma`". A ℤ-structure is a quadruple
`(R, e, up, down)` **subject to two mutual-inverse laws**, so its category
needs a further nested `Sigma` *and* an object type that carries `Prop` fields —
which is a `PSigma`/`Subtype` mixture over a `Sigma`, at a level that has not
been measured. That is scoped, not blocked, and it is the natural next
increment.

## What landed

25 named declarations, all with an empty `Kernel::axiom_footprint`. The
environment grows by **35**, measured with `shape_search --include-constructed`
before and after (4148 -> 4183), because the `CatS.FunctorLarge` record
contributes ten more that nobody names by hand:

| kind | before | after | delta | what |
|---|---:|---:|---:|---|
| definition | 1018 | 1043 | +25 | 18 named definitions + 7 `FunctorLarge` selectors |
| theorem | 2889 | 2896 | +7 | the seven named theorems |
| inductive / constructor / recursor | 61 / 89 / 61 | 62 / 90 / 62 | +1 each | `CatS.FunctorLarge`, `.mk`, `.rec` |

The named 25:

| group | declarations |
|---|---|
| the category of groups | `GrpHom`, `isGrpHom_congr`, `grp` |
| the category of monoids | `IsMonHom`, `isMonHom_id`, `isMonHom_comp`, `isMonHom_congr`, `MonHom`, `mon` |
| the forgetful functor | `AlgS.Group.toMonoidS`, the record `CatS.FunctorLarge`, `IsFunctorLarge`, `functorLarge_isFunctor`, `forgetGrpMon`, `forgetGrpMon_isFunctor` |
| pointed unary algebras | `PtAlg`, `PtAlg.carrier`, `PtAlg.zero`, `PtAlg.succ`, `IsPtHom`, `PtHom`, `ptAlg`, `IsInitialLarge` |
| ℕ's universal property | `natPtAlg`, `natMed`, `natPtAlg_isInitial` |

Rendered from the kernel:

```text
CatS.GrpHom : (G : AlgS.Group) -> (H : AlgS.Group) -> Sort 1
CatS.grp    : CatS.CategoryLarge
CatS.isGrpHom_congr :
  (G : AlgS.Group) -> (H : AlgS.Group) ->
  (f : AlgS.Group.carrier G -> AlgS.Group.carrier H) ->
  CatS.IsGrpHom G H f ->
  (a : AlgS.Group.carrier G) -> (b : AlgS.Group.carrier G) ->
  AlgS.Group.equiv G a b -> AlgS.Group.equiv H (f a) (f b)
CatS.forgetGrpMon_isFunctor :
  CatS.IsFunctorLarge (CatS.FunctorLarge.src CatS.forgetGrpMon)
                      (CatS.FunctorLarge.tgt CatS.forgetGrpMon)
                      (CatS.FunctorLarge.obj CatS.forgetGrpMon)
                      (CatS.FunctorLarge.map CatS.forgetGrpMon)
CatS.PtAlg  : Sort 2
CatS.natMed : (Q : CatS.PtAlg) -> CatS.PtHom CatS.natPtAlg Q
CatS.natPtAlg_isInitial :
  CatS.IsInitialLarge CatS.ptAlg CatS.natPtAlg CatS.natMed
```

## Consequences

- **`CatS.*`'s names are still deliberately not threaded into `NatPrelude`**,
  for the reason `AlgS.Poly.*` gives: widening `StructuresSExtraNames` changes
  a struct that `axeyum-py`'s generated field registry mirrors. Tests reach the
  declarations by calling `declare_category_setoid` against their own kernel.
- **`declare_category_setoid` now takes a `GroupCatDeps`** carrying
  `AlgS.Hom.mapOne`, so the layer is no longer buildable from `logic` plus the
  two `AlgS` records alone. That is the honest dependency: unit preservation is
  not derivable inside the category layer.
- **`declare_is_functor`, `declare_is_initial` and
  `declare_functor_is_functor` take a name suffix**, so one builder serves both
  the small and the large records. Any future third level costs one more call,
  not a copy.
- **The discrete category still has not landed**, and ADR-1620's reason still
  stands: `hom a b` must be `Sort 1`-valued, `Eq a b` is `Prop`, and there is
  no cumulativity, so it needs a `Sort 1` identity inductive. It was left out of
  scope again in favour of the three blocked constructions; it remains cheap.
- **Products and coproducts (W3-4)** are unaffected and still scoped: an object
  is a value of `C.obj`, so they never needed `Sigma`.
- **A PER-enriched category is no longer worth trying.** ADR-1620 deferred it
  as "the next thing to try if the category of groups is wanted before
  `Sigma`", and set the condition that it "should be measured against the
  `Sigma` route rather than assumed cheaper". The `Sigma` route is now measured
  at one proof per category; the PER route would need totality obligations on
  `id` and `comp` and a record without `homRefl`, i.e. a different record. The
  condition is discharged against it.

## Alternatives considered

- **`Sigma` for the hom-family instead of `Subtype`.** Refused by the kernel,
  not by preference: `Sigma.{u,v}`'s second family is `α → Type v`, and
  `IsGrpHom G H f` is a `Prop`. `PSigma` would accept it but lands at
  `Sort (max 1 u v)` with the proof's level in the `max`, which is `Sort 1` here
  and would also fit — so `PSigma` was a real alternative and `Subtype` was
  chosen because it is the *specialised* form (its second component is
  definitionally a `Prop`, and `Subtype.property` is already a theorem in the
  ADR-1613 family). A future lane wanting a hom whose second component is data
  should reach for `PSigma` and expect it to work.
- **`CommRing → CommGroup` as the first functor.** Its morphism map is the
  identity on `Subtype.val` because both projections are prefix projections, so
  every functor law would be `refl` and the construction would demonstrate
  nothing about forgetting. `Grp → Mon` was taken instead because it needs a
  real theorem (`AlgS.Hom.mapOne`) to typecheck.
- **Making `CatS.Functor` universe-polymorphic** rather than declaring a fourth
  record. Same answer ADR-1620 gave for `Category`/`CategoryLarge`:
  `declare_record` takes its levels as arguments, so two records share one
  field list at the cost of one call; a polymorphic record would need `uparams`
  threaded through every selector, in a file three other spines share.
- **Citing `Nat.Peano.initial` instead of re-proving it.** Blocked by build
  order (measurement 4), and moving `CatS.*` later in the prelude to get the
  citation would be a larger change than the two-step induction it replaces.

## Evidence

| what | where |
|---|---|
| the layer | `crates/axeyum-lean-kernel/src/nat_prelude/category_setoid/groups.rs` |
| build position | `crates/axeyum-lean-kernel/src/nat_prelude.rs`, at the `AlgS` position, after `declare_structures_s_extra` |
| tests (15) | `nat_prelude::category_setoid::groups::groups_tests::*` |
| facts | `F:cats-grp-bundled-hom`, `F:cats-forget-grp-mon`, `F:cats-nat-initial-object` |

The suite reads the kernel for every claim: admission, `axiom_footprint`,
`Declaration` kind, rendered types, universes **in both directions**, the
`ConstructorFieldUniverseTooBig` refusal with its positive twin, evaluation of
every definition against a discriminating negative twin — including `natMed` by
computation at a small magnitude — and a four-entry mutation table, each entry
one SMALL term:

| # | mutation | expected | positive twin in the same test |
|---|---|---|---|
| N1 | `compCongr` concludes about `comp v u'` | REFUSED | `comp v' u'` admits |
| N2 | the composite monoid hom is `f₁ ∘ f₂` | REFUSED | `f₂ ∘ f₁` admits |
| N3 | `natMed`'s zero equation shifted by one `succ` | REFUSED | the unshifted equation admits |
| N4 | initiality reads `med n = succ (g n)` | REFUSED | `med n = g n` admits |

Two def_eq readings are themselves the ADR-1620 measurement, pinned so a
regression cannot pass quietly:

- `CatS.grp`'s hom-family IS the `Subtype` and is **not** def-eq to the bare
  function space — the escape ADR-1620 measured as making `compCongr` false;
- `CatS.IsMonHom` unfolds to `congr ∧ (op ∧ unit)` and is **not** def-eq to
  `congr ∧ op` — the semigroup-morphism shape.

The `category_setoid` filter runs **29** tests, 15 of them new. The three
pre-existing `F:cats-*` facts pinned a count of 14; they were **recounted from
the suite's own output**, not incremented.

## Related

- [ADR-1620](adr-1620-categories-are-setoid-enriched-and-the-universe-guard-is-not-what-blocks-the-category-of-groups.md)
  — the layer this extends, and the three obstructions it measured. Its
  measurement 3 and 4 are discharged here; its measurements 1 and 2 stand.
- [ADR-1613](adr-1613-dependent-pairs-are-an-ordinary-inductive-and-the-guard-never-refused-them.md)
  — `Sigma`, `PSigma`, `Subtype`, and the ι-reduction of `Subtype.val` that
  makes three category fields free.
- [ADR-1610](adr-1610-name-the-universal-properties.md) — `Nat.Peano.initial`,
  whose content is recovered categorically here.
- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) — the
  discipline, and the standing reversal condition (still unmet; this lane adds
  a fifth data point against it).
- [ADR-1495](adr-1495-abstraction-over-structures-is-already-expressible-the-gap-is-surface.md)
  — the constructor-field universe guard, measured verbatim on a fourth record.
- [universal-property template](../08-planning/universal-property-template.md)
  — parts 2 and 4 are what `CatS.natMed` and `CatS.natPtAlg_isInitial`
  implement.
