# 09 — Category theory

Reviewer: a category theorist

Verdict, 2026-09-06: **the subject exists now — 107 declarations, footprint 0,
nine `proved` facts — and the reviewer's complaint has moved one level up: the
vocabulary landed and almost nothing was restated through it**

Last measured: 2026-09-06 at `5fa2e3feb` (kernel index `declarations=3311`)

> "Two days ago there was no category theory and quite a lot of category
> theory. Now there is category theory. What there is not is a single
> pre-existing theorem rewritten in it. You proved the first isomorphism
> theorem and it still concludes in `And`; you proved that a product is unique
> up to isomorphism and the one product you care about is in a universe where
> that theorem cannot be applied to it."

> **AUDITED 2026-09-04.** Every absence claim in the 2026-09-04 reading was
> re-checked against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence. Across the
> twelve files, 11 of 76 absence claims were false and 12 more overstated the
> gap; the cause is that the ledger characterises only 38% of its proved facts
> and does not cover 430 kernel theorems at all (ADR-1605) — **that 430 is not
> reproducible by its own method and is retired; the measured figure is 721 of
> 3,079 registered theorem names uncovered, ADR-1674**. **Re-measured
> 2026-09-06**: the absence claims in *this* file are now stale in the other
> direction — the four things it said were missing landed on 09-04 and 09-05.

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Believes that mathematical objects are determined by their maps, that a
construction is worth having when it satisfies a universal property, and that
duplicating a theorem across five carriers is a sign the abstraction was
skipped. Regards concrete construction as a means, not a subject. Their test:
can you state what a product *is*, without saying how to build one?

## What the library has today

**Category theory is a subject here.** Measured at `5fa2e3feb`:
`shape_search --ns CatS` returns **107 declarations** — 4 inductives, 4
constructors, 4 recursors, 74 definitions and **21 theorems** — in
`crates/axeyum-lean-kernel/src/nat_prelude/category_setoid.rs` and its two
submodules (7,726 lines together), with **41 `#[test]` functions** across the
layer (14 + 15 + 12; counted from source, not re-run for this review). Nine
facts `F-cats-*.json` are `proved`/`proved` with `kernel-term` evidence and an
**empty `axiom_footprint`** in every one.

| what exists | what it is, categorically |
|---|---|
| `CatS.Category` (12 fields), `CatS.CategoryLarge` | a category enriched in setoids: `hom`, `homEquiv` with refl/symm/trans, `comp`, `id`, `idL`, `idR`, `assoc`, `compCongr` — laws up to hom-equivalence, no `funext` |
| `CatS.Functor`, `CatS.FunctorLarge`, `CatS.IsFunctor`, `CatS.IsFunctorLarge`, `isFunctor_id`, `isFunctor_comp`, `functor_isFunctor` | functors both bundled and unbundled, with the composition law of the category of categories |
| `CatS.IsNat`, `isNat_id`, `isNat_ofMonoid` | naturality, as the square alone |
| `CatS.IsInitial`, `IsTerminal`, `IsInitialLarge`, `initial_unique` | initial and terminal objects; the mediating map is **given as data**, not extracted from an `Exists` |
| `CatS.IsProduct`, `IsCoproduct`, `IsProductLarge`, `CatS.Iso`, `product_unique_upto_iso` | products and coproducts as three conjuncts, and uniqueness up to a **named** isomorphism |
| `CatS.grp`, `CatS.mon`, `CatS.GrpHom`/`MonHom` as `Subtype`-bundled homs, `CatS.forgetGrpMon` with all three functor laws | the category of groups, the category of monoids, and a real forgetful functor between them |
| `CatS.ptAlg`, `CatS.natPtAlg`, `natPtAlg_isInitial` | ℕ as an initial object in the category of pointed unary algebras |
| `CatS.grpProd`, `grpProdFst`/`Snd`/`Med`, `grp_isProduct` | the product of two groups, proved to satisfy the universal property |
| `CatS.indiscrete`, `ofMonoid`, `ofMonoidHom`, `largeIndiscrete`, `grpIndiscrete` | the delooping of a monoid as a one-object category, and the indiscrete category as a control |
| `Int.Characterization.initial`, `Nat.Peano.initial` | ℤ and ℕ named as initial objects **outside** `CatS` — the 09-04 naming pass, still unconnected to the categories |

The 2026-09-04 reading said "zero declarations for `category`, `functor`,
`natural_transformation`". That is false today, and the file's own
`How to re-measure` grep was the reason it stayed plausible for a day: the
declarations are named `CatS.Category`, `CatS.Functor` and `CatS.IsNat`, so a
grep for `natural_transformation`, `initial_object` or `colimit` returns 0
while the things themselves are in the kernel. The command is replaced below.

## Their verdict

**On the method: the argument was answered by building, and the answer went
against the prediction.** The reviewer predicted concrete-carrier-first would
not scale and cited the structure spine being built twice — measured today,
`Alg` is **193 declarations** and `AlgS` **390**, with ten `ofAlg` bridges
between them, so the duplication is real and larger than the reviewer knew. But
the categorical layer built on top of `AlgS` cost **zero extra setoid
overhead**: the five fields the enrichment adds are exactly the five `AlgS`
already carries, and in the group product **all ten law fields are literally
`And.intro` of the component laws** because the product `equiv` is defined as
the conjunction (ADR-1632). The abstraction did not have to be paid for
separately. What the reviewer got right is the *diagnosis*; what they got wrong
is that the concrete-first order made the abstraction expensive.

**On what is still not connected: this is now the whole complaint.** Three
measured instances:

1. **`AlgS.Hom.firstIso` and `firstIsoClassical` conclude in `And`**, not in
   `CatS.Iso`, although both `CatS.Iso` and `CatS.grp` exist. The first
   isomorphism theorem is still a pair of maps and two equations.
2. **The uniqueness theorems and the interesting instances are in different
   universes.** `CatS.initial_unique` and `CatS.product_unique_upto_iso` both
   take a `CatS.Category`; the two non-degenerate instances,
   `natPtAlg_isInitial : IsInitialLarge` and
   `grp_isProduct : … -> IsProductLarge`, are at `CategoryLarge`. There is **no
   `CatS.IsoLarge`, no `IsTerminalLarge`, no `IsCoproductLarge`, and no `Large`
   uniqueness theorem** in the 107. So the theorem that a product is determined
   up to unique isomorphism cannot be applied to the one product the library
   built.
3. **Every universal-property instance at the small level is vacuous by
   construction.** `indiscrete_isInitial`, `indiscrete_isTerminal`,
   `indiscrete_isProduct` and `indiscrete_isCoproduct` are all over
   `CatS.indiscrete`, whose `homEquiv` is `True` — the lane declared them
   deliberately as the honest measure of what a universal property says when
   the hom-equivalence is total, which is nothing. They are good controls and
   they are not instances.

**On the morphism-equality fork: closed, and the reviewer would accept it.**
ADR-1595 decided setoid-enriched by measurement rather than preference, and the
category layer is the demonstration: no `funext`, no `Quot.sound`, footprint 0
on all nine facts. The reviewer's own suggestion — "a category enriched in
setoids, morphisms compared up to an explicit equivalence" — is what shipped.

**On what the library still proves without naming:** the pattern the 09-04
review found has not gone away, it moved. `Nat.floorRoot` and `Nat.ceilRoot`
are declared (ADR-1245) as the **divisibility-lattice adjoints** of `b ↦ bⁿ` —
the module doc says so in those words — and `shape_search` finds **one
declaration each and zero theorems about either**. The library has built a
Galois connection and stated no adjunction. That is the same failure as 09-04's
ℤ-initiality finding, one rung up the ladder.

## What they would say is missing

- **Adjunctions.** Measured absent: `adjoint` appears in the kernel only as
  prose about `floorRoot`/`ceilRoot`, and there is no `CatS` declaration for
  it. This is where the subject starts paying rather than describing, and the
  library already has an unstated instance to state it about.
- **`Large` twins for the universal-property vocabulary** — `IsoLarge`,
  `IsTerminalLarge`, `IsCoproductLarge`, and `Large` forms of `initial_unique`
  and `product_unique_upto_iso`. Without them the two real instances are proved
  and unusable.
- **Restating existing algebra through the new vocabulary**: `AlgS.Hom.firstIso`
  as a `CatS.Iso` in `CatS.grp`; `Int.Characterization.initial` and
  `Nat.Peano.initial` as `CatS.IsInitial`/`IsInitialLarge` instances rather
  than free-standing theorems.
- **Functors for the other six forgetful projections.** `AlgS` carries seven
  (`CommGroup.toGroupS`, `OrderedRing.toGroupS`, `CommRing.toCommGroupS`,
  `CommRing.toRingS`, `OrderedRing.toRingS`, `Field.toCommRing`,
  `Group.toMonoidS`); **exactly one** — `Group.toMonoidS`, as
  `CatS.forgetGrpMon` — has been made a functor.
- **Limits beyond binary products**: equalisers, pullbacks, limits and
  colimits. Measured absent (0 hits for each of `equalizer`, `equaliser`,
  `pullback`, `pushout`, `limit`, `colimit` in the category layer). The
  products lane measured the price to expect: **sixteen hom-equivalence steps**
  of `assoc`/`compCongr` bookkeeping per uniqueness-up-to-iso proof.
- **Opposite categories, functor categories, Yoneda, monads, presheaves, comma
  categories.** All measured absent (0 hits each). Nothing here is urgent; it
  is the honest shape of what a first category layer does not yet have.

## The blocker

**There is no longer a blocker, and the last recorded one was wrong.** The
`funext`/`Quot.sound` fork is closed (ADR-1595) and the layer was built without
either. ℤ as an initial object was recorded as blocked on its object type
"mixing `PSigma` and `Subtype`"; the products lane measured that object type in
the kernel and read its type back as `Sort 2`, with `CatS.PtAlg` as a same-kind
positive control, so it fits. **The real obstruction is build order**: `Int` is
declared in `int_prelude`, whose builder calls `build_nat_prelude` first, and
`CatS.*` lives in `nat_prelude` — at the `CatS` position there is no `Int` to
state initiality about. ℕ escaped this only because `Nat`, `Nat.rec`,
`Nat.zero` and `Nat.succ` are in the logic prelude and could be re-proved in
place.

Two routes, not equally cheap: declare a ℤ-structure category in a module built
after `int_prelude` (cheap, but then it is not part of the `CatS.*` prelude), or
move the whole `CatS.*` layer below `Int` (invasive — every other lane's build
position moves with it). Neither is a kernel-capability question.

**Nothing category-related is in flight.** Of the eleven live agent worktree
branches ahead of `main` at `5fa2e3feb`, **none** touches `category_setoid`,
`characterization/`, or this file.

## The 2026-09-04 Next Five — complete

- [x] **1. Name the universal properties already proved.** *Landed `c64893719`
      (W1-3, ADR-1610).* `Nat.Peano.initial` and `Int.Characterization.initial`
      both verified present at `5fa2e3feb`; facts `F-nat-peano-initial` and
      `F-int-characterization-initial` are `proved`/`proved`.
- [x] **2. A universal-property template for new carriers.** *Landed
      `c64893719` (W3-13).*
      `docs/research/08-planning/universal-property-template.md` — four parts,
      and `natPtAlg_isInitial` follows it (the mediating map given as data, not
      extracted from an `Exists`).
- [x] **3. Decide the morphism-equality discipline.** *Answered by ADR-1595:
      setoid-enriched, decided by measurement.* The category layer is the
      demonstration — footprint 0 on all nine `F-cats-*` facts.
- [x] **4. Categories, functors, and natural transformations.** *Landed
      `0e4eeba47` and `251b198fb` (W3-3, ADR-1620/1626).* `CatS.Category`,
      `Functor`, `IsNat`, `grp`, `mon`, `forgetGrpMon`. Verified in the index.
- [x] **5. Products and coproducts as universal properties.** *Landed
      `a03298818` (W3-4, ADR-1632).* `IsProduct`/`IsCoproduct`/`Iso`/
      `product_unique_upto_iso` and `grp_isProduct`. Verified in the index.
      **Caveat measured today:** the general theorem is small-level and the
      group instance is `Large`, so they cannot meet.

## Next five, in their priority order (2026-09-06)

- [ ] **1. `Large` twins for the uniqueness vocabulary** — `CatS.IsoLarge`,
      `IsTerminalLarge`, `IsCoproductLarge`, `initial_uniqueLarge`,
      `product_unique_upto_isoLarge`. The two theorems that make a universal
      property *mean* something are currently inapplicable to the two objects
      the library cares about. Measured: no `Large` form of any of the five
      exists in the 107.
- [ ] **2. Restate `AlgS.Hom.firstIso` as a `CatS.Iso` in `CatS.grp`.** The
      classical statement of the first isomorphism theorem is "G/ker f ≅ im f",
      and the library has both sides and the word for ≅ and still writes
      `And`. Depends on item 1 (`CatS.grp` is `Large`).
- [ ] **3. ℤ as an initial object,** by the cheap route: a ℤ-structure category
      in a module built after `int_prelude`. Not a kernel-capability question —
      the object type fits at `Sort 2`, measured. The expensive route (moving
      `CatS.*` below `Int`) should not be taken for this alone.
- [ ] **4. State the `floorRoot`/`ceilRoot` adjunction.** Two definitions, zero
      theorems, and the module doc already calls them adjoints. The two
      characterisations `aⁿ ∣ b ↔ a ∣ floorRoot n b` and
      `a ∣ bⁿ ↔ ceilRoot n a ∣ b` are the adjunction, and stating them is the
      first adjunction in the library and the cheapest one it will ever get.
- [ ] **5. Functors for the remaining six forgetful projections,** or a
      construction that generates them. Doing it by hand six more times is
      exactly the duplication the reviewer objects to; `forgetGrpMon` is the
      worked example to generalise from.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: zero categorical declarations. ℤ categoricity, ℕ Peano uniqueness, Cantor's fixed-point theorem, and the forgetful projections all present as concrete one-offs. Blocked on the same `funext`/`Quot.sound` fork as algebra. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 3 answered** by roadmap W0-1: the morphism-equality discipline is setoid-enriched, not `funext` (ADR-1595, decided by measurement rather than preference). Items 4 and 5 are now scoped rather than blocked. The first isomorphism theorem that settled it is itself a universal-property result stated without naming one — which is item 1's point, unchanged. | `2a640c9b6` |
| 2026-09-04 | **Next Five items 1 and 2 landed** (roadmap W1-3, W3-13), and the reviewer's "nearly free" estimate was right: `Nat.Peano.initial` (ℕ initial in pointed unary algebras with **no hypothesis on the target at all**) and `Int.Characterization.initial` (ℤ initial among ℤ-structures, needing only the two mutual-inverse laws), both direct applications of already-checked theorems with no new induction, both footprint 0. Uniqueness is stated pointwise up to the carrier's own equivalence, per ADR-1595 — no `funext`. Two mutation defects that drop the uniqueness hypothesis to `True` are refused by the kernel at the declaration. The four-part template for the next carrier is at `docs/research/08-planning/universal-property-template.md`. Categories, functors and natural transformations (item 4) deliberately stay out; ADR-1610 says why. | `c64893719`; characterization tests 10 passed |
| 2026-09-04 | **Next Five item 4 landed** (roadmap W3-3, ADR-1620), and the reviewer's own prediction about the method is tested: `CatS.Category`, `Functor`, `IsNat`, `IsInitial`/`IsTerminal` over setoid-enriched hom-sets, 61 declarations, footprint 0. **The setoid cost is zero by construction** — the five fields the enrichment adds are exactly the five `AlgS` already carries, so delooping a monoid discharges them from selectors, and the counterfactual over `Eq` does not exist for any carrier whose equality is a defined relation. The universe findings: the guard rejects `obj : Sort 1` verbatim and admits the same record at `Sort 2`; ADR-1609's claim that a record cannot hold a record is corrected to "the level is per field kind", since `Functor` holds two `Category` fields. **The category of groups is blocked on `Sigma`, not on universes**, and `Sigma` was admitted by a concurrent lane the same day — so the forgetful functors (the reviewer's item 3 complaint) and ℕ/ℤ as `IsInitial` instances are one merge away rather than one decision away. Item 5 (products/coproducts) remains. | `0e4eeba47`; `category_setoid` 14 passed |
| 2026-09-05 | **The category of groups is a real category** (roadmap W3-3 second lane, ADR-1626): `CatS.grp` and `CatS.mon` with homs bundled as a `Subtype` of functions carrying their homomorphism proof, the forgetful functor Grp → Mon as a `CatS.FunctorLarge` with all three laws, and ℕ initial among pointed unary algebras. The setoid price of a bundled-hom category is one new proof; the category laws are the underlying-function laws because `Subtype.val` reduces. ℤ as an initial object is scoped, not landed (its object type mixes `PSigma` and `Subtype`). Item 5, products, is now the next thing. | `251b198fb`; `category_setoid` 29 passed |
| 2026-09-05 | **Item 5 landed** (roadmap W3-4, ADR-1632): `IsProduct`/`IsCoproduct` with three conjuncts (the mediating map must commute with the projections; uniqueness alone is satisfiable vacuously), `product_unique_upto_iso` at sixteen hom-equivalence steps, and the product of two groups in `CatS.grp` with both triangles by `equivRefl`. The Next Five for this reviewer is complete. ℤ as an initial object is still open, now for the right reason: build order, not the object type. | `a03298818`; `category_setoid::` 41 passed |
| 2026-09-06 | **Re-measured against `main`; the file's absence claims were stale in both directions.** Corrected: "zero declarations for category/functor/natural_transformation" → **107 `CatS` declarations** (4 inductive, 4 constructor, 4 recursor, 74 definition, 21 theorem) and nine `F-cats-*` facts all `proved` with empty footprint; `Nat.Peano.rec_unique`, listed in the 09-04 table, is **ABSENT** (positive control `Nat.Peano.iter_unique`, same kind, FOUND); the `funext`/`Quot.sound` blocker section is deleted as closed. The file's own `How to re-measure` grep was **the mechanism of the staleness** — it searched for `natural_transformation`, `initial_object` and `colimit` and returned 0 against a kernel that has `CatS.IsNat`, `CatS.IsInitial` and `CatS.IsCoproduct`; replaced with `shape_search --ns CatS`. **Three new findings:** the `Large`/small split means `initial_unique` and `product_unique_upto_iso` cannot be applied to `natPtAlg_isInitial` or `grp_isProduct` (no `IsoLarge` and no `Large` uniqueness theorem exists); every small-level universal-property instance is over `CatS.indiscrete`, whose `homEquiv` is `True`, so all four are vacuous controls by design; and `Nat.floorRoot`/`Nat.ceilRoot`, documented in-kernel as divisibility-lattice adjoints, carry **zero theorems** — an unstated adjunction, the 09-04 finding one rung up. A new Next Five is opened; nothing category-related is in flight in any of the eleven live worktree branches ahead of `main`. | `5fa2e3feb`; `shape_search` index `declarations=3311`; `Alg`=193, `AlgS`=390; 41 `#[test]` in the layer (counted, not re-run) |

## How to re-measure

The 2026-09-04 version of this section grepped the kernel source for
`category`, `functor`, `natural_transformation`, `initial_object`,
`terminal_object`, `universal_property` and `colimit`. **It reported 0 for
things that exist** — the declarations are `CatS.IsNat`, `CatS.IsInitial`,
`CatS.IsCoproduct` — and that is why this file claimed the subject was absent a
day after it landed. Read the kernel index instead.

```sh
# The whole layer, by namespace. 107 at 5fa2e3feb.
./target/release/examples/shape_search --ns CatS --limit 300

# The two spines it sits on, for the "built twice" claim. 193 and 390.
./target/release/examples/shape_search --ns Alg  --limit 500 | grep -c '^MATCH'
./target/release/examples/shape_search --ns AlgS --limit 500 | grep -c '^MATCH'

# Which forgetful projections exist, and which is a functor (one: toMonoidS).
./target/release/examples/shape_search --ns AlgS --limit 500 \
  | grep -E '\.(to[A-Z]|ofAlg)'

# The universal properties named outside CatS. Every ABSENT needs a
# same-kind positive control in the same invocation.
./target/release/examples/shape_search --name Nat.Peano.initial
./target/release/examples/shape_search --name Int.Characterization.initial

# The nine facts and their footprints -- read the fact, never the prose.
ls artifacts/facts/F-cats-*.json | wc -l
grep -h '"epistemic_status"' artifacts/facts/F-cats-*.json
grep -h '"axiom_footprint"' artifacts/facts/F-cats-*.json

# What is genuinely absent. Each of these is 0 in the category layer.
for t in equalizer equaliser pullback pushout limit colimit \
         yoneda adjunction monad presheaf comma; do
  printf '%-14s %s\n' "$t" \
    "$(grep -rli "$t" crates/axeyum-lean-kernel/src/nat_prelude/category_setoid.rs \
       crates/axeyum-lean-kernel/src/nat_prelude/category_setoid/ | wc -l)"
done
```

## Related

- [04-algebra.md](04-algebra.md) — the same fork, now closed the same way
- [10-logic-and-foundations.md](10-logic-and-foundations.md) — the
  categoricity results, judged by the other reviewer who cares about them
