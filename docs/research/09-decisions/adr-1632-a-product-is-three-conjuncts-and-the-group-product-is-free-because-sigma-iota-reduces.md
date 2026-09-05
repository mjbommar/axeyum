# ADR-1632: a product is three conjuncts, and the product of two groups is free because Σ ι-reduces

Status: proposed
Date: 2026-09-05
Lane: `cat-products`
Roadmap: W3-4 (products and coproducts as universal properties), on top of W3-3 and its ADR-1626 residue

Index-summary: `CatS.IsProduct` / `CatS.IsCoproduct` / `CatS.IsProductLarge`
land the product's universal property in the shape `CatS.IsInitial` already
uses — the mediating map is a **given**, uniqueness is up to the
hom-equivalence — and the shape has to be **three** conjuncts rather than one,
because a product's mediating map must also *commute with the projections* and
uniqueness does not imply that (pinned by a negative twin: the two-triangle
form and the full form are refused as `def_eq`). `CatS.Iso` did not exist —
`CatS.initial_unique` writes the conjunction out by hand — so it is defined
here and `CatS.product_unique_upto_iso` is stated against it; that theorem is
**not** free the way `initial_unique` is, because discharging the uniqueness
clause's two hypotheses for `m := v ∘ u` needs `assoc` and `compCongr`, at
sixteen hom-equivalence steps. Two instances: `CatS.indiscrete_isProduct` /
`isCoproduct` (every object is a product of any two, the honest measure of what
a universal property says when `homEquiv` is `True`), and **the product of two
groups** — `CatS.grpProd` on `Sigma.{0,0} G.carrier (fun _ => H.carrier)` with
the two `Subtype`-bundled projections, the bundled pairing `CatS.grpProdMed`,
and `CatS.grp_isProduct`. The setoid price is measured and it is the *lowest of
any construction in this layer so far*: **all ten law fields of the product
object are literally `And.intro (G.law …) (H.law …)`**, with no congruence
bookkeeping at all, because the product setoid's `equiv` IS the conjunction of
the two component `equiv`s; and **both triangles of `grp_isProduct` are
`equivRefl`**, free by the same ι-reduction ADR-1626 measured at
`Subtype.val` — `Sigma.fst (Sigma.mk a b)` reduces, so `pr1 ∘ ⟨f, g⟩` and `f`
are the same function. 12 declarations, 4 of them checked `Theorem`s, empty
`Kernel::axiom_footprint` on every one. ℤ as an initial object is **not**
landed, and the blocker is now measured to be BUILD ORDER, not the object
type: `Int` is declared in `int_prelude`, whose `build_int_prelude_uncached`
calls `build_nat_prelude` first, so there is no `Int` at the `CatS.*` position
to state initiality about — the `PSigma`/`Subtype` mix the previous handoff
named is not an obstruction, and the ADR gives the type that does fit.
Index-status: proposed

## Context

[ADR-1620](adr-1620-categories-are-setoid-enriched-and-the-universe-guard-is-not-what-blocks-the-category-of-groups.md)
built the setoid-enriched category layer and stated one universal property:
`CatS.IsInitial`, in the shape
`docs/research/08-planning/universal-property-template.md` part 2 requires — the
mediating map is a **given** (`med : forall b, C.hom a b`, computed, never
extracted from an `Exists`), and uniqueness is up to the category's own
hom-equivalence, which is the strongest form available in a kernel with neither
`funext` nor `Quot.sound` (ADR-1595).
[ADR-1626](adr-1626-the-layer-that-was-missing-was-sigma-and-three-blocked-constructions-came-back-together.md)
then made `CatS.grp : CatS.CategoryLarge` real, with a `Subtype`-bundled
hom-family.

W3-4 asks for the next universal property up: the product, its dual, and a
concrete instance. Three questions had to be answered by building rather than
by reading.

## Decision

### 1. A product is three conjuncts, and the third is not the interesting one

Initiality is one clause: `∀ b g, homEquiv (med b) g`. A product is not, and
the reason is structural rather than stylistic. Write only

```text
∀ x f g m, (pr1 ∘ m ~ f) → (pr2 ∘ m ~ g) → m ~ med x f g
```

and nothing says `med x f g` itself makes the triangles commute — the
hypothesis set can be empty. Write only the two triangles and every object with
a pair of maps out of it "is" a product. So:

```text
CatS.IsProduct C a b p pr1 pr2 med :=
  (∀ x f g, C.homEquiv x a (C.comp x p a pr1 (med x f g)) f)
∧ (∀ x f g, C.homEquiv x b (C.comp x p b pr2 (med x f g)) g)
∧ (∀ x f g m, C.homEquiv x a (C.comp x p a pr1 m) f
            → C.homEquiv x b (C.comp x p b pr2 m) g
            → C.homEquiv x p m (med x f g))
```

`CatS.IsCoproduct` is the **same builder with a `dual` flag**: every hom
reversed, every composite written on the other side. One function produces
both, and the suite refuses `def_eq` between them at the same arguments, so the
dual is measured to be a different proposition rather than a renamed copy.

`CatS.IsProductLarge` is the same builder again over `CatS.CategoryLarge`,
because that is where `CatS.grp` lives — exactly the `IsInitial` /
`IsInitialLarge` split ADR-1626 already made.

### 2. `CatS.Iso` is new, and `product_unique_upto_iso` is not free

`CatS.initial_unique` states its conclusion as a bare conjunction of two
round-trip equivalences; there was no `Iso` in the module. Verified ABSENT
against a **fresh** `shape_search` index (`declarations=3093`, above the 3,050
floor) with a positive control of the same kind FOUND
(`CatS.isGrpHom_congr`, itself landed by ADR-1626, so the index postdates that
merge). `CatS.Iso C a b f g` is therefore declared in exactly the shape
`initial_unique` produces by hand, and refused as `def_eq` to the one-sided
statement (a split epi is not an iso).

`CatS.product_unique_upto_iso` then reads:

```text
∀ C a b p pr1 pr2 medP  q qr1 qr2 medQ,
  IsProduct C a b p pr1 pr2 medP → IsProduct C a b q qr1 qr2 medQ →
  Iso C p q (medQ p pr1 pr2) (medP q qr1 qr2)
```

The isomorphism is **named**, not asserted to exist: it is the pair of
mediating maps the universal property already computes.

This is where the abstract half stops being free. `initial_unique` collapses
because initiality gives `med b ~ g` for *every* `g`, so both round trips are
two `homTrans` steps. A product's uniqueness clause takes two hypotheses, and
discharging them for `m := v ∘ u` needs the two fields `super::Cat` does not
carry — `assoc` and `compCongr`:

```text
pr1 ∘ (v ∘ u) ~ (pr1 ∘ v) ∘ u      -- assoc, then homSymm
              ~ qr1 ∘ u             -- compCongr on q's triangle and homRefl u
              ~ pr1                 -- p's triangle
```

four steps; two obligations per side, two sides, **sixteen hom-equivalence
steps** for the theorem. Every one of them is `assoc`/`compCongr` bookkeeping —
nothing in the proof mentions groups, sets or elements. That is the measured
price of stating uniqueness for a *limit* rather than for an initial object,
and it is the number a later lane should expect to pay again for equalisers and
pullbacks.

### 3. The product of two groups is the cheapest construction in this layer

`CatS.grpProd G H : AlgS.Group` has carrier
`Sigma.{0,0} G.carrier (fun _ => H.carrier)`. The levels decide the half of the
ADR-1613 family, exactly as ADR-1626 found for hom-families: both carriers are
`Sort 1 = Type 0`, so `u = v = 0` and `Sigma.{0,0}` lands back at `Type 0 =
Sort 1`, which is what `AlgS.Group.carrier` demands. (`PSigma.{1,1}` also lands
at `Sort 1`; `Sigma` is chosen because it is the half that carries `fst_mk`,
`snd_mk` and `mk_eta`.)

The measured cost table:

| where | fields | new proofs | free |
|---|---|---|---|
| `CatS.grpProd` (the object) | 15 | 10 | 5 (`carrier`, `equiv`, `op`, `e`, `inv` are data) |
| `CatS.grpProdFst` / `Snd` | 2 conjuncts each | 1 each | 1 each |
| `CatS.grpProdMed` | 2 conjuncts | 2 | 0 |
| `CatS.grp_isProduct` | 3 conjuncts | 1 | 2 |

Two findings sit in that table.

**Every one of the ten law proofs is `And.intro (G.law …) (H.law …)` and
nothing else.** Not "morally"; literally — `assoc` is
`And.intro (G.assoc a.1 b.1 c.1) (H.assoc a.2 b.2 c.2)`, `opCongr` is
`And.intro (G.opCongr … (And.left h₁) (And.left h₂)) (H.opCongr … )`. There is
**no congruence bookkeeping at all**, which is not what the rest of this layer
looks like: ADR-1626's `compCongr` needed the bundled congruence and an
`equivTrans`, and the `AlgS` image group needed a real argument. The reason is
that the product setoid's `equiv` is *defined* as the conjunction of the two
component `equiv`s, so a law about the pair and the pair of the component laws
are the same proposition up to ι-reduction of `Sigma.fst`/`Sigma.snd` on a
`Sigma.mk`. Choosing a coarser or finer `equiv` would have destroyed this.

**Both triangles of `grp_isProduct` are `equivRefl`.** `pr1 ∘ ⟨f, g⟩` unfolds
to `fun x => Sigma.fst (Sigma.mk (f x) (g x))`, which ι-reduces to `f`, so the
triangle is reflexivity of `G.equiv` and not a calculation. This is the same
mechanism ADR-1626 measured for `Subtype.val (Subtype.mk f h)` at `idL`, `idR`
and `assoc` — the third independent site at which it pays, and the reason to
prefer computed structure over extracted structure is now a *cost* argument and
not only a soundness one. Uniqueness is one `And.intro` for the same reason:
the goal `P.equiv (m x) ⟨f x, g x⟩` reduces to exactly the conjunction of the
two hypotheses applied at `x`.

The `Eq`-flavoured counterfactual does not exist. Over `Eq` the *object* would
be the same, but `CatS.grp` would not exist at all (ADR-1626: the hom-setoid
would need `funext`), so there is nothing to price against.

### 4. `CatS.indiscrete_isProduct` is worth landing precisely because it is empty

In `CatS.indiscrete A` every hom-set is `A` and `homEquiv` is `True`, so
**every** object, with **any** pair of maps, is a product of **any** two
objects — the theorem quantifies over the apex and both projections and proves
the whole three-conjunct statement with `True.intro`. It is the twin of
`CatS.indiscrete_isInitial`/`isTerminal`, and it is the honest measure of what a
universal property says when the hom-equivalence is total: nothing. Landing it
keeps the reader from reading `grp_isProduct` as though the *statement* did the
work.

## Consequences

- 12 new declarations in a NEW file
  (`crates/axeyum-lean-kernel/src/nat_prelude/category_setoid/products.rs`),
  registered from `category_setoid.rs`, so concurrent lanes' merges into that
  module stay additive. `declare_category_setoid` now returns a fifth
  `ProductNames`; the two call sites that destructure it were widened by one
  binding each.
- Four checked `Theorem`s — `product_unique_upto_iso`, `indiscrete_isProduct`,
  `indiscrete_isCoproduct`, `grp_isProduct` — each read back from the
  environment as `Declaration::Theorem`, each with an empty
  `Kernel::axiom_footprint` asserted after `Environment::contains` (an empty
  footprint is also what a missing name returns).
- Every new `Definition` carries an evaluation test. `grpProd`'s is at a
  CONCRETE pair of groups whose `op`, `e` and `inv` all differ between the
  factors (`op a b = a` / `op a b = b`; `e = 0` / `e = 1`; `inv a = a` /
  `inv a = a+1`), on a `Nat` carrier whose `equiv` is the total relation — so
  every law field is `True.intro` and the *operations* are free to
  discriminate. A product that swapped its components computes a different
  value, and the suite says so.

## What did NOT land, and the measured reason

**ℤ as an initial object.** The handoff recorded this as blocked because the
object type "mixes `PSigma` and `Subtype`". That is not an obstruction. An
object of ℤ-structures is `(R : Sort 1, e : R, up down : R → R)` with two laws,
and the type that holds it is

```text
CatS.ZStruct :=
  Sigma.{1,0} (Sort 1) (fun R =>
    Subtype.{1} (Sigma.{0,0} R (fun _ => Sigma.{0,0} (R → R) (fun _ => R → R)))
                (fun d => (∀ x, down d (up d x) = x) ∧ (∀ x, up d (down d x) = x)))
```

whose levels work out: `Subtype.{1} : … → Sort (max 1 1) = Sort 1`, so the
inner family is `Sort 1 = Type 0` and `Sigma.{1,0} : … → Type (max 1 0) =
Type 1 = Sort 2` — exactly the level `CatS.CategoryLarge.obj` takes, and one
step up from `CatS.PtAlg`, which ADR-1626 already landed at `Sort 2` by the
same construction with the `Subtype` layer omitted.

The actual blocker is **build order**, and it is measured rather than argued:
`Int` is declared in `int_prelude`, and `build_int_prelude_uncached` calls
`build_nat_prelude` first, so at the `CatS.*` position inside `nat_prelude`
there is no `Int` to state initiality *about*. ADR-1626 hit the same wall for ℕ
and got past it because `Nat`, `Nat.rec`, `Nat.zero` and `Nat.succ` are in the
**logic** prelude, so `CatS.natPtAlg_isInitial` could be re-proved in place
rather than cited. `LogicPrelude` has no `int` field, so that escape does not
exist here. Two routes remain for a later lane, and they are not equally
cheap: declare the ℤ-structure category in a module built *after*
`int_prelude` (cheap, but it is no longer part of the `CatS.*` prelude), or
move the whole `CatS.*` layer below `Int` (invasive, and every other lane's
build position moves with it). Neither is a kernel-capability question, which
is the finding.

## Alternatives considered

- **State the product with an `Exists`-quantified mediating map.** Rejected by
  the universal-property template: the map must be computed, or the theorem is
  not usable to build anything. It would also have made `grp_isProduct`'s
  triangles unprovable-by-`refl`, since there would be no term to ι-reduce.
- **Two conjuncts (triangles only), with uniqueness as a separate theorem.**
  Rejected: it is the packaging that lets `product_unique_upto_iso` project the
  clause it needs from a single hypothesis, and the suite pins that the
  two-conjunct form is a *different* proposition.
- **`PSigma` for the product carrier.** Both fit at these levels. `Sigma` wins
  on the projection lemmas it carries, which a later lane relating the product
  to its factors will want.
- **Reuse `groups.rs`'s private `Ob` / `BundledCat` / `sub_*` helpers.**
  Rejected for merge additivity: they are private to a file another lane is
  editing, and the four `Subtype` wrappers are three lines each.
