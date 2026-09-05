# Lane: cat-products — products and coproducts as universal properties in `CatS` (W3-4)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, cat-products, 2026-09-05).** W3-4 is landed: the
product's universal property, its dual, an isomorphism vocabulary, uniqueness
up to isomorphism, and two instances — including **the product of two groups in
`CatS.grp`**. 12 declarations, 4 of them checked `Theorem`s, every one with an
empty `Kernel::axiom_footprint`
([ADR-1632](../../research/09-decisions/adr-1632-a-product-is-three-conjuncts-and-the-group-product-is-free-because-sigma-iota-reduces.md)).
All of it in a NEW file
(`crates/axeyum-lean-kernel/src/nat_prelude/category_setoid/products.rs`)
registered from `category_setoid.rs`, so concurrent lanes' merges into that
module stay additive.

1. `CatS.IsProduct` / `CatS.IsCoproduct` (over `CatS.Category`) and
   `CatS.IsProductLarge` (over `CatS.CategoryLarge`, where `CatS.grp` lives) —
   the universal-property-template shape `CatS.IsInitial` already uses: the
   mediating map is a **given**, uniqueness is up to the hom-equivalence.
2. `CatS.Iso` (ABSENT before this lane) and `CatS.product_unique_upto_iso`.
3. `CatS.indiscrete_isProduct` / `isCoproduct`.
4. `CatS.grpProd`, `CatS.grpProdFst`, `CatS.grpProdSnd`, `CatS.grpProdMed`,
   `CatS.grp_isProduct`.

**A product needs THREE conjuncts and initiality needs one.** The mediating map
must also *commute with the projections*, and uniqueness does not imply that:
with only the uniqueness clause the hypothesis set can be empty, and with only
the two triangles every object carrying a pair of maps "is" a product. The
suite pins this rather than asserting it — the two-conjunct form and the
three-conjunct form are refused as `def_eq`, and so are the form with the two
projections swapped and the dual.

**`product_unique_upto_iso` is NOT free the way `initial_unique` is.**
Initiality gives `med b ~ g` for *every* `g`, so both round trips collapse in
two `homTrans` steps. A product's uniqueness clause takes two hypotheses, and
discharging them for `m := v ∘ u` needs `assoc` and `compCongr` — the two
fields `Cat` does not carry:
`pr1 ∘ (v ∘ u) ~ (pr1 ∘ v) ∘ u ~ qr1 ∘ u ~ pr1`. Four steps, two obligations
per side, two sides: **sixteen hom-equivalence steps**, all of them
`assoc`/`compCongr` bookkeeping. That is the number a later lane should expect
to pay again for equalisers and pullbacks.

**The product of two groups is the cheapest construction in this layer, and the
reason is ι-reduction.** The carrier is `Sigma.{0,0} G.carrier (fun _ =>
H.carrier)` — both carriers are `Sort 1 = Type 0`, so `u = v = 0` and the pair
lands back at `Sort 1`, which is what `AlgS.Group.carrier` demands. Then:

- **All ten law fields of the object are literally `And.intro (G.law …)
  (H.law …)`.** No congruence bookkeeping at all — not "morally", literally.
  The product setoid's `equiv` is *defined* as the conjunction of the two
  component `equiv`s, so a law about the pair and the pair of the component
  laws are the same proposition up to ι-reduction of `Sigma.fst`/`Sigma.snd` on
  a `Sigma.mk`. Choosing a coarser or finer `equiv` would have destroyed this.
- **Both triangles of `grp_isProduct` are `equivRefl`.** `pr1 ∘ ⟨f, g⟩` unfolds
  to `fun x => Sigma.fst (Sigma.mk (f x) (g x))`, which reduces to `f`. Same
  mechanism ADR-1626 measured at `Subtype.val (Subtype.mk f h)` for
  `idL`/`idR`/`assoc` — the **third** independent site at which "computed, not
  extracted" pays in build cost rather than only in soundness.
- Uniqueness is one `And.intro`, for the same reason: the goal
  `P.equiv (m x) ⟨f x, g x⟩` reduces to exactly the conjunction of the two
  hypotheses applied at `x`.

The `Eq`-flavoured counterfactual does not exist: over `Eq` the *object* would
be the same, but `CatS.grp` would not exist at all (ADR-1626), so there is
nothing to price against.

**`CatS.indiscrete_isProduct` is landed precisely because it is empty.** In
`CatS.indiscrete A` every hom-set is `A` and `homEquiv` is `True`, so every
object with any pair of maps is a product of any two objects, and the theorem
quantifies over all three. It is the honest measure of what a universal
property says when the hom-equivalence is total: nothing. Without it a reader
can mistake `grp_isProduct` for a fact about the *statement*.

**ℤ as an initial object did NOT land, and the recorded blocker was wrong.**
The handoff said the object type "mixes `PSigma` and `Subtype`". It does, and
the mix fits — measured in
`products_tests::the_z_structure_object_type_fits_at_sort_2`, which builds

```text
Sigma.{1,0} (Sort 1) (fun R =>
  Subtype.{1} (Sigma.{0,0} R (fun _ => Sigma.{0,0} (R → R) (fun _ => R → R)))
              (fun d => (∀ x, down d (up d x) = x) ∧ (∀ x, up d (down d x) = x)))
```

in the kernel and reads its type back as `Sort 2` (and NOT `Sort 1`, NOT
`Sort 3`), with `CatS.PtAlg` as a same-kind positive control at the same level.
The real blocker is **build order**: `Int` is declared in `int_prelude`, and
`build_int_prelude_uncached` calls `build_nat_prelude` first, so at the
`CatS.*` position there is no `Int` to state initiality *about*. ADR-1626 got
past the same wall for ℕ only because `Nat`, `Nat.rec`, `Nat.zero` and
`Nat.succ` are in the **logic** prelude and could be re-proved in place;
`LogicPrelude` has no integer type. Two routes remain and they are not equally
cheap: declare the ℤ-structure category in a module built after `int_prelude`
(cheap, but then it is not part of the `CatS.*` prelude), or move the whole
`CatS.*` layer below `Int` (invasive — every other lane's build position moves
with it). Neither is a kernel-capability question, which is the finding a later
lane should start from instead of the type.

**Merge note for whoever lands this.** `declare_category_setoid` now returns a
fifth element (`ProductNames`); the two call sites that destructure it were
widened by one binding each
(`category_setoid.rs`'s own test fixture and `groups/groups_tests.rs`). Nothing
else in `category_setoid.rs` or `groups.rs` was edited, so an additive merge
with a concurrent `CatS.*` lane is a one-line reconciliation at each of those
two sites.
