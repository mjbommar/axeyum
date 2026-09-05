# Lane: vector-spaces-field — `AlgS.Field` with apartness, vector spaces over it, and the first dimension statement

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, vector-spaces-field, 2026-09-05).** W3-2's blocked
half, ADR-1627. **Every declaration was admitted on first submission; every
footprint is empty.** ℚ and ℝ both instantiate.

**The brief's central question, answered: no.** It asked whether `CReal.inv`'s
positive-bound witness is the apartness witness, so that a field could carry
`inv : (x : α) → apart x zero → α`. It is not, and the reason is a
large-elimination wall rather than a missing lemma. `CReal.inv : (x : CReal) →
(k : Nat) → PosBound x k → CReal` takes the **modulus as data**; `Apart x zero`
is `Or (lt x zero) (lt zero x)`, a `Prop`, and `pos_bound_of_lt` yields the
modulus only inside an `Exists`, also a `Prop`. Neither the sign nor the modulus
survives elimination into a `CReal`, and `CReal.no_total_inverse` already proves
the total form impossible. So the record carries

```text
mulInvEx : ∀ a, apart a zero → Exists carrier (fun b => equiv (mul a b) one)
```

a `Prop`, which ℝ discharges by one `Or.elim` on the sign and one `Exists.rec`
on the modulus per branch. **Nothing is lost**: every consumer of a field
inverse here is proving a `Prop`, so it opens the existential and never needs
the inverse as a term. This is also the Bishop / Mines–Richman–Ruitenburg
definition.

**Second design change, also forced: tightness is a PREDICATE.**
`AlgS.Field.IsTight` is a separate `Prop`, not a field. ℚ proves it
(`Rat.fieldS_isTight`, from `lt_trichotomy`); `CReal` cannot, from anything in
the tree. `creal.rs`'s doc block calls tightness "Markov's principle" — **that
is wrong**, Markov is the converse, and the `apart` doc block one screen away
states the direction correctly. Tightness of the Bishop apartness IS
constructively true, but its proof needs a *single-index introduction rule for
`CReal.lt`* (`y_n − x_n > 2/(n+1)` gives `lt x y` with an explicit rational
gap), and no such lemma exists. Making tightness a field would have made ℝ not
a field, for a property no theorem above the record uses.

**Third: `apartCompat` replaces irreflexivity as the record's field.** Both
apartness-congruence directions follow from cotransitivity plus setoid
compatibility, and *neither follows from irreflexivity* — `apart_left_congr`
needs the left disjunct of `apartCotrans a b h a'` refuted, which irreflexivity
cannot do. One field instead of two; irreflexivity is derived.

**29 fields, `MAX_FIELDS` unchanged at 32.** The first 23 are `AlgS.CommRing`'s
own `FieldSpec` closures verbatim (exposed as
`structures_setoid::comm_ring_fields_for_field_s`), which is what makes
`toCommRing` and `ofCommRing` free. `ofCommRing`'s hypothesis types are built by
calling the record's own closures against the ring's selectors, so they cannot
drift.

**Setoid cost per construction.** ℚ: **zero** — `AlgS.CommRing.ofAlg
Rat.commRing` supplies all 23 ring fields with `equiv := @Eq Rat`; only the six
field arguments are proved, and cotransitivity is the one place decidability is
spent (`Rat.lt_trichotomy` plus one `Eq.rec` transport, `Rat.ne_of_lt`). ℝ:
**zero on the ring half** (`CReal.commRingS` existed) and two theorems on the
field half — the positive branch of `mulInvEx` is free (`pos_bound_of_lt` then
`mul_inv_cancel`), the negative branch is the whole cost (`pos_of_neg_lt_zero`,
plus `AlgS.mul_neg_right` because `CReal` has only `neg_mul_neg`, which is
squares).

**Dimension: the first statement landed, the general one did not, and its cost
is sized.** `AlgS.VectorSpace.basis_zero_unique : isBasis v 0 → isBasis u m →
m = 0` — invariance of basis number at zero, a genuine instance of "any two
bases have the same cardinality", with the field's non-triviality doing the
work. It takes **no `IsVectorSpace` hypothesis**, which is itself the finding:
at length zero the module axioms are unused. The general theorem needs the
Steinitz exchange, and the obstruction is neither the field nor `Quot` — it is
**index surgery on a coefficient family** (`Nat.beq`-guarded replacement plus a
`linComb` relation), and `Nat.lt`/`Nat.beq` are undeclared at the `AlgS` build
position, which is why `module_setoid`'s `coeffAgree` exists at all. Item (2)
of ADR-1627's decomposition is the piece nobody had priced.

**The ℚ bridge, measured rather than promised.** ADR-1609's item 1 is free
(`toCommRing Rat.fieldS`); item 2 — `linComb` ↔ `Rat.sumRange` — is **`Eq.refl`
exactly**, not merely "adjacent", because both sides are the same `Nat.rec`
and every selector ι-reduces; item 3 is **confirmed blocked** on
`rowEchelon_isEchelon` (ADR-1554 obligation 4, behind obligations 2 and 3) **and
one gap ADR-1609 did not list**: the row space is ℚ^n, an `AlgS.CommGroup` over
`Nat → Rat`, which does not exist. Honest price: three open ℚ-side lanes plus
ℚ^n as a setoid commutative group plus general dimension invariance.

**Gates.** See the landed-changes rows; every suite carries at least one
negative control that builds a proof term differing in a small subterm and
requires the trusted gate to refuse it, paired with a positive twin.

<!-- plan-section: landed-changes -->

| 2026-09-05 | vector-spaces-field | `AlgS.Field` (29 fields, apartness as data, existential inverse) + `AlgS.VectorSpace.*` with `solve_smul` and `basis_zero_unique`; footprints empty, 18 tests |
| 2026-09-05 | vector-spaces-field | ℚ instantiates: `Rat.fieldS` at zero setoid cost, and `Rat.fieldS_isTight` — the tightness ℝ cannot supply; 5 tests |
| 2026-09-05 | vector-spaces-field | ℝ instantiates: `CReal.fieldS`, `CReal.mulInvEx` by `Or.elim` on the sign and `Exists.rec` on the modulus; 6 tests |
| 2026-09-05 | vector-spaces-field | ℚ is a vector space over itself and `linComb` at ℚ is DEFINITIONALLY `Rat.sumRange`; ADR-1609's bridge item 3 measured and still blocked; 3 tests |
