# ADR-1627: a constructive field has an existential inverse, because `CReal` cannot have a functional one

Status: proposed
Date: 2026-09-05
Lane: `vector-spaces-field`
Roadmap: W3-2 (vector spaces over an abstract field, bases, dimension — reviewer 04.5)

Index-summary: `AlgS.Field` lands the blocked half of roadmap W3-2 — a
constructive field over the setoid spine, with apartness as positive data —
together with `AlgS.VectorSpace.*`, both instances (**ℚ and ℝ**), and the first
dimension statement. **Every declaration was admitted on first submission;
every footprint is empty.** Two design decisions were forced by measurement,
and both contradict the brief this lane was given. (1) **The inverse is
`mulInvEx : ∀ a, apart a zero → ∃ b, equiv (mul a b) one`, an `Exists`, not a
function `(x : α) → apart x zero → α`.** The functional shape is *undefinable
at `CReal`*: `CReal.inv` takes the modulus `k` as DATA, while `Apart x zero` is
`Or (lt x zero) (lt zero x)` — a `Prop` — and `pos_bound_of_lt` yields the
modulus only inside an `Exists`. Neither the sign nor the modulus survives
elimination into a `CReal`. The existential form is a `Prop`, both eliminations
are legal, and no consumer loses anything because every consumer of a field
inverse in this library is proving a `Prop`. (2) **Tightness is a predicate,
`AlgS.Field.IsTight`, not a record field.** ℚ proves it; `CReal` cannot, from
anything in the tree. `creal.rs` calls tightness "Markov's principle", which is
**wrong** — Markov is the converse — but the constructive proof it does need is
a single-index introduction rule for `CReal.lt`, which does not exist. Making
tightness a field would have made ℝ not a field. Also: **`apartCompat`
(setoid compatibility) replaces irreflexivity as the record's field**, because
both apartness-congruence directions follow from cotransitivity plus
compatibility and neither follows from irreflexivity — one field instead of
two, and irreflexivity is derived. The ℚ bridge is measured, not promised:
ADR-1609's item 2 is `Eq.refl` **exactly**, and item 3 is confirmed blocked
plus one gap ADR-1609 did not list.
Index-status: proposed

## Context

[ADR-1609](adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md)
landed modules over an `AlgS.CommRing` with a basis layer (`linComb`, `spans`,
`linearIndependent`, `isBasis`) and stopped at vector spaces, naming two
obstructions. One — "a record cannot hold a record" — was corrected by
[ADR-1620](adr-1620-categories-are-setoid-enriched-and-the-universe-guard-is-not-what-blocks-the-category-of-groups.md):
the level is fixed per `FieldKind`, and `CatS.Functor` holds two `Category`
records. The other stood: **dimension needs `AlgS.Field`, which needs an
apartness relation**, the open question
[ADR-1588](adr-1588-a-setoid-flavored-alg-spine-for-creal.md) and
[ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) both
recorded and neither closed.

Constructively a field's inverse is defined on elements *apart* from zero, not
on elements not-equal to zero, and apartness is positive data. `CReal` already
carries `Apart` with `apart_symm`, `apart_irrefl`, `apart_cotrans`,
`apart_congr`, `not_equiv_of_apart` and `apart_zero_one`. The obvious design —
and the one this lane was briefed to build — is a record with `apart` as a
field and

```text
inv : (x : carrier) → apart x zero → carrier
```

with `mulInv`. The brief asked, explicitly, whether `CReal.inv`'s existing
positive-bound witness is the apartness witness.

## Decision

### 1. The inverse is existential. The answer to the brief's question is **no**.

`creal/inverse.rs` states the shape verbatim:

```text
CReal.inv : (x : CReal) → (k : Nat) → CReal.PosBound x k → CReal
```

The **modulus `k` is data**, and that is deliberate: `creal/inverse.rs`'s own
module doc explains that a `Prop` hypothesis does not block a `Type`-valued
definition — what is blocked is *branching* on one. `CReal.Apart x zero` is
`Or (lt x zero) (lt zero x)`, a `Prop`, so choosing which reciprocal to compute
would eliminate a disjunction into `Type`. And `CReal.pos_bound_of_lt` delivers
the modulus only inside an `Exists`, also a `Prop`, so the modulus cannot be
extracted either. **`inv : (x : α) → apart x zero → α` is undefinable at
`CReal`**, and `CReal.no_total_inverse` already proves the total form
impossible. This is a large-elimination wall, not a missing lemma; no amount of
`creal` work closes it.

So `AlgS.Field`'s inverse field is

```text
mulInvEx : ∀ a, apart a zero → Exists carrier (fun b => equiv (mul a b) one)
```

which is a `Prop`. `CReal` discharges it by `Or`-elimination on the sign
followed by `Exists`-elimination of the modulus, both `Prop → Prop` and both
legal. **Nothing is lost**: every consumer of a field inverse in this library
is proving a `Prop`, so it opens the existential with `Exists.rec` and never
needs the inverse as a term — `AlgS.Field.mul_left_cancel` and
`AlgS.VectorSpace.solve_smul` are exactly that, and they are the two theorems
the field exists for. This is also the standard definition in constructive
algebra (Bishop; Mines–Richman–Ruitenburg): a field is a ring with an apartness
in which every element apart from `0` is invertible.

### 2. Tightness is a predicate, not a field.

`AlgS.Field.IsTight F := ∀ a b, ¬(F.apart a b) → F.equiv a b` is a separate
`Prop` over an `AlgS.Field`. The measurement:

- **ℚ proves it**, `Rat.fieldS_isTight`, from `Rat.lt_trichotomy` and one
  `Eq.rec` transport (`Rat.ne_of_lt`).
- **`CReal` cannot**, from anything in the tree.

`creal.rs`'s doc block on `not_apart_one_of_pow_succ_eq_one` says tightness "is
Markov's principle, neither proved nor assumed here". **That is wrong.** Markov
is the converse, `¬(Equiv x y) → Apart x y`; the `apart` doc block on the same
struct states the direction correctly one screen away. Tightness of the Bishop
reals' apartness is constructively true: `le x y` is `∀ n, x_n − y_n ≤
2/(n+1)`, a Π₁ statement, and each instance is a decidable rational
comparison, so `Rat.le_or_lt` at a fixed `n` either closes the goal or produces
a rational gap. What the second branch then needs is a **single-index
introduction rule for `CReal.lt`** — from `y_n − x_n > 2/(n+1)`, produce
`lt x y` with the explicit gap `q := (y_n − x_n) − 2/(n+1)`, an estimate using
regularity twice — and **no such lemma exists** among `CReal`'s order theorems.
It is a genuine analytic obligation, not a lookup.

Making tightness a field would therefore have made ℝ not a field in this
library, for a property **no theorem above the record uses**. It is a predicate,
ℚ satisfies it, and `CReal`'s case is left open with the route named.

### 3. `apartCompat` replaces irreflexivity as the record's field.

The record's apartness fields are `apart`, `apartSymm`, `apartCotrans`,
`apartCompat`, and the two field-specific ones `mulInvEx` and `oneApartZero`.
`apartCompat : ∀ a b, equiv a b → apart a b → False` is the setoid
compatibility law. It is strictly stronger than irreflexivity, which it derives
in one line (`apartCompat a a (equivRefl a)`), and it is what makes both
congruence directions provable:

```text
apart_left_congr : equiv a a' → apart a b → apart a' b
```

is `apartCotrans` at `c := a'` giving `apart a a' ∨ apart a' b`, with the left
disjunct refuted by `apartCompat`. **With only irreflexivity the left disjunct
is not refutable and the theorem does not follow**, so a record carrying
irreflexivity would have needed a separate congruence field. One field, not
two, and the derivation is checked (`AlgS.Field.apart_irrefl`,
`apart_left_congr`, `apart_right_congr`).

`oneApartZero : apart one zero` is the non-vacuity witness: without it every
other apartness law holds of the relation that separates nothing, and the
record admits the zero ring. It is what `basis_zero_unique` spends.

### 4. Vector spaces are modules over a field, and dimension lands at zero.

`AlgS.VectorSpace.IsVectorSpace F M smul := AlgS.Module.IsModule
(AlgS.Field.toCommRing F) M smul` — a definition, not a new conjunction. The
two field-only theorems:

- `smul_left_cancel : a # 0 → a•v ~ a•w → v ~ w`;
- `solve_smul : a # 0 → a•v ~ w → ∃ c, v ~ c•w` — **solving for a
  coefficient**, the atomic Steinitz exchange step and the one place a
  vector-space proof genuinely needs the field rather than the ring.

`basis_zero_unique : isBasis v 0 → isBasis u m → m = 0` is **the first
dimension statement in this library**: a genuine instance of "any two bases have
the same cardinality". `spans v 0` collapses the space (`linComb c v 0`
ι-reduces to `M.e`), so `linearIndependent u (succ j)` at the two constant
coefficient families `fun _ => one` and `fun _ => zero` forces `equiv one zero`,
refuted by `oneApartZero` through `apartCompat`.

It takes **no `IsVectorSpace` hypothesis**, and that is itself the finding: at
length zero the module axioms are not used at all, only the field's
non-triviality. Stating it over a module would have been a weaker theorem with a
decorative hypothesis.

## What did NOT land, and what it costs

**The general dimension theorem — `isBasis v n → isBasis u m → n = m` — is not
here.** The obstruction is neither the field nor `Quot`. The Steinitz exchange
rewrites the *indexing* of a coefficient family (replace `v i` by `w`, reindex
the rest), and at the `AlgS` build position `Nat.lt`, `Nat.beq` and every
`sumRange` reindexing lemma are undeclared — `module_setoid`'s own `coeffAgree`
exists only because `Nat.lt` does not. The pieces:

1. *"a sum apart from zero has a summand apart from zero"* — provable, by
   induction with cotransitivity (`x + y # 0 → x # 0 ∨ y # 0` follows from
   `apartCotrans` at `x`). This is the constructive content and the field
   supplies it.
2. *index surgery on a coefficient family* — a `Nat.beq`-guarded replacement
   plus the lemma that `linComb` over the replaced family relates to the
   original. This needs `Nat.beq` at the `AlgS` position, i.e. either moving the
   vector-space layer later in the build or re-deriving a decidable index
   equality there.
3. *the exchange induction itself*.

Item 2 is the one nobody has priced before, and it is the reason the general
theorem is a lane and not a follow-on.

## The ℚ bridge, measured

ADR-1609 sized it in three items and said "do not price the bridge as small".
Measured:

| item | ADR-1609 | measured |
|---|---|---|
| 1. an `AlgS.CommRing` for ℚ | free | free — `AlgS.Field.toCommRing Rat.fieldS` |
| 2. `linComb` ↔ `Rat.sumRange` | "`Eq.refl`-adjacent" | **`Eq.refl` exactly** |
| 3. `rank`/`nullity` as `spans`/`linearIndependent` | the real cost | **blocked, and worse than stated** |

Item 2 is `Eq.refl` because both sides are the same `Nat.rec`: `linComb` is base
`M.e`, step `fun j ih => M.op ih (smul (c j) (v j))`; `Rat.sumRange g` is base
`Rat.zero`, step `fun j ih => Rat.add ih (g j)`. At `M := toCommGroupS` of ℚ's
ring and `smul := Rat.mul` every selector ι-reduces and the two minor premises
are the same term. The convention match ADR-1609 guessed at — exclusive bound,
new term on the right — is real. The test asserts `def_eq` of the two sides
directly, with a negative control (drop the vector factor) that must fail.

Item 3 is confirmed blocked on `rowEchelon_isEchelon`
([ADR-1554](adr-1554-the-pivot-is-computed-not-extracted-and-the-fuel-is-exact.md)
obligation 4, behind obligations 2 and 3, "at least a lane on its own and
probably two"). **And there is a fourth item ADR-1609 did not list**: the row
space is ℚ^n, which as a carrier is `Nat → Rat`, and an `AlgS.CommGroup` over a
function type does not exist. It is work rather than an obstruction — the
polynomial ring showed function-space carriers are statable over setoids and
only over setoids — but it is a fourth piece. So the honest price of connecting
`Rat.rank` to the abstract theorem is **three open ℚ-side lanes plus ℚ^n as a
setoid `AlgS.CommGroup` plus general dimension invariance**, and this ADR
promises none of them.

## Consequences

- `AlgS.Field` is **29 fields** (`MAX_FIELDS` is 32, unchanged): `AlgS.CommRing`'s
  23 verbatim plus six. The 23 are the *same `FieldSpec` closures* the spine's
  own `CommRing` is built from — exposed as
  `structures_setoid::comm_ring_fields_for_field_s` — which is what makes
  `toCommRing` and `ofCommRing` free.
- `AlgS.Field.ofCommRing` is the constructor an instance calls: a ring it
  already has plus six proofs, never 23 restated ring laws. Its hypothesis types
  are built by calling the record's **own** `FieldSpec` closures against the
  ring's selectors, so they cannot drift from the record.
- **`AlgS.mul_neg_right`** (`a·(−b) ~ −(a·b)`, three steps off
  `AlgS.mul_neg_one`) is declared in `nat_prelude::field_setoid` rather than in
  `structures_setoid`, deliberately: that file is a shared append point and
  inserting a spec into `declare_structures_s_extra`'s middle is a merge hazard.
  Its only consumer is the `CReal` instance's negative branch — `CReal` has
  `neg_mul_neg` (squares) and no `mul_neg`.
- **Setoid cost per instance.** ℚ: **zero** — `AlgS.CommRing.ofAlg
  Rat.commRing` supplies all 23 ring fields with `equiv := @Eq Rat`, and only
  the six field-specific arguments are proved (apartness is `Not (Eq Rat a b)`;
  cotransitivity is the one place decidability is spent). ℝ: **zero on the ring
  half** (`CReal.commRingS` already existed) and two new theorems on the field
  half — `pos_of_neg_lt_zero` and `mulInvEx` — of which the positive branch of
  `mulInvEx` is free and the negative branch is the whole cost.
- `CReal.fieldS` lives in a module-local ADR-1512 registry, so adding to it
  touches that module and `creal.rs`'s `STEP_DISPATCH` and nothing else;
  `steps_generated.rs` was regenerated (217 steps, 0 order violations).
- **`AlgS.Field.IsTight CReal.fieldS` is deliberately absent.** Anyone who wants
  it should prove the single-index `lt` introduction rule first; that is the
  whole gap.

## Alternatives considered

- **`inv` as a data field, ℚ only.** Rejected: it makes ℝ not a field, which is
  the opposite of the point, and the whole reason W3-2 wanted a field was to
  reach dimension over ℝ as well as ℚ.
- **`apart := ¬(equiv …)`.** Rejected on the discipline this repository already
  keeps (apartness as data, never as a negation) and on the mathematics: over ℝ
  the two differ by Markov's principle, and `CReal.not_equiv_of_apart` is
  one-directional on purpose.
- **Bumping `MAX_FIELDS`.** Not needed — the record is 29 of 32 — and it would
  have been a change to a shared `Copy` array in `structures.rs` for no gain.
- **Tightness as a field with ℝ omitted from the instances.** Rejected; see §2.

## Evidence

| what | where |
|---|---|
| `AlgS.Field` + `AlgS.VectorSpace` admit, footprints empty, 18 tests | `cargo test -p axeyum-lean-kernel --release --lib -- field_setoid vector_space` |
| ℚ instance, tightness, 5 tests | `… --lib -- rat_prelude::field_setoid_instance` |
| ℚ vector space + the `Eq.refl` bridge, 3 tests | `… --lib -- rat_prelude::vector_space_instance` |
| ℝ instance, 6 tests | `… --lib -- creal::field_setoid_instance` |

Every suite includes at least one **negative control** that builds a proof term
differing in a small subterm and requires the trusted gate to refuse it, paired
with a positive twin (the real declaration, present in the environment) so a
control rejecting for an unrelated reason is visible.

## Related

- [ADR-1588](adr-1588-a-setoid-flavored-alg-spine-for-creal.md) — the `AlgS`
  spine, which named the apartness question
- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) —
  setoid quotients; recorded apartness as a separate open question
- [ADR-1609](adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md)
  — modules and the basis layer; the two obstructions this ADR closes and
  corrects
- [ADR-1554](adr-1554-the-pivot-is-computed-not-extracted-and-the-fuel-is-exact.md)
  — `rowEchelon_isEchelon` and its four obligations
- [ADR-0510](adr-0510-the-real-inverse-is-partial-and-its-modulus-is-data.md)
  — `CReal.inv`'s modulus-as-data design, which decided this ADR
