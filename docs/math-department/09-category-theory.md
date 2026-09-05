# 09 — Category theory

Reviewer: a category theorist
Verdict, 2026-09-04: **absent as a subject, and philosophically opposed to the method — but the library keeps proving universal properties without noticing**
Last measured: 2026-09-04 at `1856cdb3c`

> "You have proved that ℤ is the initial object in its category and that ℕ
> satisfies a universal property, and you did not name either of them. There
> is no category theory here and there is quite a lot of category theory
> here."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Believes that mathematical objects are determined by their maps, that a
construction is worth having when it satisfies a universal property, and that
duplicating a theorem across five carriers is a sign the abstraction was
skipped. Regards concrete construction as a means, not a subject. Their test:
can you state what a product *is*, without saying how to build one?

## What the library has today

**No category theory as a subject.** Measured: zero declarations for
`category`, `functor`, `natural_transformation`, or any of the standard
apparatus.

**But universal properties are being proved, under other names.** This is the
finding of the review:

| what exists | what it is, categorically |
|---|---|
| `Int.Characterization.categorical`, with `induction`, `injective`, `surjective`, `up_injective`, `iter_down_injective`, `rec_unique`, `iso`, `cross`, `shift` | ℤ characterized by a universal property, with uniqueness of the mediating map — the statement that any structure satisfying these axioms is uniquely isomorphic to ℤ |
| `Nat.Peano.induction`, `Peano.injective`, `Peano.surjective`, `Peano.iter_unique`, `Peano.rec_unique`, `Peano.iter_succ`, `Peano.zero_ne_succ` | ℕ as a natural-numbers object: the Dedekind–Peano categoricity result, with uniqueness of iteration |
| `Alg`/`AlgS` spines with forgetful projections `toGroupS`, `toCommGroupS`, `toRingS`, and `AlgS.Group.ofAlg` | the beginnings of forgetful functors between structure categories, hand-written per pair |
| `Nat.cantor_no_fixed_point` | Lawvere's fixed-point theorem in its concrete instance |
| `Complex.no_compatible_order` | a negative universal statement: no relation on ℂ satisfies the ordered-field axioms |

So the library repeatedly reaches for exactly the results this reviewer cares
about, states them concretely for one carrier, and does not connect them.

## Their verdict

**On method: opposed, and with an argument rather than a preference.** The
library is concrete-carrier-first. Every theorem lives over a specific
construction — this ℕ, this ℝ as a setoid of regular sequences, this ℚ as
matrices of integers — and the abstraction layer (`Alg`, `AlgS`) was added
afterward as records of operations. Their prediction is that this does not
scale, and they would cite the library's own history as evidence: the
structure spine had to be built **twice**, once over `Eq` and once over an
explicit equivalence, because the concrete carriers disagree about what
equality is. A categorical treatment would have had one notion of morphism and
one of isomorphism from the start.

**On the absence: unbothered in the short term.** They would concede that
category theory pays off when there are many structures to relate, and this
library has few. Building the categorical apparatus now would be premature.

**On the near-term opportunity: interested.** The ℤ categoricity and ℕ Peano
uniqueness results are, in their language, initial-object and
natural-numbers-object theorems. They are already proved. Naming them as such
costs almost nothing and would let the library state, once, what it currently
states per carrier: that the construction is determined up to unique
isomorphism by its universal property. That is also the honest answer to
"which ℝ?" — a question the library will face the moment a second real-number
construction appears.

**On the deeper obstruction: sympathetic but blunt.** A category has a
*collection of morphisms* as data, and morphism equality is function equality.
Without `funext`, the composition and identity laws cannot be stated in the
usual way; without quotients, no category of quotient objects exists. So the
subject is behind the same door as [04-algebra.md](04-algebra.md), and the
setoid route — a category enriched in setoids, morphisms compared up to an
explicit equivalence — is the constructively standard workaround and is
exactly what `AlgS` already is, without saying so.

## What they would say is missing

- **The definition of a category**, functors, and natural transformations, in
  whichever equality discipline the library settles on.
- **Universal properties as a stated pattern**: initial and terminal objects,
  products, coproducts, limits — so that ℤ's and ℕ's characterizations become
  instances rather than one-offs.
- **Functors between the existing structure categories**, replacing the
  hand-written forgetful projections.
- **Adjunctions**, which is where the subject starts paying rather than
  describing.
- **Setoid-enriched categories**, if the `Quot.sound` decision goes against
  adding the axiom — the standard constructive treatment.

## The blocker

**`funext` and `Quot.sound`, the same fork as
[04-algebra.md](04-algebra.md)**, plus one design question of its own:
whether to build categories over setoids (morphism equality as an explicit
equivalence, matching `AlgS`) or to wait for function extensionality. The
first is available today and is the honest continuation of what the library
already does; the second is cleaner and needs an axiom.

Note that nothing blocks the *cheap* half — naming the universal properties
that are already proved does not need any of this.

## Next five, in their priority order

- [x] **1. Name the universal properties already proved.** *Done 2026-09-04.* State
      `Int.Characterization.categorical` as an initial-object property and the
      Peano results as a natural-numbers-object property, in the library's own
      vocabulary, with the uniqueness of the mediating map explicit. Their
      view: nearly free, and it turns two isolated results into a pattern the
      next carrier can follow.
- [x] **2. A universal-property template for new carriers.** *Done 2026-09-04.* When ℝ, ℂ, or a
      future carrier is constructed, state what it is *the* solution to. This
      is the answer to "which construction?" and it is the question a second
      real-number construction will force.
- [x] **3. Decide the morphism-equality discipline** — *answered by ADR-1595: setoid-enriched.* — setoid-enriched or
      `funext` — in the same ADR that settles the quotient question. The two
      decisions are the same decision.
- [x] **4. Categories, functors, and natural transformations** — *done 2026-09-04, setoid-enriched; the category of groups landed 2026-09-05 once `Subtype` existed.* over that
      discipline, with the existing forgetful projections as the first
      functors and the `Alg`/`AlgS` spines as the first two categories.
- [x] **5. Products and coproducts as universal properties** — *done 2026-09-05; the group product is the first instance where the abstraction earned its keep.*, with the
      existing concrete constructions (`CPoint` as ℝ×ℝ, list append as a free
      monoid) recovered as instances. The first point where the abstraction
      would have to earn its keep against the concrete versions already built.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: zero categorical declarations. ℤ categoricity, ℕ Peano uniqueness, Cantor's fixed-point theorem, and the forgetful projections all present as concrete one-offs. Blocked on the same `funext`/`Quot.sound` fork as algebra. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 3 answered** by roadmap W0-1: the morphism-equality discipline is setoid-enriched, not `funext` (ADR-1595, decided by measurement rather than preference). Items 4 and 5 are now scoped rather than blocked. The first isomorphism theorem that settled it is itself a universal-property result stated without naming one — which is item 1's point, unchanged. | `2a640c9b6` |
| 2026-09-04 | **Next Five items 1 and 2 landed** (roadmap W1-3, W3-13), and the reviewer's "nearly free" estimate was right: `Nat.Peano.initial` (ℕ initial in pointed unary algebras with **no hypothesis on the target at all**) and `Int.Characterization.initial` (ℤ initial among ℤ-structures, needing only the two mutual-inverse laws), both direct applications of already-checked theorems with no new induction, both footprint 0. Uniqueness is stated pointwise up to the carrier's own equivalence, per ADR-1595 — no `funext`. Two mutation defects that drop the uniqueness hypothesis to `True` are refused by the kernel at the declaration. The four-part template for the next carrier is at `docs/research/08-planning/universal-property-template.md`. Categories, functors and natural transformations (item 4) deliberately stay out; ADR-1610 says why. | `c64893719`; characterization tests 10 passed |
| 2026-09-04 | **Next Five item 4 landed** (roadmap W3-3, ADR-1620), and the reviewer's own prediction about the method is tested: `CatS.Category`, `Functor`, `IsNat`, `IsInitial`/`IsTerminal` over setoid-enriched hom-sets, 61 declarations, footprint 0. **The setoid cost is zero by construction** — the five fields the enrichment adds are exactly the five `AlgS` already carries, so delooping a monoid discharges them from selectors, and the counterfactual over `Eq` does not exist for any carrier whose equality is a defined relation. The universe findings: the guard rejects `obj : Sort 1` verbatim and admits the same record at `Sort 2`; ADR-1609's claim that a record cannot hold a record is corrected to "the level is per field kind", since `Functor` holds two `Category` fields. **The category of groups is blocked on `Sigma`, not on universes**, and `Sigma` was admitted by a concurrent lane the same day — so the forgetful functors (the reviewer's item 3 complaint) and ℕ/ℤ as `IsInitial` instances are one merge away rather than one decision away. Item 5 (products/coproducts) remains. | `0e4eeba47`; `category_setoid` 14 passed |

| 2026-09-05 | **The category of groups is a real category** (roadmap W3-3 second lane, ADR-1626): `CatS.grp` and `CatS.mon` with homs bundled as a `Subtype` of functions carrying their homomorphism proof, the forgetful functor Grp → Mon as a `CatS.FunctorLarge` with all three laws, and ℕ initial among pointed unary algebras. The setoid price of a bundled-hom category is one new proof; the category laws are the underlying-function laws because `Subtype.val` reduces. ℤ as an initial object is scoped, not landed (its object type mixes `PSigma` and `Subtype`). Item 5, products, is now the next thing. | `251b198fb`; `category_setoid` 29 passed |
| 2026-09-05 | **Item 5 landed** (roadmap W3-4, ADR-1632): `IsProduct`/`IsCoproduct` with three conjuncts (the mediating map must commute with the projections; uniqueness alone is satisfiable vacuously), `product_unique_upto_iso` at sixteen hom-equivalence steps, and the product of two groups in `CatS.grp` with both triangles by `equivRefl`. The Next Five for this reviewer is complete. ℤ as an initial object is still open, now for the right reason: build order, not the object type. | `a03298818`; `category_setoid::` 41 passed |

## How to re-measure

```sh
for t in category functor natural_transformation adjoint initial_object \
         terminal_object universal_property colimit; do
  printf '%-24s %s\n' "$t" "$(grep -rli "$t" crates/axeyum-lean-kernel/src/ | wc -l)"
done

grep -rhoE '"(Int\.Characterization|Nat\.Peano)\.[A-Za-z_]+"' \
  crates/axeyum-lean-kernel/src/ | tr -d '"' | sort -u
```

## Related

- [04-algebra.md](04-algebra.md) — the same fork, argued in full
- [10-logic-and-foundations.md](10-logic-and-foundations.md) — the
  categoricity results, judged by the other reviewer who cares about them
