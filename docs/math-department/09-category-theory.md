# 09 — Category theory

Reviewer: a category theorist
Verdict, 2026-09-04: **absent as a subject, and philosophically opposed to the method — but the library keeps proving universal properties without noticing**
Last measured: 2026-09-04 at `1856cdb3c`

> "You have proved that ℤ is the initial object in its category and that ℕ
> satisfies a universal property, and you did not name either of them. There
> is no category theory here and there is quite a lot of category theory
> here."

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

- [ ] **1. Name the universal properties already proved.** State
      `Int.Characterization.categorical` as an initial-object property and the
      Peano results as a natural-numbers-object property, in the library's own
      vocabulary, with the uniqueness of the mediating map explicit. Their
      view: nearly free, and it turns two isolated results into a pattern the
      next carrier can follow.
- [ ] **2. A universal-property template for new carriers.** When ℝ, ℂ, or a
      future carrier is constructed, state what it is *the* solution to. This
      is the answer to "which construction?" and it is the question a second
      real-number construction will force.
- [ ] **3. Decide the morphism-equality discipline** — setoid-enriched or
      `funext` — in the same ADR that settles the quotient question. The two
      decisions are the same decision.
- [ ] **4. Categories, functors, and natural transformations** over that
      discipline, with the existing forgetful projections as the first
      functors and the `Alg`/`AlgS` spines as the first two categories.
- [ ] **5. Products and coproducts as universal properties**, with the
      existing concrete constructions (`CPoint` as ℝ×ℝ, list append as a free
      monoid) recovered as instances. The first point where the abstraction
      would have to earn its keep against the concrete versions already built.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: zero categorical declarations. ℤ categoricity, ℕ Peano uniqueness, Cantor's fixed-point theorem, and the forgetful projections all present as concrete one-offs. Blocked on the same `funext`/`Quot.sound` fork as algebra. | ledger snapshot at `1856cdb3c` |

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
