# ADR-1610: name the universal properties, do not build a category theory library

Status: accepted
Date: 2026-09-04
Lane: `universal-properties`

Index-summary: `Nat.Peano.categorical` and `Int.Characterization.categorical`
each already prove a comparison map structure-preserving and bijective, and
nothing in the kernel said the two theorems were the same SHAPE of claim.
Two new declarations, `Nat.Peano.initial` and `Int.Characterization.initial`,
name the weaker, unconditional half of that shape (existence + pointwise
uniqueness of the mediating map, no axiom on the target) as its own theorem,
built entirely from already-proved theorems. No `Category`, `Functor`, or
`NaturalTransformation` type is added.
Index-status: Accepted

## Context

The 09 (category theory) persona review
([`docs/math-department/09-category-theory.md`](../../math-department/09-category-theory.md))
found "no category theory as a subject" and, in the same file, "the library
repeatedly reaches for exactly the results this reviewer cares about, states
them concretely for one carrier, and does not connect them." Its evidence:

- `Int.Characterization.categorical` proves that any `ℤ`-structure admits a
  structure-preserving bijection from `Int`, with the uniqueness half
  (`rec_unique`) proved separately and combined into one packaged theorem.
- `Nat.Peano.categorical` proves the same shape for `Nat` against the Peano
  axioms.

Both are, in the reviewer's vocabulary, "this object is initial in its
category, and the comparison map is in fact a bijection because the target
also satisfies the object's defining axioms" — but the kernel and the fact
ledger record them as two unrelated one-off theorems named `categorical`,
with no shared vocabulary connecting them and no statement of the *weaker*,
unconditional claim (mere initiality) that the stronger one is built on top
of.

The reviewer's own priority order
([`docs/math-department/00-roadmap.md`](../../math-department/00-roadmap.md),
items W1-3 and W3-13) puts naming this pattern first and building any real
categorical apparatus (`Category`, `Functor`, products, adjunctions) fifth,
behind an explicit blocker: this kernel has no `funext` and no `Quot.sound`
(ADR-1595), so morphism equality cannot be stated as function equality and a
category's composition/identity laws cannot be written in the usual form
without first deciding a setoid-enriched encoding — the same fork
[ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md)
and
[ADR-1602](adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)
already resolved in favour of "build the concrete thing first, on setoids,
and defer the abstraction until a second instance forces it."

## Decision

**Name the pattern as two theorems, not as a category theory library.**

1. `Nat.Peano.initial` and `Int.Characterization.initial`
   (`crates/axeyum-lean-kernel/src/characterization/universal_property.rs`)
   state, per carrier, the universal property proper: for every object of
   the relevant family (a pointed unary algebra for `Nat`; a `ℤ`-structure —
   a pointed set with a mutually-inverse pair of endomorphisms — for `Int`),
   there is a structure-preserving map out of the constructed carrier, and it
   is the unique one. **No hypothesis pins the target beyond what makes it a
   member of the family** — unlike `categorical`, which additionally assumes
   the target satisfies the *object's own* defining axioms (Peano; generation
   + aperiodicity) to get a bijection rather than a mere mediating map.
2. Both proofs are **direct applications of already-checked theorems**:
   `iter_zero`, `iter_succ`, `iter_pred` (existence, each a `refl` because
   `iter` is *defined* to satisfy them) and `iter_unique` / `rec_unique`
   (uniqueness, already proved by induction on the *source*). Nothing here
   re-derives an induction; a statement drifting from the underlying theorem
   makes the new declaration **fail to type-check**, per the kernel's own
   discipline (`docs/contributor-guide/kernel-proof-engineering.md`).
3. Uniqueness is stated **pointwise** (`∀ n, h n = f n`), never as function
   equality `h = f` — there is no `funext` to license that promotion, so the
   statement is exactly as strong as the setoid discipline permits and no
   stronger.
4. **No new type, trait, or namespace for "category" is added.** A
   `Category`/`Functor`/`NaturalTransformation` layer is explicitly out of
   scope (roadmap W3-3), for the same reason ADR-1595 and ADR-1602 give for
   the concrete-first pattern elsewhere: without a settled morphism-equality
   discipline across *every* future category (not just these two), an
   abstraction built now would be re-derived once that discipline is chosen,
   and nothing here needs it — the mediating-map statement above is
   expressible entirely in the vocabulary this kernel already has (`∀`,
   `∧`, `Eq`, no quotient).
5. A **template**
   ([`docs/research/08-planning/universal-property-template.md`](../08-planning/universal-property-template.md),
   mirrored in the module doc of `universal_property.rs`) records the
   four-part shape both instances follow, so a third carrier (`ℝ`, or
   whatever forces "which construction?" next) states its own universal
   property the same way rather than re-deriving the pattern.

## Evidence

- `crates/axeyum-lean-kernel/src/characterization/universal_property.rs`:
  both declarations admitted, axiom footprint `[]`.
  `characterization::characterization_tests::the_characterization_package_builds_and_every_witness_is_axiom_free`
  now asserts `entries.len() == 34` (was 32).
- Non-vacuity: `characterization_tests::initial_is_not_vacuous_it_instantiates_at_the_carrier_itself`
  instantiates `Nat.Peano.initial` at `(Nat, zero, succ)` directly (no
  hypothesis to discharge — initiality needs none) and
  `Int.Characterization.initial` at `(Int, 0, (·+1), (·−1))` with the two
  inverse laws discharged by the ring laws, exactly as
  `Int.Characterization.categorical_at_int` discharges its own four-hypothesis
  list for the stronger theorem.
- Mutation: two new `Weakening` variants, `NatInitialDropUniqueZero` and
  `IntInitialDropUniqueZero`, each replace the packaged uniqueness clause's
  `h 0 = z` / `g 0 = e` hypothesis TYPE with `True` while the proof still
  supplies the real equation — the kernel refuses both, at the declaration
  itself (`characterization_tests::every_injected_defect_is_rejected`,
  `Weakening::defects().len() == 24`, was 22).
- `cargo run -q -p axeyum-lean-kernel --example characterization_status`
  exits 0: `34/34` theorems admitted with an empty footprint, `24/24`
  injected defects refused at the declaration they were aimed at.
- Ledger: `artifacts/facts/F-nat-peano-initial.json`,
  `artifacts/facts/F-int-characterization-initial.json`, both curated
  (not `[generated]`), `epistemic_status: proved`, `axiom_footprint: []`.

## Alternatives

- **Build `Category`/`Functor` now and derive both `initial` theorems as
  instances of a generic `IsInitial` predicate.** Rejected for the reason
  ADR-1595/ADR-1602 already gave for algebra and the metric layer: this
  kernel has no settled morphism-equality discipline (setoid-enriched vs.
  waiting for `funext`), and a generic categorical layer built before that
  choice is fixed would either bake in the wrong equality or need a second
  pass once it is chosen. Two instances do not justify the layer; the
  reviewer's own file says as much ("building the categorical apparatus now
  would be premature").
- **State the universal property with `Exists`** (`∃ f, preserves f ∧ ∀ h,
  preserves h → h = f`), the textbook `∃!` phrasing. Rejected for this
  kernel specifically: the quantified type is `Nat → N` / `Int → R`, whose
  universe level is `imax(1, u)` for a universe-polymorphic `u`, which would
  need to be threaded through `Exists.{level}` correctly with no existing
  precedent in this codebase for an `Exists` over a *function* type at a
  polymorphic level (every existing `exists_at` call in
  `crates/axeyum-lean-kernel/src/characterization/` quantifies over `Nat` or
  `Int` at a fixed level). The named-witness form (`iter`, already declared,
  already used by `categorical`) avoids the risk entirely and matches the
  vocabulary `categorical` already uses — "computed, not extracted"
  (2026-08-27 architecture review), applied to the mediating map itself.
- **Fold `initial` into `categorical` as a comment**, rather than a separate
  declaration. Rejected: `categorical`'s hypothesis list conflates the
  category's defining axioms (inverse laws; no axioms at all for `Nat`) with
  the *further* axioms that pin the object among its peers (generation,
  aperiodicity, the Peano axioms). A reader cannot recover "is `Int` merely
  initial" from `categorical` without manually discarding two of its four
  hypotheses. A separate, checked theorem is the only way "initiality alone
  needs no axiom on the target" is itself a falsifiable claim rather than an
  assertion in a docstring.

## Consequences

- The next universal-property carrier (a second `ℝ` construction, forced by
  roadmap item W1-3's own framing of "which ℝ?") has a template to follow
  rather than a blank page: name the family's defining axioms, name the
  mediating map as a definition, prove existence by the map's own computation
  rules, prove uniqueness by induction on the source, package as one
  conjunction.
- `Category`, `Functor`, and `NaturalTransformation` (roadmap W3-3) remain
  unbuilt, and this ADR does not resolve when they should be — that is
  bundled with the same setoid-vs-`funext` decision
  [04-algebra.md](../../math-department/04-algebra.md) already blocks on.
  W3-3 stays a distinct, larger task; it is not unblocked by this one.
- The fact ledger now carries two curated (not `[generated]`) facts stating,
  in prose, exactly what "initial" means for these two carriers and how it
  differs from "categorical" — closing the same kind of gap ADR-1605 measured
  at scale (a theorem the kernel admits with no reviewable prose describing
  it), for these two theorems specifically.
