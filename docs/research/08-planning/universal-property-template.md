# Universal-property template

Status: accepted (ADR-1610)
Owner: lane `universal-properties`, roadmap items W1-3 / W3-13

This is the template roadmap item W3-13 asks for: the stated shape a future
carrier's "this construction is *the* solution to this problem, up to unique
isomorphism" theorem should follow. It is deliberately **not** a category
theory library — see
[ADR-1610](../09-decisions/adr-1610-name-the-universal-properties.md) for why
naming the pattern is nearly free while building `Category`/`Functor` now
would not be. The two instances today are `Nat.Peano.initial` and
`Int.Characterization.initial`
(`crates/axeyum-lean-kernel/src/characterization/universal_property.rs`).

## The constraint that shapes every step

This kernel has no `funext` and no `Quot.sound` (ADR-1595). A category's
morphism equality is ordinarily function equality; here it cannot be, so
**every uniqueness claim below is stated pointwise** (`∀ x, h x = f x`), never
as `h = f`. This is not a weaker substitute chosen for convenience — it is
exactly as strong a claim as the setoid discipline permits, and no stronger
claim can be made honestly without first resolving the same setoid-vs-`funext`
fork [04-algebra.md](../../math-department/04-algebra.md) is blocked on.

## The four parts

### 1. State the category's defining axioms as the hypothesis list — and no more

An "object" is a carrier plus operations satisfying *exactly* the axioms that
make it a member of the family in question. Get this right first, because
getting it wrong either overstates the theorem (silently assuming something
extra) or understates it (proving a bijection theorem's hypothesis list
when only initiality is claimed).

- For `Nat`, the family is "pointed unary algebras" `(N, z, s)`. There is
  **no axiom at all** — every `(N, z, s)` is such an object.
- For `Int`, the family is "`ℤ`-structures" `(R, e, up, down)` with `up`/`down`
  mutually inverse. That mutual-inverse pair **is** the family's defining
  axiom, not an extra hypothesis pinning the object further.

Distinguish this from the axioms that pin the object *uniquely among its
peers* (Peano's induction; `Int`'s generation + aperiodicity). Those belong to
a *separate*, stronger theorem — see part 4.

### 2. Name the mediating map as a computed definition, never an extracted witness

The map a universal property asserts exists should be a `Definition` already
in the environment for other reasons, applied here — not a witness pulled out
of an `Exists` proof. `Nat.Peano.iter` and `Int.Characterization.iter` are
both pre-existing definitions; `initial` uses them directly. This is the
"computed, not extracted" lesson of the
[2026-08-27 architecture review](../11-design-review/2026-08-27-architecture-review.md),
applied one level up — and it is also why this template's own statement is a
conjunction (`preserves f ∧ ∀ h, preserves h → …`) rather than an `∃ f, …`:
naming `f` as the concrete, already-declared map sidesteps needing an
`Exists` over a universe-polymorphic function type at all.

### 3. Prove existence as the map's own computation rules

The named map should satisfy the structure-preservation equations
*definitionally*, or as close to it as the encoding allows — `iter_zero`,
`iter_succ`, `iter_pred` are each a `refl`. If proving "the map preserves the
structure" needs real induction rather than unfolding a definition, something
about the map's construction should probably be reconsidered.

### 4. Prove uniqueness by induction on the SOURCE, package as one theorem

Induction runs on the object being characterized (`Nat`'s own recursor;
`Int.Characterization.induction`), never on the target — a uniqueness proof
that needed to induct on the target would be assuming something about it,
which is exactly what initiality must not do. Package existence and
uniqueness as **one** theorem (`initial`), a conjunction:

```text
(f 0 = z ∧ ∀ n, f (n+1) = s (f n))                       -- existence
∧ ∀ h, (h 0 = z ∧ ∀ n, h (n+1) = s (h n)) → ∀ n, h n = f n -- uniqueness, pointwise
```

so a reader sees "this IS the universal property" in one declaration, not
three separately-motivated lemmas they have to assemble themselves.

## What this is not: categoricity

A **separate**, strictly stronger theorem (`Nat.Peano.categorical`,
`Int.Characterization.categorical`) additionally assumes the *target* itself
satisfies the object's own defining axioms — the Peano axioms; generation +
aperiodicity — and concludes the comparison map is a **bijection**. That is
what pins the object up to isomorphism *among its peers* (ruling out `ℤ/n`,
`ℤ ⊔ ℤ` as models of the weaker `ℤ`-structure axioms alone). Initiality
(parts 1–4 above) needs none of that. Conflating the two overstates what
initiality alone gives you — see ADR-1610's "Alternatives" section for why
they are kept as two declarations rather than one theorem with a comment.

## Applying this to a third carrier

When a second construction of an existing object appears — the roadmap
already names ℝ as the case that will force this ("which construction?") —
state:

1. The family's defining axioms as the new carrier's hypothesis list (part 1).
2. The comparison map as a named `Definition`, built from what already exists
   for the current construction (part 2).
3. The structure-preservation equations, ideally definitional (part 3).
4. Pointwise uniqueness by induction on the *current* construction, packaged
   as one `initial`-style theorem (part 4).

Only once two real instances of a *new* family exist is a generic
`Category`/`Functor` layer justified — not before, per ADR-1610 and the same
"build the concrete thing first" call ADR-1595 and
[ADR-1602](../09-decisions/adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)
already made for algebra and the metric layer.
