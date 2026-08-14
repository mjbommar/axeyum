# 04 — Implement: what we build, and what we import

**The decision this strand exists to force.** `nat_prelude` is being built by
hand, one theorem at a time — 106 proved, roughly one ADR each — while
**232,000 theorems** sit in Mathlib next door under a permissive licence, and we
already have a reader for them.

Both activities are defensible. Doing both without a stated boundary is not.

## Why building by hand is not obviously wrong

The instinct is that importing dominates. It does not, for three measured
reasons:

1. **An imported theorem carries its source's trust, not ours.** Mathlib's
   232,000 theorems are checked by Lean's kernel. Importing them means our
   kernel *re-checks* them — which is genuinely valuable (see
   [`03`](03-integrate.md)) — but the axioms they rest on are Lean's. Our
   published metric is **assumptions remaining per prelude**, and that number is
   about *our* trusted base.
2. **A hand-built prelude is small enough to be checked by a person.** 106
   theorems with an ADR each is an auditable object. 232,000 is not, by anyone.
3. **The build order teaches us what the kernel is missing.** The last 60
   commits of hand-building surfaced well-founded recursion, certified division
   and gcd's universal property as *kernel* requirements. Importing would have
   hidden those under a translation layer.

## Why importing is not obviously wrong either

1. **ℤ, ℚ and ℝ are enormous and entirely standard.** Nothing about our project
   is improved by re-deriving the reals.
2. **Coverage is the point of the [mathematics strand](../mathematics-2026-08/README.md).**
   Rung 5 says the stack cannot *state* most mathematics. Import is the fastest
   route to statability.
3. **The re-check is itself the contribution.** An independent kernel admitting
   a foreign library is a stronger artifact than the same kernel admitting its
   own library.

## The boundary, proposed

**Build by hand what the trusted base rests on. Import what merely needs to be
stateable.**

| tier | policy | rationale |
|---|---|---|
| **Foundations** — ℕ, ℤ, the order and ring structure our own certificates quantify over | **build** | these are what "assumptions remaining" measures; they are small; and building them exposes kernel gaps |
| **Standard superstructure** — ℚ, ℝ, analysis, topology, algebra | **import**, and re-check | enormous, standard, and we gain nothing by re-deriving |
| **Anything a certificate quantifies over** | **build or re-check to axiom-free** | a certificate resting on an imported axiom inherits it |
| **Everything else** | **import as read-only reference** | usable for statability and coverage; not part of the trusted base |

The line is not "small versus large". It is **"does our evidence depend on
it?"** — which is the same question the engineering strand's precondition work
asks, and the same question the ledger asks of every claim.

## The number that decides this

`#print axioms`. On 2026-08-14 an axeyum development was accepted by Lean's own
kernel and reported **no axioms at all** — strictly smaller than the
`[propext, Classical.choice, Quot.sound]` footprint a competing effort
publishes. Mathlib's content, imported, will not be axiom-free.

So the boundary has an operational test:

> **If importing a declaration would enlarge the axiom footprint of a
> certificate we ship, build it instead. Otherwise import it.**

That is checkable per declaration, it is measurable in aggregate, and it turns
an architectural argument into a number.

## What this means for the current split of work

- The other lane building ℤ from proved ℕ is **correct under this policy** —
  ℤ is foundational and our certificates quantify over it. It should not be
  redirected to import.
- The importer should target **superstructure**, not foundations. Pointing it at
  Mathlib's `Int` would duplicate the other lane's work with a weaker artifact.
- The two meet at ℚ, and that is the first genuine decision point rather than a
  foregone conclusion. Take it deliberately, with the axiom-footprint test.

## What to do first

1. **Write the boundary down as an ADR** when the ADR index is not being touched
   60 times a day — until then, this document is the record.
2. **Instrument the axiom footprint per certificate**, so the test above is
   mechanical rather than a judgement call. Today it is one `#print axioms` line
   run by hand.
3. **Do not import ℤ.** Not because import is wrong, but because two lanes
   producing the same artifact by different routes, with no stated preference,
   is how a project ends up with two Sturm implementations and two colouring
   encoders — [the engineering strand's finding](../refactor-2026-08/02-composition.md),
   arriving in the library.
