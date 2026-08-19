# 04 — Implement: what we build, and what we import

**The decision this strand exists to force.** `nat_prelude` is being built by
hand, one theorem at a time — 106 proved, roughly one ADR each — while
**284,457 theorems** sit in Mathlib next door under a permissive licence, and we
already have a reader for them.

Both activities are defensible. Doing both without a stated boundary is not.

> **The boundary below was taken, and the build side won on the ground.**
> Re-measured 2026-08-19: `nat_prelude` holds **139** theorems, and ℤ, ℚ, the
> constructed ℝ and ℂ have been proved out natively — the kernel reads
> `complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30`,
> with `real` being the *axiomatized* package the constructed carrier replaces.
> So "106" below is a 2026-08-14 figure kept for the argument it supports, and the
> tier table's "**import** ℚ, ℝ" row describes a policy that events overtook:
> both were built. That is a finding about the boundary, not a violation of it —
> the deciding question was always "does our evidence depend on it?", and our
> certificates quantify over ℝ.

## Why building by hand is not obviously wrong

The instinct is that importing dominates. It does not, for three measured
reasons:

1. **An imported theorem carries its source's trust, not ours.** Mathlib's
   284,457 theorems are checked by Lean's kernel. Importing them means our
   kernel *re-checks* them — which is genuinely valuable (see
   [`03`](03-integrate.md)) — but the axioms they rest on are Lean's. Our
   published metric is **assumptions remaining per prelude**, and that number is
   about *our* trusted base.
2. **A hand-built prelude is small enough to be checked by a person.** 106
   theorems with an ADR each is an auditable object. 284,457 is not, by anyone.
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

That sentence survives 2026-08-18's finding, but say it precisely now that
"Lean" is ambiguous: it was Lean's **kernel**, and on the whole constructed-real
carrier the kernel takes all 470 declarations while the **elaborator** refuses
four ([`03-integrate.md`](03-integrate.md#lean-has-two-checkers-and-they-disagree)).
The axiom-freedom claim is unaffected — it is a property of the footprint, not of
which Lean read the file — but any *comparison* against another project's
`#print axioms` has to state which checker produced it, or it compares two
different measurements.

That test is no longer hypothetical, and it is now measured in **both**
directions. Imported 2026-08-15: four of the five first imports
(`Nat.le_refl`, `Nat.le_succ`, `List.nil_append`, `Bool.and_comm`)
reach no Lean axiom at all, and `Classical.em` costs exactly
`[propext, Classical.choice, Quot.sound]` by Lean's own `#print axioms`.

But the two kernels do not spell the answer the same way: on the same imported
`Classical.em`, `Kernel::axiom_footprint` reports **six** names, adding `Quot`,
`Quot.mk` and `Quot.lift`, because it counts the whole quotient package as
trusted surface. Ours is the more conservative reading. So the operational test
below has to name **which kernel's footprint** it is comparing, or it silently
compares two different numbers. See
[ADR-0454](../research/09-decisions/adr-0454-imported-kernel-lean-proof-route.md).

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
  **Settled 2026-08-19: ℚ was built.** It reads `rat: axiom=0 opaque=0
  quotient=0` from the kernel, and the constructed ℝ and ℂ were built on top of
  it. The axiom-footprint test would have given the same answer — a certificate
  quantifying over an imported ℚ inherits Lean's axioms — but the decision was
  taken by construction rather than by argument, so record it as an outcome
  rather than as evidence that the test was applied.

## What to do first

1. **Write the boundary down as an ADR.** The reason this was deferred is
   gone: the ADR index is now *generated* (`python3 scripts/gen-adr-index.py`),
   so concurrent lanes no longer contend on it. ADR-0454 settles the narrower
   question of how an imported fact is labelled; the tier boundary in the table
   above is still unwritten.
2. ~~**Instrument the axiom footprint per certificate**, so the test above is
   mechanical rather than a judgement call. Today it is one `#print axioms` line
   run by hand.~~ **Done — verified 2026-08-19.**
   `cargo run -p axeyum-solver --features full --example front_door_carrier --
   --require-axiom-free` reads `Kernel::axiom_footprint` off the shipped front
   door's own refutations and **makes the exit status depend on the finding**:
   nonzero unless every fixture reconstructs over `CReal` with an empty carrier
   footprint, the `Real` control is non-empty on every fixture (so a broken
   measurement cannot read as success), and the emitted module names the
   constructed carrier. It exits 0 today at 12 / 17 / 8 carrier axioms over
   `Real` and 0 / 0 / 0 over `CReal`.
3. **Do not import ℤ.** Not because import is wrong, but because two lanes
   producing the same artifact by different routes, with no stated preference,
   is how a project ends up with two Sturm implementations and two colouring
   encoders — [the engineering strand's finding](../refactor-2026-08/02-composition.md),
   arriving in the library.
