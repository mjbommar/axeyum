# The abstraction question has never been asked

**Measured 2026-09-01.** The repository has argued the *aggregate* question
exhaustively and the *abstraction* question not at all.

```
ADRs mentioning aggregates (List / Finset / ...)     281
ADRs on polymorphism / typeclasses / structures        0   (grep returns only
                                                            false positives)
add_inductive call sites in the kernel                98
typeclass/structure machinery in inductive.rs          0
```

`docs/curriculum/foundational-books/axler.md`, landed today, states the
consequence plainly at its Chapter 1 row:

> There is no polymorphism in this kernel's term language, so "for every vector
> space" cannot even be **stated**, let alone proved or refuted. **This is the
> chapter that sets the pattern for the rest of the table.**

Roughly half of Axler's ten chapters are `X-TA` — unavailable for a
**type-theoretic abstraction** reason, not a proof-difficulty one. Their
*concrete* specializations are frequently already proved and axiom-free.

## Why this went unasked, and it is a structural blind spot not an oversight

**The fact ledger is a statement-level mechanism.** It records propositions,
screens them, draws them into partitions, and reports a dispatchable frontier.
Every one of those operations presupposes the statement is *writable*. A
proposition that cannot be expressed never enters the inventory, never gets
screened, never appears as open, and therefore **never appears as missing**.

So the queue can be empty and the frontier can be green while an entire branch
of mathematics is out of reach, and no gate in this repository will say so. The
one artifact that surfaced it is a **curriculum** — a human learning order,
which contains chapters whether or not we can state them. That is precisely the
argument `spivak.md` makes for why a curriculum beats a dependency graph, and it
just paid out in a way nobody predicted.

This session is the evidence: after that finding landed, the coordinator
dispatched lanes at nursery draw mechanics, guard scoping, and individual mirror
closures — all admission plumbing for statements — because the queue is what
reports pressure and the queue cannot see this.

## What ADR-1310 did and did not settle

ADR-1310 decided **"add no aggregate type"** and was right on its evidence: the
determinant needed a *fold*, not a type, and `Nat.Fin` had already been added
with **zero non-test consumers**. But its scope was `List` / `Fin`-indexed
families / `Prod` — **containers**, driven by one theorem. It says so, and it
names its own revisit condition:

> If a genuinely order-sensitive multiset statement ever becomes the priority,
> revisit **then**, with that statement as the driver.

**`axler.md` is that driver, for a different axis.** The question is not "which
container" but "is there any mechanism by which a statement quantifies over a
*structure* — a field, a vector space, a group — rather than over a fixed
carrier." Nothing in ADR-1310 addresses that, and nothing else does either.

Note also that an inductive costs **zero** rows in `Kernel::axiom_footprint`
(`lean_pp.rs` filters to `Axiom | Opaque | Quotient`), and this kernel adds
inductives routinely — 98 call sites. So "we avoid it to protect axiom-freedom"
is not the reason, and must not become the retroactive one.

## The question, stated so it can be answered

1. **Is abstraction reachable here at all?** Lean 4 structures are inductives
   with projections plus elaboration sugar; typeclass resolution is an
   elaborator feature, not a kernel one. This kernel has `add_inductive` and a
   positivity checker. **What exactly is missing — kernel capability, or the
   surface that makes it usable?**
2. **What would the minimal honest version be?** A `Field` structure and one
   theorem quantified over it would settle more than any amount of argument.
3. **What does it cost?** Not in axioms — in the `Nat.Fin` failure mode, where
   a mechanism lands and no development adopts it.
4. **What breaks if we do not?** Name the subjects. Linear algebra past
   Chapter 2 is measured. Abstract algebra, topology and category theory are
   the obvious rest, and that claim should be checked rather than assumed.

**A well-argued "no" is a legitimate answer** — `Nat.Fin`'s zero adoption is
real evidence, and ADR-1310's refusal was correct on its own question. But it
must be *argued against this driver*, and recorded, rather than inherited from a
decision about containers.
