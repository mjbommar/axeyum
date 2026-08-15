# 03 — Integrate

**The question.** How does collected, aligned mathematics get *through*
`axeyum-lean-import` into an independently-checked environment — at population
scale rather than fixture scale?

> **This phase touches contested files.** `crates/axeyum-lean-kernel/` is owned
> by another lane. `crates/axeyum-lean-import/` is not, but it is one edge away.
> Sequence accordingly; see
> [`refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md).

## Where the path actually stands

```
axeyum-lean-import   official lean4export NDJSON 3.1.0, FAIL-CLOSED
                     17 genuine v4.30 fixtures, 10 test suites
K1 (import)          5/5 — on five PINNED SINGLE-ROOT fixtures
real Init/Std        13 of 40 well-known theorems admitted (2026-08-15)
population           dependency-closed Init/Std/mathlib: UNSTARTED
L3                   0/12 — the phase supplying Z, Dvd, finite sums
```

**Update 2026-08-15.** S1 has been run, five times over, at single-theorem
granularity, and it moved S2 ahead of everything else. The reader handled real
Lean output at every size tried and declined nothing; all 27 declines came from
the kernel's definitional equality, in four clusters
([`01-collect.md`](01-collect.md)). At a 13/40 admission rate a fail-closed
importer reports only the FIRST blocker in a stream, so the decline census S2
describes is not a later refinement — it is the only way to size the remaining
work.

The importer is real and its discipline is good: a private staging kernel that
publishes only after the complete stream succeeds, so an error cannot expose a
partial environment; unsupported string literals, unsafe/partial declarations,
unknown records and malformed or forward references all rejected rather than
skipped; quotient records buffered as one exact ordered package through the
kernel's atomic canonical-package gate.

**What has never been tested is scale.** The five streams committed on
2026-08-15 ARE dependency closures — `lean4export` emits the requested constant
plus everything it reaches — but the largest is 2,692 records and 106
declarations, and all five together are 4,919 records. The difference from there to a population is not linear; it is the
difference between a term and a graph with 8.4 M edges.

## The four walls this will hit, all of them already seen

This project has hit the same class of wall four times in one day, and an import
of this size will hit it again. Naming them in advance is cheaper than
rediscovering them:

1. **Materialisation.** `parse_drat` had to hold whole proofs; reconstruction
   held 346 M arena nodes at 24.6 GB; the whnf cache was keyed on a *count*.
   **Assume the importer materialises the stream** until measured otherwise, and
   design the streaming story before the first population run.
2. **The arena.** The kernel's expression arena is monotone and never released —
   measured at ~76–100 bytes per interned node. A 308,129-declaration
   environment is a different order of magnitude from 17 fixtures, and *kernel
   arena checkpointing* is already on the roadmap for exactly this reason.
3. **Per-query rebuild.** Every reconstruction route calls `Kernel::new()` and
   pays ~26 ms of prelude construction, against 6.6 µs to revalidate a cached
   package — **~4,000×**. A large imported environment makes that tax
   proportionally worse, so kernel reuse is a *precondition* for this phase, not
   a follow-up.
4. **A gate that cannot see what it checks.** Formatting was blind to 156
   modules; clippy passed over a cached warning; a validator collapsed 228 errors
   into one message. An import gate must report **what it admitted and what it
   declined**, per declaration, or a partial import will look like a complete
   one.

## The staged plan

**S1 — One dependency-closed slice.** `Init` plus the transitive closure of a
single interesting theorem. Measure: declarations, edges, wire bytes, peak RSS,
wall time, and the decline list. This is the measurement that sizes everything
after it, and the requirements document already names it as the next step.

**S2 — Make declines first-class.** The importer is fail-closed on malformed
input, which is right. For a *population* the useful mode is different: admit
what is admissible, **name every declaration that was not, and why**. A report
saying "admitted 41,203, declined 812, here they are by reason" is a coverage
measurement. A hard failure on declaration 41,204 is not.

This is the same discipline as the claims checker's
`103 claims re-checked, 0 errors, 24 row(s) not re-checked here` — the clause
that names what it could not verify instead of passing silently.

**S3 — Close L3.** L3 is 0/12 and it supplies **ℤ, `Dvd`, and finite sums** —
i.e. exactly the content the [mathematics strand](../mathematics-2026-08/02-the-library.md)
identifies as the keystone. Note the strategic tension and resolve it
deliberately: **ℤ can be imported or constructed, and we are currently doing
both.** The other lane is building ℤ from proved ℕ; the importer could admit
Mathlib's. They are not the same artifact — one has our kernel's proofs behind
it, the other has Lean's — and the difference matters for the assumptions
metric.

**S4 — Population run, with a budget.** Only after S1–S3. Expect to fail; the
value is in *where*, and in the decline census.

## The measurement that makes this strand worth doing

Not "declarations admitted". This:

> **How many of Mathlib's declarations does an independent kernel, written by
> different people in a different language, accept — and where exactly does it
> disagree?**

A disagreement would be a genuinely significant finding about a library 284,457
theorems deep, and finding none is a strong assurance result. Either outcome is
publishable, and axeyum is one of very few systems positioned to produce it,
because it has a second kernel rather than a second copy of the first.

That is also why S2 matters more than S4: **the decline census is the result**,
not the leftovers.
