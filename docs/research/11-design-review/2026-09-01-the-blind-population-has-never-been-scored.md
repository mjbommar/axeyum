# The blind evaluation population has never been scored

**Measured 2026-09-01, independently of the lane that first reported it.**

Over `artifacts/autogenesis/nursery-v2-extension.json`, joining each entry's
partition against its fact file's `epistemic_status`:

```
development   proved 176   open   4
train         proved 125   open   5
held-out      proved   0   open 190
missing fact files: 0
```

Counting v1 as well, the refill-economics lane measured **206 held-out rows
across 20 families, zero ever settled**, against development 273 proved / 27
open and train 197 proved / 11 open.

**The positive controls are in the same query**, which is what makes the zero
mean something: development and train, drawn by the same generator into the
same manifest under the same screens, are 90%+ settled. The number is not a
tooling artifact.

## Why this is a deficiency and not a backlog item

The held-out partition exists to answer one question — *can this system close
propositions it has never seen?* — and it is the only artifact in the
repository that can answer it. Everything else measures capability against
targets we chose.

The apparatus protecting it is real and this session exercised all of it:

- Draw 17 was **refused** because `Nat.count` is a definitional alias with 22
  existing lemmas and four of its ten rows already proved term-for-term. That
  refusal cost a cycle and was correct.
- `assert_draw_lawful` now enforces a `do-not-draw-held-out` review that
  existed and was **structurally unreadable** — keyed by module name while the
  lookup used family name.
- Guard **G3** refuses a divergence registration that would block an
  already-settled mirror, which caught a genuine two-lane conflict today.
- All seven ADR-0542 amendments on record are **contamination repairs**.

So the project spends real effort keeping this population blind, and has never
cashed it. Each contamination incident spends part of a resource that has
produced no measurement.

## What this does NOT license

**Do not thin the held-out fraction to raise throughput.** The refill-economics
lane considered and explicitly refused that, and it is right: a third of every
draw going to blind evaluation is the cost of being able to make the claim at
all. If the ratio is wrong, the evidence for that is a *scored* population, not
an unscored one.

ADR-0615's stated reason for starting the partition cycle at held-out — that
the surviving blind families were down to two — is over-satisfied tenfold at
20 families and has not been re-measured since. That is a separate question
and also not a licence to shrink.

## The obligation

Score it. A held-out family is dispatched *once*, with the result recorded
whether it closes or not — a failure to close is exactly as informative as a
success and is the reason the population exists. The measurement that comes
back is the first honest answer this project has to "does the flywheel
generalise", and every session that passes without it spends the resource
without reading it.
