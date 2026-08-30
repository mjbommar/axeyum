# ADR-0695: The construction spends the closed rows, not the evaluation test

Status: accepted
Date: 2026-08-30
Index-summary: ADR-0653 exempted the mandatory `Definition` evaluation test from its "declare the construction and nothing else" rule on the ground that a test is not a declaration; that exemption is true and beside the point, because `Nat.fermatNumber 0 = 3` is decided by REDUCTION the moment the definition is admitted and three held-out `fermat-numbers` rows were spent 21 minutes before draw 7 preregistered them — so the evaluation test stays mandatory and unchanged, and a new draw-time and standing screen refuses any held-out row the construction already settles

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0615
(the evaluation envelope is per cohort), ADR-0645 (draw 6 declined),
ADR-0653 (an unblocking lane declares the construction and nothing else)

## Context

ADR-0653 established the rule after the `Nat.dist` lane proved seven
supporting theorems alongside the construction it was sent to declare, five
of them exact Mathlib mirror names, and R9 correctly refused the family:

> **A lane sent to unblock a held-out family declares the CONSTRUCTION and
> nothing else.**

It then wrote one sentence more, which is where this ADR starts:

> the evaluation-test requirement for a new `Definition` is safe here
> precisely because a test is not a declaration.

That sentence is true and it does not do the work it was asked to do. Twenty
hours later the `Nat.fermatNumber` lane followed ADR-0653 exactly — definition
only, no theorems — and draw 7 still preregistered a family that was 3 of 10
spent.

## What was measured

Timestamps re-derived with `git log --reverse -S` (`git log -1 -S` gives the
NEWEST commit touching a string, which is how an earlier reading of this got
the order wrong), and the order confirmed by ancestry:

```
0065c83b1  2026-08-30 06:48:10  feat(nat_prelude): declare Nat.fermatNumber, definition only
29d51bd0b  2026-08-30 07:09:52  feat(autogenesis): draw 7
git merge-base --is-ancestor 0065c83b1 29d51bd0b   -> YES
```

Three of the family's ten rows are, verbatim from `artifacts/facts`:

```
Nat.fermatNumber 0 = 3      Nat.fermatNumber 1 = 5      Nat.fermatNumber 2 = 17
```

Each is a closed equation between a constant applied to numerals and a
numeral. Once `Nat.fermatNumber` is admitted, each is decided by reduction and
closes by `Eq.refl`. **No theorem had to be declared and no test had to be
written for those rows to stop being blind.** The same commit's
`fermat_number_evaluates_correctly` asserts all three by `Kernel::def_eq` —
verified present at that SHA — but that is the running demonstration the
reduction fires, not the mechanism of the spend. Deleting the test would not
make the rows blind again.

R9 screens the Mathlib **source names** (`Nat.fermatNumber_zero` and its
siblings), none of which is declared here, so it reported a clean 0 of 10 and
was right about the question it asks.

## The tension, and why it dissolves

Two repository rules appeared to be in direct conflict:

- CLAUDE.md: **every new `Definition` needs an evaluation test**, because the
  trusted gate cannot tell you a definition is wrong — a function that computes
  the wrong value has the right type. `Nat.lor` and the Bézout witnesses are
  the incidents behind that rule, and both were caught by evaluation and by
  nothing else.
- ADR-0653: an unblocking lane must not write down the mathematics of the
  family it is opening.

If asserting `fermatNumber 0 = 3` is what spends the row, the two rules cannot
both hold: one demands the assertion and the other is defeated by it. Three
repairs suggest themselves and each has a real cost — evaluate at arguments the
pool does not contain (and lose the discriminating case the values were chosen
for); declare first, draw, then add the test (and leave a definition unverified
in between, which is exactly what the evaluation rule exists to prevent); or
accept the spend.

**The conflict is not real, because the test is not the cause.** The
`Definition` is a declaration, it is admitted before any test runs, and from
that instant every closed evaluation over it is decided. The choice was never
between a verified definition and a blind family; the family stopped being
blind at `add_declaration`.

## Decision

**1. The evaluation-test requirement is unchanged and remains mandatory.** No
delay, no relocation, no weakening. It is not the leak, and treating it as one
would trade a real soundness guard for an imaginary blindness guard. ADR-0653's
exemption sentence is superseded by this ADR — not because it was wrong, but
because it answered the wrong question.

**2. Discriminating arguments stay discriminating.** Do not steer an evaluation
test away from a row's values. Picking arguments to dodge a nursery pool is how
`Nat.lor`'s absorbing-zero defect gets shipped: it type-checks, and only
evaluation at the argument that matters catches it.

**3. A draw may not take a held-out row that the construction already
settles.** A row is *closed-evaluation* when its Mathlib proposition is a
binder-free equation whose vocabulary is numerals and constants already
declared in this kernel. Such a row is decided by reduction; it is not blind,
whatever anyone has or has not proved about it. `check-holdout-closed-evaluation.py`
enforces this over the standing population and is registered in `just check`.

**4. An unblocking brief states the screen, not just the prohibition.** "Declare
the construction and nothing else" is necessary and not sufficient. Add: *before
drawing, list the pool's rows that are closed equations over the constant you
just declared, and exclude them.* For `Mathlib.NumberTheory.Fermat` that is
three of thirteen, which is knowable from the pool before any code is written.

**5. `fermat-numbers` is amended out of held-out as a whole**, per ADR-0542's
`whole-family-with-source-review-groups-indivisible` unit, with the ledger row
recording the reduction as the cause and the test as a witness. No row deleted,
no fact reopened. Held-out 136 -> 116 across 12 families, together with the
`natural-parity` amendment landing beside it.

## Alternatives rejected

**Delay the evaluation test until after the draw.** Rejected on the strongest
ground available: it leaves a `Definition` in the environment that nothing has
checked computes the right value, for exactly as long as the draw takes. The
kernel cannot tell you it is wrong, and three separate wrong definitions were
caught by evaluation in one day. Also it does not work — the rows are spent by
the definition, so the draw would still be preregistering settled rows.

**Evaluate only at arguments outside the pool.** Rejected. It weakens the test
where it is most load-bearing (see decision 2), and it is not sound anyway: the
pool takes the alphabetically-first ten rows, so which values are "outside" it
is an artifact of naming rather than of mathematics.

**Screen at draw time only.** Rejected as insufficient, not as wrong. A
draw-time screen cannot see a construction declared *after* the draw, which is
a live route to the same spend. The standing gate covers both; the draw-time
rule (decision 4) makes the refusal cheap by catching it before a family is
authored.

**Widen R9 to definitions.** Rejected. R9 asks whether the Mathlib source NAME
is declared here, which is a different and still useful question; the names
`Nat.fermatNumber_zero` and friends genuinely are absent. Overloading one screen
with two criteria makes both harder to reason about, and the reduction question
needs the row's STATEMENT, which R9 never reads.

## Consequences

- `check-holdout-closed-evaluation.py` is registered and green:
  `held_out=116|closed_shaped=0|violations=0|snapshot_declarations=2383|fixtures=10|verdict=PASS`.
  Its classifier is self-tested on every run against a pinned fixture table,
  because a clean population would otherwise let it pass vacuously — the defect
  this repository finds in its own checkers more than any other.
- The gate reads the committed environment snapshot, which goes stale
  **fail-open** for this screen: a construction declared minutes ago reads as
  absent, so its rows read as blind. That is the exact 21-minute window Fermat
  opened. Mitigated with a source-level fallback that over-approximates
  "declared", which can only make the gate refuse a draw, never admit one. The
  snapshot's own note claims it "can only go stale in the fail-closed
  direction"; for this screen and for R9 that is backwards.
- `Mathlib.NumberTheory.Fermat` remains good supply for development. Only its
  blindness is spent, and seven of its ten rows — coprimality, monotonicity,
  oddness, `fermat_primeFactors_one_lt`, `pow_of_pow_add_prime` — are genuinely
  unproved here.
- The next unblocking constant should be screened for this before it is
  declared, not after. `Nat.nthRoot` and `NatCast.natCast` are ADR-0653's other
  two candidates; both need the closed-equation count over their pools taken
  first.
