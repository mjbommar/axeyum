# ADR-1480: A recorded score is not a breach, and the held-out population is cashed for the first time

Date: 2026-09-01
Status: Accepted
Lane: `score-the-blind-population`

Index-summary: The held-out partition existed for four months to answer one
question — can this system close propositions it has never seen? — and had
never been cashed: 176 proved in development, 125 in train, **0 of 190
held-out**. Not because anything failed, but because
`check-autogenesis-holdout-isolation.py` treated `proved` on a held-out fact as
an unconditional violation, so every route to a recorded score was a gate
breach. This amends that guard: a settled held-out fact is permitted **only**
when a committed evaluation record names it, and that record must carry the
`protocol_commit` that fixed the protocol before the outcomes. Everything else
still fails, pinned by six mutation-verified controls. Cashed against
`integer-absolute-value`, selected by a rule committed before any statement was
read: **10 CLOSED of m = 10**, every row admitted first attempt, axiom-free.

Index-status: Accepted

## Context

Two numbers, measured independently by joining
`artifacts/autogenesis/nursery-v2-extension.json` against `artifacts/facts/`:

| partition   | proved | open |
|-------------|-------:|-----:|
| development |    176 |    4 |
| train       |    125 |    5 |
| **held-out**|  **0** |**190**|

The project spends real effort keeping that partition blind. Draw 17 was
*refused* rather than contaminate one family (ADR-1450). `assert_draw_lawful`
was built to enforce a review that was structurally unreadable.
`check-holdout-closed-evaluation.py` refuses a row the construction already
settles by reduction. All seven ADR-0542 amendments on record are contamination
repairs. And it had never been cashed.

The reason is mechanical rather than anybody's oversight.
`scripts/check-autogenesis-holdout-isolation.py` carried

    SETTLED = {"proved", "computed"}

and failed on any held-out fact reaching either, with no exception. That is
exactly right for every *accidental* route in — the 2026-08-21 incident it was
built for spent 19 of 76 held-out propositions on one theorem — and it is wrong
for the one *deliberate* route the population exists for. A blind evaluation
population that can never be scored is not an evaluation population; it is a
list.

## Decision

**1. A recorded score is not a breach.** A settled held-out fact is permitted
when, and only when, a committed evaluation record under
`artifacts/autogenesis/holdout-evaluation-*.json` names it. The record must be
`state: "scored"`, must carry a `protocol_commit`, and must name only held-out
rows it actually settled.

The `protocol_commit` is load-bearing and is not bookkeeping. **It, not this
gate, is what makes an evaluation blind**: a commit that fixes the selection
rule, the denominator, the attempt order, the outcome taxonomy and the stopping
rule *before* any target statement is read is the only thing separating a
measurement from a story told afterwards. A record that cannot point at one
licenses nothing.

**2. Everything else still fails**, and that is the half worth checking. A
held-out fact settled with no record; a record naming one row while a second is
settled beside it; a record in `draft`; a record without a `protocol_commit`; a
record claiming a row that is still `open`; a record naming a row outside the
held-out population; a record that does not parse. Each is a violation and each
is pinned by a control that only it kills
(`scripts/tests/test_check_autogenesis_holdout_isolation.py`, six new guards,
mutation-verified).

The verdict line gained `recorded_scores=` and `settled=` still counts only the
*unaccounted* ones, so it keeps meaning what it always meant.

**3. `validate_exemptions` is NOT amended.** It still refuses any exemption
naming a held-out row, unchanged. An exemption is a suppression; this is not
one. A scored row is accounted for because the fact about it changed, not
because someone decided to stop looking.

**4. A partition-integrity digest, with its negative control.** Scoring creates
a second hazard the isolation gate does not cover: that while recording a score,
some row quietly changes partition — moved to `development` because it turned
out hard, or to `held-out` because it turned out easy. Neither shows up in a
diff anybody reads, because a manifest of 716 entries is not read line by line.
`scripts/check-drawn-population-zero-diff.py` digests all 716
`(fact_id, partition)` pairs across both manifests and pins the baseline. Its
negative control runs on **every** invocation: recompute with one row's
partition flipped and require the digest to move. Without it the gate would
print a stable digest whether or not the function looked at `partition` at all,
and a digest over `fact_id` alone would pass forever.

## The score

Family selected by a rule committed at `067d675a3` **before any statement in
the family was read**: the lexicographically first held-out family name,
skipping any family this lane had already been exposed to. That exclusion is
not decoration — while learning the manifest's field names the lane printed one
entry in full and so saw `Int.exists_greatest_of_bdd`'s statement, whose family
`descent-and-well-ordering` is lexicographically first. It is disclosed in the
protocol and excluded. The rule then selects **`integer-absolute-value`**.

m = 10 (the whole family), fixed in advance. Attempt order: ascending
`candidate_id`, a SHA-256 digest, so the easy rows could not be tried first.

**10 CLOSED of 10. Every row admitted by `Kernel::add_declaration` on the first
attempt, axiom-free.** Per-row outcomes in
`artifacts/autogenesis/holdout-evaluation-v1.json`; the walk-through, including
what each proof actually needed, is in
[`docs/research/11-design-review/2026-09-01-the-blind-population-scores-ten-of-ten.md`](../11-design-review/2026-09-01-the-blind-population-scores-ten-of-ten.md).

**Read the score with its cause, or it is misleading.** The family was cheap for
one structural reason that is a property of *this construction* and not of the
system's proving ability: `Int.le`, `Int.lt` and `Int.mul` are four-case
COMPUTING definitions over `Nat` here, rather than Lean core's
`NonNeg (b - a)`. After an `Int.rec` split every goal has already ι-reduced, and
a sign hypothesis is *self-discharging* in the branches it excludes —
`Int.le Int.zero (negSucc n)` **is** `False`. Mathlib reaches the same ten
theorems through `abs`, `sq_eq_sq₀` and the linear-ordered-ring API; none of
that was needed or used. **A different family whose content is not
constructor-shaped would not behave this way, and 10/10 must not be read as a
rate.**

## Consequences

* **The family is spent.** Scoring one member is evidence about its siblings —
  that is why the split key is `<family>:<statement-shape>` — so
  `integer-absolute-value` is gone for future blind evaluation. Intended, and
  on the books rather than inferred from a diff. Seventeen of the nineteen
  held-out families remain fully blind; the eighteenth carries the disclosed
  one-row exposure.
* **The zero-diff holds.** Digest `d831a202…` over 716 rows, identical at the
  protocol commit and after scoring. No drawn row changed partition or
  membership.
* **Nothing about this widens what may be *proved*.** It widens what may be
  *recorded*. A held-out fact still cannot be settled quietly; it can now be
  settled loudly.

## What this ADR deliberately does NOT decide

**A scored row's dependency component crosses partitions, and the repair path
for that is blocked.** A proved held-out row necessarily depends on lemmas
established in `development`/`train`, so its declared-dependency component spans
partitions. Measured on this tree: five of the ten scored rows now sit in two
components that `check-autogenesis-nursery.py` reports as crossings.

Three things are established about it, and the fourth is left open on purpose:

1. `check-autogenesis-nursery.py` is **already red on `main`** — verified in a
   detached worktree at `7e2f859dc`: exit 1, the same three violation types, 5
   leaking components, 302 member rows. This is not caused by the scoring.
2. The scoring adds **no new violation type and no new leaking component**. It
   enlarges a component that was already leaking and already covered by a
   now-stale exemption, from 302 to 307 listed rows.
3. An amendment excluding scored rows from the crossing computation was written
   and then **reverted**, because it was measured to be a **pure no-op on this
   tree** — byte-identical guard output with and without it. Shipping an
   unexercised widening of a blindness guard is the failure this repository
   cares most about, arriving in the direction nobody watches.

What stays open: `validate_exemptions` refuses *any* exemption naming a held-out
row, with the reason "a crossing that reaches the blind population is a finding
for review and an ADR-0542 amendment, never a suppression". That is the right
rule for an unscored row and it has no branch for a scored one, so whoever
repairs the pre-existing red will find the sanctioned repair closed to them.
**The review that rule asks for is `holdout-evaluation-v1.json`, and the
amendment it asks for is this ADR** — wiring the two together is the next lane's
decision, and it should be made when there is a crossing whose verdict actually
depends on it.

## Alternatives rejected

* **Leave the guard absolute and never score the population.** This is the
  status quo, and it is what four months of it produced: a partition kept
  perfectly blind and never once read. The cost of the guard was invisible
  precisely because a gate that refuses everything looks identical to a gate
  with nothing to refuse.
* **Score it and suppress the guard for the run.** A spend that is not on the
  books is the 2026-08-21 incident with better intentions.
* **Record the score without flipping the facts.** Considered seriously, and it
  is the fallback the protocol names if this ADR is not adopted. Rejected as
  the primary route because a ledger that knows a theorem is proved and says
  `open` is lying in the direction that looks modest, and the axiom footprint —
  the metric this project actually publishes — would be unreadable for ten
  theorems it has.
