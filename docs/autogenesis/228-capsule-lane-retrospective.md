# What P0–P2 changed, why it was necessary, and what to do differently

Date: 2026-08-22

Plan: [`226`](226-production-measurement-and-general-producer-plan.md) ·
Incident: [`227`](227-held-out-partition-breach-result.md) ·
Decision: [ADR-0542](../research/09-decisions/adr-0542-held-out-partition-breach-repair.md)

This is written for the lane registering kernel capsules, and for whoever picks
that work up next. It is not a complaint about it — most of what that lane built
is good and is still standing. It is an account of three things that were
structurally impossible to notice from inside the work, and of the gates that
now notice them for you.

## The three findings, in one table

| | Measured | Why it mattered |
|---|---|---|
| The held-out partition was breached | one operation named a `held-out` fact; the family is the unit of contamination, so **19 of 76** rows were spent | the programme's stated guarantee is "every policy improvement is evaluated against immutable held-out populations" |
| The registry is a dispatch table | **24 operations, 23 facts covered, 0 naming more than one fact, 0 of 144 ready facts covered** | an operation per target cannot fail to "produce" and cannot produce anything nobody wrote |
| Production was unmeasurable | no cross-prelude theorem counter existed; the real total is **418**, not the 139 the one existing counter reported | a metric that cannot move is worse than no metric |

## Timeline, measured from the artifacts

```text
08-18 16:xx  nursery frozen: train 78 / development 60 / held-out 76
08-19        reflexivity coverage census over 138 rows: 114 / 15 / 7 / 2
08-21 19:20  operations = 15
08-21 ~20:xx registration of a capsule naming F:ml430-nat-gcd-greatest-0a04214a
             -- partition: held-out, family: natural-gcd
08-22 03:17  operations = 21, pin = 21          (the lane had tracked it exactly)
08-22 04:16  operations = 22, pin = 21          (ratchet goes red)
08-22 05:26  operations = 24, pin = 21
08-22 07:16  operations = 24, pin = 21          (red 3 h; two capsules landed meanwhile)
```

Nine capsules in ten hours, each with a plan doc, a result doc, a receipt, a
gate and a reproduction command. The velocity and the care are both real. What
none of it could show is that the *shape* of the output had stopped changing.

## What we changed

**P0 — containment.** `natural-gcd` moved out of held-out **as a whole family**,
because the policy's own `partition_unit` is
`whole-family-with-source-review-groups-indivisible` and splitting it would have
repaired a leakage breach by breaking the anti-leakage invariant. Held-out
re-froze at 57 rows / 3 families; train+development rose 138 → 157. The move is
recorded in an amendment ledger carrying the breaching fact id, operation id,
commit and dates, and **a family assigned back to held-out is now a generator
error** — the spend is irreversible by construction rather than by convention.

`scripts/check-autogenesis-holdout-isolation.py` now fails if any held-out fact
is settled by *any* route, or if any artifact outside the two files that define
the population references a held-out fact id.

**P1 — measurement.** `prelude_theorem_inventory` +
`gen-theorem-production-ledger.py` count theorems across all eight preludes:
**418 distinct, all axiom-free**. `gen-production-provenance-ledger.py` splits
those results by who produced them: of 136 established facts, **0** came through
an operation covering more than one fact.

**P2 — the ratchet.** Both generality counters are gated by value. A new
single-target capsule cannot move them, so activity can no longer be mistaken
for production.

## Why it had to be done rather than noted

Three separate instruments were pointed at this work and none of them could see
any of it:

- `check-autogenesis-nursery.py` validates the manifest's *internal* integrity —
  no family, shape, source group or component crosses a partition — and never
  inspects what operations do to the population it describes.
- `validate-autogenesis-operations.py` mentioned `partition`, `nursery` and
  `held-out` **zero times**.
- the README's immutability guarantee was prose.

That is this repository's most-repeated failure shape, and it is why the fix had
to be a gate rather than a paragraph. A doc line did not stop a whole lever being
built on a fabricated verdict in `explain_corpus`; 40 of 162 checker runs exited
0 on completion alone; a corpus gate ran zero tests for 15 days. **The rule that
generalizes: if a guarantee has no gate, it is a wish, and the next lane will
violate it without ever seeing it.**

## What was not wrong

Worth stating plainly, because the findings above are easy to over-read:

- **The capsules are real, checked work.** Each carries an independently checked
  kernel goal, a replayable receipt, and negative controls on its adapter.
- **The lane tracked its own ratchet exactly** through 21 operations — 15, 16,
  17, 18, 19, 20, 21 all pinned in the same commit as the registration. The red
  window is recent, not chronic.
- **Doc 16 and doc 17 got the strategy right.** "The next action is not to import
  Mathlib answers or hand-author proof plans… aggregate typed declines by family
  … the first capability acquisition should be chosen from that measured
  bottleneck." That is exactly right, it was written before any of this, and it
  is what P3/P4 now resume.
- **The 2026-08-19 reflexivity census is the census the plan asks for**, run with
  a genuinely generic producer, and it already names the dominant cluster:
  **114 of 138 rows — 83% — died in the adapter on a proof-bearing dependency.**

## What to do differently

**1. Choose the next target from the frontier, not from the neighbourhood.**
Nine of the ten most recent operations are Fibonacci/gcd. Picking the adjacent
theorem is how a lane ends up with nine capsules and zero generality. `just next`
and `scripts/fact-frontier.py` exist for this.

**2. Before writing a capsule, ask what the next three targets share with it.**
If the answer is "nothing — each needs its own route," that is the finding, and
it belongs in a decline record rather than in three more capsules. If the answer
is a shared shape, build the operation for the shape and register it against all
of them. `applicability.fact_ids` takes a list; nothing ever required it to have
length one.

**3. Widen an existing operation before adding a new one.** The provenance
ledger now counts operations covering more than one fact. That number rising is
the only thing in this programme that distinguishes a producer from a person.

**4. Regenerate every artifact downstream of the population in the same commit.**
When train/development changes size, these go stale together, and two of them
were already stale before P0 touched anything:

```sh
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py
python3 scripts/gen-autogenesis-baseline.py
python3 scripts/create-autogenesis-reflexivity-coverage-input.py   # needs the Lean capture
```

**5. Move a pin in the same commit as the thing it pins.** The operations-count
ratchet has been red for three hours across two further registrations. A ratchet
that is red by default stops being read, and this one is the instrument that
would have shown the registry growing without generalizing.

**6. Do not pin a number another lane moves hourly — pin a floor.** An equality
on `already_established` went red every time anyone registered a capsule, so it
got bumped without being read. `assertGreaterEqual` still catches the regression
that matters and leaves legitimate growth alone.

**7. A test that names a specific fact expires silently.**
`test_established_row_is_not_redispatched` set a hard-coded fact to `proved` — a
fact another lane had already proved, making the mutation a no-op. It passed
while testing nothing. Select the subject from the live population instead.

**8. When a claim is about a population, check the population's own metadata
first.** "138 dependency-ready facts" and "train + development = 138" are the
same number and different sets — the ready set is 44 train, 44 development and
**50 held-out**. Two of us nearly proposed pointing a producer at it.

## What the gates now do for you

You no longer have to remember items 1–4 above:

| Gate | Refuses |
|---|---|
| `check-autogenesis-holdout-isolation.py` | any settled held-out fact; any reference to one from any artifact |
| `create-autogenesis-mathlib-nursery-split.py` | an amended family assigned back to held-out; an amendment without its breach record |
| `gen-production-provenance-ledger.py --check` | a stale generality count, an unknown `proof_route`, an operation not in the registry |
| `gen-theorem-production-ledger.py --check` | a moved theorem count, and it names the direction — a fall is never re-pinned quietly |

## The one-line version

The work was careful and the machinery is sound; what was missing is that
**nothing in the loop measured whether the output was getting more general, so
nine hours of real work moved the metric that matters by zero.** That number is
now on the flywheel dashboard, and it is the one to watch.

## What comes next

P3 in [`226`](226-production-measurement-and-general-producer-plan.md), with one
addition this retrospective makes concrete: the 2026-08-19 census has **no
must-decline negative controls**. The nursery's twelve mutated statements are
`answer_access: unavailable` — externally *unknown*, not known-false. A producer
evaluated only on true statements cannot be shown to fail, which is the
checker-that-cannot-fail lesson never yet applied to a producer.
