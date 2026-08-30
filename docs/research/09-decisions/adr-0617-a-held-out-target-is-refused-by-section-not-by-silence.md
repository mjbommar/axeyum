# ADR-0617: A held-out target is refused by section, not by silence

Status: accepted
Date: 2026-08-30
Index-summary: Two tools answered "is this already proved" and only one refused held-out ids; the unguarded one closed ten blind-evaluation rows. The matchers stay separate because each is blind where the other sees, but the dispatcher-side tool now reports the BLOCK first and withholds only the three retrieval sections, and a moved partition must name a recorded ADR-0542 breach (new guard R10)

## Context

`scripts/check-autogenesis-holdout-isolation.py` was FAIL on `main`:
`held_out=127, settled=10`. Ten preregistered blind-evaluation rows were
`proved`, closed by the already-proved sweep `92a61164e`.

### What actually happened, dated

The ten split into two families with **different causes**, and the distinction
decides what the amendments must say. Declaration dates are the first commit
introducing each `<leaf>: kernel.name_str(nat, "<leaf>")` registration.

| family | manifest | preregistered | declarations landed | blind when preregistered? |
| --- | --- | --- | --- | --- |
| `natural-logarithm` (6 rows settled of 21) | nursery-v1 | 2026-08-18 `2d65f19d8` | 2026-08-28 (`3707c6040`, `1dd090dff`, `722d9c204`, `2ccf6322c`) | **yes** |
| `natural-divisibility` (4 of 10) | nursery-v2-extension | 2026-08-29 `94b3e61ee` | 2026-08-13 `46b47f869`, 2026-08-14 `eccaf84ac`, 2026-08-24 `7de26df70` | **no** |

So `natural-logarithm` was genuinely blind for ten days and was spent by
ordinary `log.rs`/`clog.rs` development that never mentions the mirror
programme — the `natural-binomial` shape ADR-0542 already records. And
`natural-divisibility` was **never blind**: it was preregistered against
theorems that had been admitted for 5 to 16 days, which is the debt ADR-0615
recorded as owed at "4 of 10".

**The sweep caused neither.** Every declaration predates it, so it recorded a
spend rather than making one, and none of the ten facts is reopened here: they
are genuinely proved and their evidence re-derives.

**The measured figure is worse than 4 of 10, and the reason is general.**
`F:ml430-nat-dvd-mul-right-a87a83c4` is satisfied by a declaration we named
`Nat.dvd_mul`. R9 — the generator's blindness screen — matches Mathlib **names**
and is therefore structurally blind to a proposition already proved under a
different name. Only the type-comparing ranker in `scripts/brief-step0.py` saw
it. Conversely, three of that sweep's four false positives were
`natural-divisibility` rows whose constants matched but whose argument order did
not, which a name screen would never have proposed.

### The mechanical cause

Two tools answer "is this already proved", and they differ in a guard:

* `check-autogenesis-already-proved.py` refuses a held-out id **even when named
  explicitly**, and its docstring says so. Its author built that in.
* `brief-step0.py`, written hours later for the same job, did not. It reported
  held-out in **section 4** — after section 1 had already printed the
  already-proved verdict and named the declaration.

The sweep used the second. The warning arrived after the leak.

### And the amendment ADR-0542 prescribes had nothing to bind to

`create-autogenesis-mathlib-nursery-split.py` regenerates `nursery-v1.json`
from the ledger, so a v1 amendment is enforced. The v2 extension had no such
link: `frozen_partitions` froze `family_partitions`, so the manifest was its
own authority. A hand edit that moved a family **and** recomputed
`extension_sha256` regenerated perfectly clean, with no amendment anywhere. A
digest catches a careless edit, never a deliberate one.

## Decision

**1. Both families leave held-out, with separate amendment reasons.**
`natural-logarithm` (21 rows) and `natural-divisibility` (10) move to
`development` under ADR-0542's whole-family rule. Their `reason` strings record
the different causes rather than a shared formula, because "was blind and was
spent" and "was never blind" are different findings about the programme.
Held-out re-freezes at **96**: `natural-square-root` 16 (v1) and eight v2
families at 10 each.

**2. A moved partition must name a recorded breach — new guard R10.**
`nursery-v2-extension.json` now carries `preregistered_family_partitions`
beside `family_partitions`; `frozen_partitions` freezes the former, giving the
effective assignment an immovable reference. R10 requires every difference
between the two to be an ADR-0542 amendment with matching `from`/`to`, and
refuses an amended family recycled back into held-out.

R8's move-check becomes R10's; R8 keeps only "a preregistered family keeps
existing". This is not tidying. Re-aiming R8 at `preregistered_assignment()`
was tried and is **worse than useless** — that function derives from `frozen`,
so the two can never disagree and the guard cannot fail. Two further drafts of
R10 had the same shape: comparing `assign_partitions()` against
`preregistered_assignment()` makes both the no-amendment branch and the
destination branch unreachable, because the ledger is applied last and the two
then agree by construction. R10 reads the two dicts the **manifest** records,
which is what makes every branch reachable.

**3. `brief-step0.py` refuses a held-out target by SECTION, not by silence.**

Copying the sibling's blanket refusal would be the wrong repair, because the two
tools have different consumers. The sibling screens a set and its output is a
report; going quiet costs a line. `brief-step0.py` is run by the **dispatcher**
on a specific target, and its whole output is what a brief should contain — so
"this is held-out, do not dispatch it" is the single most valuable sentence it
can produce. A tool that exits silently on exactly the target where the
dispatcher most needs an answer sends them to a less careful method, which is
how the sweep happened in the first place.

So the split is by section:

* the **BLOCK is reported first and loudly**, and the run exits **5**;
* sections 1–3 (already-in-the-environment, near misses by shape, modules to
  read) are **withheld**, because naming the declaration whose rendered type
  matches a blind proposition *is* the proof route, and so is a shape near miss,
  and so is "read these modules".

The check is **fail-closed**: an unreadable partition, or an empty held-out
population, refuses rather than reporting. `blocked_report` degrades to
UNANSWERABLE and keeps going, which is right for a section that only annotates
and wrong for the check that decides whether the retrieval sections run at all.

There is deliberately **no override flag**. An escape hatch a lane can pass is
how a guard stops being one, and the legitimate route already exists: record an
amendment, after which the row is not held-out and the tool answers normally.
The amendment is the flag, and it leaves a breach record where a flag leaves
nothing.

**4. The two tools are NOT merged; the guard is what gets shared.**

They look like duplicate implementations and are not. The name screen is blind
to a proposition proved under another name (`Nat.dvd_mul` for
`Nat.dvd_mul_right`); the constant-multiset screen is blind to argument order
(4 false positives in 25 exact-constant candidates, three of them in this same
family). Each catches what the other misses, and their costs differ — the name
screen is a dictionary lookup over the dispatchable set, the type screen ranks
every open statement against every rendered type. Collapsing them would delete
a real check.

What was duplicated is the **guard**, and that is exactly what differed. So the
sibling gains the fail-closed empty-population check it never had (its refusal
is `set(fact_ids) & held`, unreachable when `held` is empty), and both tools now
refuse rather than report when blindness cannot be established. Three readers of
the two manifests remain — this tool, the frontier module, and the isolation
gate — and consolidating them is left open; they agree today and none of them
was the cause.

## Consequences

* Held-out breadth is **96**, and the honest reading of that number is bounded
  in one direction only: measured against a 2,289-declaration snapshot with
  both controls passing, the nine remaining families show **0** already-declared
  by name and **0** exact-constant candidates by type. The snapshot is STALE by
  five named leaves, none in these families' namespaces, and a stale snapshot
  can produce a false ABSENT but never a false PRESENT — so 96 is an **upper
  bound** on blind breadth, not a floor.
* Neither screen measures "hard". A row provable in one line from existing
  machinery matches neither, so 96 counts rows that are *not already proved*,
  which is a weaker property than *blind and unattempted*.
* `nursery-v2-extension.json`'s own `limitations` still record that no
  dependency-component analysis was run for it, so a v2 held-out row can share
  a component with a dispatchable one and nothing in that manifest sees it.
  That erosion is unquantified and is **not** included in the 96.
* `brief-step0.py` exit 5 is new. A caller that treated any nonzero exit as
  "tool broken" will now see a refusal as breakage; the refusal prints its own
  reason and the remedy.

## Alternatives rejected

**Reopen the ten facts.** They are genuinely proved, the kernel declarations
predate the sweep, and the evidence re-derives. Reopening would falsify the
ledger to tidy a partition.

**Delete the two families' rows.** ADR-0542 already rejected this for
`natural-gcd`: it shrinks the population and hides the cost. The rows stay
fully usable in development, where looking is allowed.

**Move only the contaminated rows.** `partition_unit` is
`whole-family-with-source-review-groups-indivisible`, and `log.rs`'s shared fuel
recursion and `divisibility.rs` are evidence about every sibling. Splitting
would repair a leakage breach by violating the anti-leakage invariant.

**Give `brief-step0.py` the sibling's blanket refusal.** Rejected in decision 3:
it withholds the one answer the dispatcher needs and pushes them to a less
careful method.

**Add `--spend-held-out`.** Rejected. A flag a lane can pass leaves no record;
an amendment leaves a breach.
