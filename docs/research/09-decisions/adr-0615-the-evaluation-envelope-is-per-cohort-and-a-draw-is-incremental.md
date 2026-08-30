# ADR-0615: The evaluation envelope is per cohort, and a draw is incremental

Status: accepted
Date: 2026-08-29
Index-summary: Apply nursery-v1's 100..300 envelope per COHORT rather than to the sum, freeze preregistered partitions against regeneration, never rewrite an emitted fact, and refuse a held-out candidate we already declare

## Context

The autogenesis flywheel's input queue emptied on 2026-08-29
([design review](../11-design-review/2026-08-29-the-mirror-population-is-consumed.md)).
A refill (`94b3e61`) took the dispatchable set 0 → 50 at 17:22. Lanes closed
**39 of those 50 between 18:03 and 19:19**, and the ledger's whole-day figure is
**60 `ml430` mirrors flipped to `proved`** (135 → 195). The dispatchable set is
back to **11**, nine of them one family.

A lane attempted a second draw and refused, with arithmetic that re-measures
correctly: `PER_FAMILY = 10`, a `(held-out, development, train)` cycle that
restarts at held-out per draw, and R5's "at least two new held-out families"
together fix the smallest compliant refill at **4 families = 40 rows**; the
combined population is **294** against `EVALUATION_CEILING = 300`. It named
three options — raise the ceiling, allow extending an existing family, or shrink
`PER_FAMILY` — and said all three were recorded decisions, not a lane's.

That refusal was right. Its stated reason was the **least** of three blockers,
and the other two destroy data rather than merely refusing.

## Decision

**Four changes, and the ceiling raise is not one of them.**

1. **The `100..300` envelope is applied per COHORT, as it is written.**
   `EVALUATION_CEILING` (a sum bound) is replaced by `EXTENSION_CEILING =
   V1_EVALUATION_ENTRIES`, a bound on the quoted cohort alone, and v1's own
   range is now **asserted** by the generator rather than assumed.
2. **A draw is incremental.** A family an earlier draw preregistered keeps its
   partition; the assignment cycle runs over the new families only. New guard
   **R8**.
3. **A fact is emitted once and never rewritten.** A preregistered fact is
   immutable in what preregistration binds (`id`, `title`, `formal.*`) and
   mutable in what the ledger owns (`epistemic_status`, `evidence`,
   `depends_on`).
4. **A held-out candidate whose Mathlib name we already declare is refused.**
   New guard **R9**.

`PER_FAMILY` stays 10 and R5 stays. Extending an existing dispatchable-eligible
family is rejected. Both are argued under *Alternatives*.

## Evidence

### Where 300 comes from, and what it was protecting

`EVALUATION_CEILING = 300` was introduced **the same morning** (`94b3e61`), and
its comment cites its source honestly: *"R3 — the ceiling. v1's policy caps the
evaluation population at 300."* That is a faithful transcription of
`artifacts/autogenesis/nursery-v1.json`:

```json
"evaluation_fact_count": { "minimum": 100, "maximum": 300 }
```

pinned as a literal in `scripts/check-autogenesis-nursery.py:82` as *"the
100..300 programme range"*. The range enters on 2026-08-18 (`2d65f19d8`,
`c9717b3bc`) with two authorities:

- **ADR-0478**: *"it must report not ready until it contains 100–300 evaluation
  facts, all three evaluation partitions, real declared dependency depth,
  multiple provenance and route-hypothesis families, mutations, and at least one
  held-out component."*
- **Roadmap task AG2.3**: *"define 100-300 provenance-classified Nat/Int facts
  with real dependency depth, route diversity, mutations, and held-out
  components for sustained evaluation."*

So **300 is the upper end of a design-time sizing envelope, written when the
population was zero** and the question was how large an evaluation set had to be
before it meant anything. In every consumer the **floor** is what does work:
`docs/autogenesis/11-nursery-foundation-result.md` lists *"the 100–300
population floor"* first among nine `ready=false` blockers, and `--require-ready`
exists to fail until the population is big enough. The maximum had never
rejected anything until 2026-08-29.

It also does not bound what a ceiling would need to bound. Per-row evaluation
cost is a lane proving a theorem, which is the same whether or not the row sits
in one manifest; held-out dilution is governed by the leakage rules and the
`<family>:<statement-shape>` split key, not by a total; per-fact review is
`validate-facts.py`, per fact.

**And it never governed the sum.** `check-autogenesis-nursery.py` sets
`NURSERY = artifacts/autogenesis/nursery-v1.json` and computes `evaluation` from
that manifest's own entries. The 300 is a per-manifest bound on v1's 214. R3
applied it to `V1_EVALUATION_ENTRIES + len(entries)` across two manifests — a
stricter reading than any rule states, made when the sum was the only thing in
view, and the reading that made the second draw impossible.

### The two blockers nobody had measured

**Fact clobber.** `gen-autogenesis-nursery-refill.py --check` was **already red
on main**:

```
autogenesis-nursery-refill: 39 generated file(s) are stale, first
  artifacts/facts/F-ml430-int-add-le-add-a76ad5ce.json; regenerate without --check
```

39 is exactly the number of draw-1 mirrors lanes closed. The generator rebuilt
every fact file for every entry, so its own printed advice would have overwritten
39 `proved` facts with fresh `open` stubs — discarding evidence rows and status
flips from five lanes. The ceiling had been shielding the ledger from the
generator by accident.

**Silent repartition.** `assign_partitions()` derived every family's partition
from one cycle over all of `FAMILY_MODULES`, and the generator never read its own
prior output. Simulated by adding four plausible new families to the eight from
draw 1:

| family | draw 1 | after adding 4 |
| --- | --- | --- |
| integer-order | development | train |
| natural-division | **train** | **held-out** |
| natural-divisibility | held-out | development |
| natural-lcm | development | train |
| integer-parity | train | development |
| natural-parity | held-out | train |
| natural-totient | development | train |

**Seven of eight move.** `natural-division` is 8 of 10 proved; moving it into
held-out manufactures a blind population out of rows whose answers are
published. Neither existing guard sees it: **R6** re-derives the assignment from
the same function the emitter used, so both agree on the new wrong answer, and
**R1** only forbids a family crossing partitions *within* one manifest.

### What the held-out partition is worth, and what the right size is

Held-out today is **67 rows / 5 families / 16 distinct `<family>:<shape>` split
keys** — `natural-logarithm` 21, `natural-square-root` 16 (v1), and
`integer-division`, `natural-divisibility`, `natural-parity` at 10 each (v2).

The number that decides sizing is not the count but the **attrition**. v1 froze
with four held-out families; **two were amended away within seven days**
(ADR-0542: `natural-gcd` 08-22, `natural-binomial` 08-25). Neither loss came
from dispatching at a held-out row. One was an operation registered against a
held-out fact; the other was **ordinary, unrelated hand development in
`choose.rs`** that had already proved 5 of 20 rows before anyone noticed. So the
blind population decays at roughly **half its families per week**, driven by the
development happening beside it rather than by any failure of evaluation
discipline.

That reframes the question. "More held-out rows" is not the goal; **replenishment
at or above attrition, in families not under concurrent development** is. At
5 families and ~2 lost per week, the current buffer is about two and a half
weeks — and only if the new families avoid areas lanes are building in.

They do not, entirely. Screening every held-out row's `source_name` against
`kernel-environment-snapshot-v1.json` (2,207 declarations; controls:
`Nat.add` present, `Bogus.zzz` absent):

| family | already-declared | partition |
| --- | --- | --- |
| natural-logarithm | 0/21 | held-out (v1) |
| natural-square-root | 0/16 | held-out (v1) |
| integer-division | 0/10 | held-out (v2) |
| **natural-divisibility** | **4/10** | held-out (v2) |
| natural-parity | 0/10 | held-out (v2) |

`Nat.dvd_add`, `Nat.dvd_add_iff_right`, `Nat.dvd_antisymm` and `Nat.dvd_mod_iff`
were preregistered blind **today**, against a snapshot that already contained
them and which the generator itself loads. That is the `natural-binomial`
signature (5 of 20) in a family six hours old. A name match is necessary and not
sufficient for "already proved" — the statements may differ — but for blindness
it is exactly the question. Hence R9.

The existing rows are **grandfathered**: moving a preregistered partition is an
ADR-0542 amendment with a recorded breach, never something a regeneration does.
The amendment is owed to whoever owns that repair.

### Whether the 40-row atom is the thing to change

It is, but in the opposite direction from the one proposed. A minimum-compliant
draw assigns `held-out, development, train, held-out` — **20 held-out, 10
development, 10 train, so 20 dispatchable rows.** Against a measured 60 mirror
closures per day, that is roughly **eight hours of queue**. The 80-row draw that
just happened yielded 50 dispatchable and was consumed in **under two hours**
for its first 39.

So 40 rows is not a coarse atom the ceiling cannot afford; it is about one
working session. Shrinking `PER_FAMILY` makes each preregistration event smaller
and more frequent, which is the wrong direction on every axis: more draws means
more preregistration events to compare results against, and each one still costs
a full generator run and a recorded decision.

### The variable yield of a draw

`scripts/check-autogenesis-already-proved.py` measures **0 of the 11** current
dispatchable rows as already-proved by name match, while the `natural-lcm`
family was **5 of 10** free before any work began. So N dispatchable rows buy
somewhere between N/2 and N units of real work, and the variance is per family
rather than per row. This argues for drawing **larger** — a draw sized to the
worst case is a draw that is usually too small — and for running the
already-proved screen at dispatch time so a lane knows which rows are free
before it starts, rather than at draw time where nothing can be done about it.
It is deliberately *not* a screen that rejects candidates: a mirror we can close
in an afternoon is a good row, not a wasted one.

## Alternatives

**Raise `EVALUATION_CEILING` to ≥334.** Rejected as the framing, not the number.
It treats a per-manifest bound as a cross-manifest one and then relaxes it,
leaving the misattribution in place and the two data-destroying blockers
untouched. A future lane would hit exactly the same wall one draw later.

**Allow a refill to extend an existing dispatchable-eligible family.** Rejected.
It buys dispatchable rows with **zero** held-out breadth, and held-out breadth is
the resource with the measured attrition. It also sidesteps R5 by construction,
which is a guard being routed around rather than reconsidered.

**Shrink `PER_FAMILY` below 10.** Rejected on the arithmetic above: the atom is
already about one working session against the observed consumption rate.

**Make the ceiling a pure review-cadence number (400, 450).** Rejected as
unjustifiable — the objection this ADR opens with. `EXTENSION_CEILING =
V1_EVALUATION_ENTRIES` is a *rule*: the unattested cohort may never outweigh the
attested one, which is ADR-0601's "imports are labeled scaffolding, never
headline" applied to the same distinction. It also points at the right exit. The
v2 cohort exists at a weaker grade only because re-attestation needed a built
Mathlib; `scripts/provision-lean-import-toolchain.sh` now does that in about five
minutes on this host. When the ceiling binds, re-attest.

**Make preregistration drift fatal during a draw as well as under `--check`.**
Rejected. One lane's edit to one settled fact would then block every future draw.
The drift is printed by name on stderr, the file is never written in either mode,
and `--check` remains fatal.

## Consequences

- **Easier**: a second draw is now possible and safe. Adding families to
  `FAMILY_MODULES` and re-running preserves every preregistered partition and
  every closed fact, which is what "additive extension" always claimed to mean.
- **Harder**: a held-out family must be genuinely novel to us. R9 will refuse
  candidate families drawn from areas lanes are actively building, which is the
  point, and it will make some Mathlib modules unusable for held-out.
- **Newly visible**: `gen-autogenesis-nursery-refill.py --check` is a meaningful
  reproduction gate now that it no longer proposes to revert the ledger. It is
  **deliberately not registered** in `check.sh` or the justfile yet, because it
  is red on arrival from the `F:ml430-nat-totient-eq-zero-3be161d6` drift, which
  is another lane's fact to repair. Registering it is owed once that is resolved.
- **Revisit when**: the quoted cohort reaches 214, or held-out drops below four
  families. The second is likelier and is the one to watch; the attrition figure
  in this ADR rests on two amendments and deserves re-measuring at four.

## Related

- ADR-0478 (nursery splits by dependency component) — the source of `100..300`.
- ADR-0542 (held-out partition breach repair) — the amendment-ledger discipline
  R8 and R9 exist to keep regeneration out of.
- ADR-0601 (three producers, one trust anchor) — "scaffolding, never headline",
  which is what the quoted-cohort ceiling encodes.
- ADR-0603 (graded statement families) — the grading vocabulary the v1/v2 split
  uses.
- [`docs/research/11-design-review/2026-08-29-the-mirror-population-is-consumed.md`](../11-design-review/2026-08-29-the-mirror-population-is-consumed.md)
