# ADR-0692: the dominance test has two axes, not a vote — and IVT still passes it

Status: accepted
Date: 2026-08-30
Index-summary: An adversarial audit charged that
`08-ivt-and-evt-measured-against-mathlib.md` grades IVT and EVT on
inconsistent criteria — three Mathlib-wins are excused for IVT's "Net" verdict
and one sinks EVT's. The charge is correct about the document's presentation:
no test was written down before it was applied, and the "Net" lines read as an
unweighted vote over an ad hoc axis list. It does not follow that IVT is
merely "mutually non-dominated," which is the audit's proposed fix.
`07-the-cost-model-and-pareto-position.md` already states the actual test —
trusted base and computational content, on a statement we ship, with breadth
EXPLICITLY conceded rather than counted — and that test was simply never
carried into the axis tables. Applied uniformly: IVT dominates on both claimed
axes for `ivt_approx`; EVT has no statement yet on which the comparison can
even be run, which is not a loss, it is inapplicability, and matches what
ADR-0675 and ADR-0691 already concluded by other means.
Index-status: accepted

- **Lane:** `ivt-claim-correction`
- **Corrects:** the axis tables and "Net" verdicts in
  [`08-ivt-and-evt-measured-against-mathlib.md`](../../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md)
  §4, and the unscoped public claim "IVT is Pareto-dominant over Mathlib"
  drawn from it.
- **Responds to:**
  [`2026-08-30-session-audit.md`](../11-design-review/2026-08-30-session-audit.md)
  §Part 1 item 3, which found the document's own axis table inconsistent.
- **Does not touch:** ADR-0675 or ADR-0691's decisions, which this ADR finds
  correct on independent re-derivation (see "What survives unchanged" below).
  **Reclassifies nothing.** No fact, `epistemic_status`, or proof was edited.

## The charge, restated precisely

`08-…`'s own §4 IVT table records three axes where it says "Mathlib
dominates": the exact conclusion (labeled "real and permanent"), generality of
statement (labeled "reachable"), and generality of structure (labeled "report
it as a loss, not as 'not meaningful'"). The document's own "Net for IVT" line
then reads: *"the Pareto claim holds."* Its EVT table records one comparable
axis — "Any positive EVT statement: Mathlib dominates outright" — and the
"Net for EVT" line reads: *"the Pareto claim does not hold."* Nowhere between
the two tables is there a stated rule for why three Mathlib-wins are
compatible with "holds" and one is not. A reader — including the one this was
reported to — has no way to apply the same test themselves, which is exactly
the defect `07-…` names for the un-scoped claim in the first place.

## Adjudication

**The charge holds as a presentation defect. It does not hold as a verdict
defect**, because the test `07-…` actually states is narrower than the
seven-axis table `08-…` built, and applying THAT test resolves the asymmetry
without needing a new axis-counting rule.

`07-the-cost-model-and-pareto-position.md` §1 states the claim in two
sentences that between them define exactly two axes and explicitly exclude a
third:

> "**On every statement we ship, strictly dominate**: constructive ⟹
> classical plus a program; trusted base 0 vs 3 axioms; every theorem
> executable where Mathlib's analysis is `noncomputable`."
>
> "**Concede breadth EXPLICITLY** at current efficiency, and treat it as a
> curve to bend, not a wall … labeled imports cover the gap meanwhile,
> excluded from every headline count as a stated invariant."

So the dominance claim is over exactly two axes — **trusted base** (axiom
footprint) and **computational content** (constructive-with-a-program vs
classical-existence) — evaluated on a statement we actually ship that is
comparable in content to Mathlib's. Breadth (how general the statement is: its
target, its orientation, the ambient structure it quantifies over) is a
**separate, explicitly conceded axis**, reported for honesty and never counted
toward or against the dominance verdict. `08-…`'s seven-axis table built a
much larger comparison — a genuinely useful one — and then answered the
narrower dominance question by an unweighted head-count over all seven, which
is not the test `07-…` states and is not any test written down anywhere.

Re-reading `08-…`'s own IVT rows against the two-axis test:

- **Trusted base**: `ivt_approx` and the whole IVT family read
  `axiom_footprint = 0` from the kernel; Mathlib's IVT sits on
  `Classical.choice`/`propext`/`Quot.sound` via `IsPreconnected`. We dominate.
- **Computational content**: the bisection route (`ivt_bisect_hi`/`_lo`,
  `ivt_bisect_approx`) is a definition the kernel reduces — a real algorithm —
  where Mathlib's proof is a one-line corollary of connectedness that extracts
  nothing executable. We dominate.

The "exact conclusion" row the document lists as a third, independent
Mathlib-win is not a third axis at all — it is **the same trade as
computational content, read from the other side.** Mathlib gets an exact
root because it assumes classical choice and proves nothing computable about
it; we get an approximate root because we refuse that assumption and the
approximation is exactly the price of the program. `07-…`'s own phrase
"constructive ⟹ classical **plus a program**" already prices this in as one
trade, not two. Listing "we dominate on computational content" as a win and
"Mathlib dominates on exactness" as a separate loss double-counts one fact.
This document's §4 table did that, and it is the specific thing being fixed.

"Generality of statement" (fixed target `0`, one orientation) and "generality
of structure" (`CReal → CReal` vs an arbitrary order) are genuinely separate
from both axes above, and they are exactly the breadth `07-…` says to concede
explicitly. They are reported, honestly, as scope limits — one cheap and
reachable, one real and not reachable inside this kernel's type system — and
neither counts toward or against the dominance verdict, because the verdict
was never a claim about them.

**Applied this way, IVT's dominance claim holds cleanly, with no excusing of
losses required**, because there are no losses on the two axes the claim is
actually about. The audit's "mutually non-dominated" fix is a defensible
answer to a *seven-axis unweighted-vote* question, but that is not the
question `07-…` asks, and adopting it would replace one unstated test with
another.

### EVT, under the same two-axis test

For EVT the question is not "does it lose on the two axes" — it is whether a
comparison can be RUN at all. Mathlib's comparable content is
`IsCompact.exists_isMaxOn`: a positive, attained maximiser. Our repertoire
consists of `CReal.evt_attained_max_decides_sign` (an impossibility result:
attainment on one linear family would decide an absent sign principle) plus,
as of ADR-0691, `CReal.supOn` (a value, with a convergence law, and
*no characterizing law yet* — confirmed below). Neither is comparable content
to a positive attained maximum; the boundary result is a different kind of
statement (what the constructive fragment CANNOT reach), not a weaker version
of what Mathlib proves.

So there is no row on which "trusted base" or "computational content" can be
measured against Mathlib's EVT, because there is nothing on our side that
plays the same role Mathlib's theorem plays. This is not a loss on either
claimed axis — it is the absence of a comparison, which is a different verdict
than "loses." **EVT is not currently eligible to be cited as a per-statement
dominance example**, which is exactly ADR-0675's and ADR-0691's conclusion,
reached here independently from the axis test rather than from row-counting.

### Re-derivation against the current kernel (post-`CReal.supOn`)

Built fresh in this lane's own worktree (stale binaries report false
negatives), `kernel_declaration_projection` on `HEAD`:

```
CReal.supOn                    -> found  creal/complex/cpoint  definition  axioms=0
CReal.evt_approx_max           -> ABSENT (no declaration of that name)
CReal.supOn_upper_bound        -> ABSENT (no declaration of that name)
CReal.ivt_exact_root_decides_sign -> found  creal  theorem  axioms=0
CReal.le_total                 -> ABSENT   (positive control: CReal.lt_cotrans -> found)
```

This matches ADR-0691 exactly: `supOn` landed as a value with a convergence
law; the upper-bound law and the approximate-least-upper-bound law — the two
declarations that would make it *characterized as a supremum*, and therefore
the thing an `evt_approx_max` row 1 could be built from — are still absent.
EVT's ineligibility for the dominance claim is therefore current, not stale.

## Mathlib re-verification

Three quotes `08-…` and the audit both attribute to Mathlib at
`c5ea00351c28e24afc9f0f84379aa41082b1188f` were re-read directly from
`/data0/axeyum/lean-import-toolchain/mathlib4` (already provisioned at the
pinned commit; `git log -1` confirms it) rather than trusted from either
document:

- `Mathlib/Topology/Order/IntermediateValue.lean:552`,
  `theorem intermediate_value_Icc` — verbatim, including the
  `[ConditionallyCompleteLinearOrder α] [OrderTopology α] [DenselyOrdered α]`
  variable stack it inherits from lines 232/361.
- `Mathlib/Topology/Order/Compact.lean:246`,
  `theorem IsCompact.exists_isMaxOn` — verbatim, including the
  `[LinearOrder α] [TopologicalSpace α]` variable block at line 143.
- `Mathlib/Order/Filter/Extr.lean:113`, `def IsMaxOn` — verbatim.

All three match both documents exactly. **Not refuted.**

## Decision

1. **State the two-axis test explicitly in `08-…`, before either axis table,
   quoting `07-…` §1 rather than paraphrasing it.** Trusted base and
   computational content are the dominance axes; generality/structure/exactness
   are conceded breadth, reported but never scored.
2. **Collapse the "exact conclusion" row into the computational-content row**
   in both axis tables — it is the same trade, not a second axis — and
   relabel the remaining breadth rows as "conceded, not scored" rather than
   leaving them ambiguously mixed into a dominance table.
3. **Rewrite both "Net" lines to name the axes explicitly** rather than saying
   "the Pareto claim holds/does not hold" unqualified:
   - IVT: *"Dominates on trusted base and computational content for
     `ivt_approx`, the statement shipped; breadth (target generality,
     ambient structure) is explicitly conceded, not scored."*
   - EVT: *"No statement exists yet on which the comparison can be run;
     `evt_attained_max_decides_sign` is a boundary result, not a weaker
     positive statement, and `supOn` (ADR-0691) is a value without the
     characterizing laws that would make it comparable. Not eligible to be
     cited as a dominance example."*
4. **Do not adopt "mutually non-dominated" for IVT.** It answers a
   seven-axis unweighted vote that `07-…` never proposes, and stating the
   narrower, already-written test resolves the inconsistency without it.

## What survives unchanged

- ADR-0675's decision — cite IVT, not EVT — is correct and is now reached by
  two independent routes (row-inventory, and the two-axis test here).
- ADR-0691's decision — land `supOn`, do not yet claim EVT dominance — is
  correct and this ADR's kernel re-check confirms its stated remaining gap
  (`supOn_upper_bound`-shaped and `evt_approx_max`-shaped declarations both
  absent) is still accurate post-merge.
- Row 2's `evidence.kind = "exhaustive-enumeration"` overstatement (an
  absence check against four hand-written names, not a derivability proof) is
  unchanged by this ADR and remains open per `08-…` §5 item 4.

## Alternatives rejected

- **Adopt the audit's "mutually non-dominated" verdict for IVT wholesale.**
  Rejected: it treats every axis in an ad hoc table as equally load-bearing
  for "dominance," which is not the claim `07-…` makes and would require
  inventing a new, still-unstated weighting rule rather than using the one
  that already exists.
- **Weaken EVT's verdict to match IVT's leniency, on the theory that both
  should get the same benefit of the doubt.** Rejected per this lane's brief:
  the direction of travel is the stricter, explicit test, and EVT's gap
  (no comparable statement exists) is not the same shape as IVT's conceded
  breadth (a statement exists and is narrower). Collapsing that distinction
  would hide the one row this repository most needs to keep visible —
  `CReal.evt_approx_max` is genuinely not built yet.
- **Leave the two-axis test implicit and only reword the "Net" lines.**
  Rejected: the audit's core finding is that no test was written down for a
  reader to apply themselves; rewording the conclusion without stating the
  rule that produced it repeats the defect in smaller font.

## Cost

Documentation only. No fact, gate, or proof term changed.
`prelude_theorem_inventory` and `kernel_declaration_projection` were rebuilt
fresh in this lane's worktree (~62 s combined) rather than trusted stale.
