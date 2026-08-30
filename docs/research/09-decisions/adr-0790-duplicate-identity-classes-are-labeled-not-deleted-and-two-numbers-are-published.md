# ADR-0790: Duplicate identity classes are labeled, not deleted, and two numbers are published

Status: accepted
Date: 2026-08-30
Index-summary: ADR-0771's 15 identity classes (theorem pairs sharing a byte-identical `Kernel::render_lean` canonical type) all survived hand verification as genuine same-proposition duplicates; each pair now carries a schema-level `equivalent_to` edge from one member to a canonical survivor -- no fact deleted or retracted -- and `scripts/check-proposition-duplication.py` gates new unlabeled pairs from entering. `validate-facts.py` and `bench-results/PARITY.md` now print DISTINCT PROPOSITIONS ESTABLISHED (2,106) beside FACTS SETTLED (2,121 proved) rather than quoting the larger number alone.
Index-status: accepted

Lane: `ledger-duplicate-propositions`.

## Context

[ADR-0771](adr-0771-trust-and-circularity-are-read-from-the-admitted-term-and-the-identity-map-is-derived.md)
(`scripts/check-trust-closure.py`, the L0/S2 gate) computed `identity_classes`
as a side effect of auditing trust closures: sets of THEOREM declarations
whose `Kernel::render_lean` canonical type is byte-identical. It measured

> **15 identity classes, all 15 with both members as ledger facts, and in 13
> of them one member's proof closure literally contains the other.**

That lane deliberately did not repair it -- a lane that reports an
overstatement does not also repair it, by this repository's own standing
rule. The published headline is **2,121 proved facts**. If 15 of those are
the same 15 propositions counted twice, the honest number is lower, and the
one metric this project treats as its output has been double-counting.

A type IS the proposition in this kernel's propositions-as-types setting, so
two theorems with byte-identical canonical types cannot denote different
Props -- this is close to the strongest test available for "these are the
same statement" short of reading a formal semantics by hand. It is also,
notably, blind to duplicates that are NOT byte-identical (a reordered
hypothesis, an unfolded `Monotone`, a differently-named bound variable that
the renderer does not normalize the same way) -- see Limitations below.

## What was verified

Every one of the 15 pairs was read by hand: `formal.statement`, `depends_on`,
and (via `artifacts/trust-closure/equivalent-pairs.tsv` where applicable) the
literal proof-closure containment, before any fact was touched.

**All 15 survived scrutiny as genuine duplicates.** None was a case of "A is
proved from B but states something strictly stronger" -- the task briefing
for this lane expected some fraction to be rejected on exactly that ground,
and none was; a byte-identical canonical type leaves no room for a strictly
stronger conclusion; it isn't a *test* for sameness, it's what sameness is
in a propositions-as-types kernel; the review this ADR describes is really
verifying that the identity-class computation and each fact's stated subject
line up correctly, not second-guessing an independent mathematical judgment.

Two of the 15 are not in S2's 13-item disclosed backlog because neither
member's proof literally reaches the other -- they were proved
**independently**, so each is still a fresh duplicate discovery rather than a
"one reused the other's proof" case:

- `CPoint.apollonius_from_stewart` / `CPoint.apollonius_median` -- the same
  Apollonius median-length identity, one proof routed through a specialized
  Stewart's theorem, the other through direct dot-product identities.
- `Int.add_mul` (an `ml430` Mathlib-parity mirror, `int_prelude/add_basics.rs`,
  2026-08-29) / `Rat.int_right_distrib` (internal `Rat`-prelude plumbing,
  2026-08-25) -- literally `(a+b)*c = a*c+b*c` over `Int`, declared twice
  under two names four days apart, from the same two dependencies
  (`Int.mul_comm`, `Int.left_distrib`).

The other 13 match S2's disclosed backlog exactly: an ml430 Mathlib-mirror
fact, a `Characterization`/`Peano` namespace restatement, or a capstone
theorem (`Rat.weak_law_of_large_numbers`) whose kernel proof directly invokes
a sibling already registered as its own fact
(`Rat.chebyshev_sampleMean_uncorrelated`).

## Decision

### Facts are never deleted or retracted

[ADR-0542](adr-0542-held-out-partition-breach-repair.md)
is binding, and several of the 15 are preregistered `ml430` mirror targets.
Both members of every pair keep `epistemic_status: proved`, their own
`evidence`, and their own `provenance`. Nothing about whether these are true
theorems changes -- only how they are COUNTED.

### One canonical survivor per pair, marked by the OTHER member

A new fact-schema field, `equivalent_to` (`artifacts/ontology/fact.schema.json`,
array, `minItems`/`maxItems` 1), records that a fact's `formal.statement` is a
byte-identical kernel proposition to the named fact. It is deliberately NOT
`supersedes` -- that field already means "this fact makes an older one
obsolete", and neither member of these pairs is obsolete; both proofs remain
independently checked and both stay in the ledger.

Canonical choice, applied uniformly: for the 13 disclosed pairs, the
canonical member is the one whose kernel theorem is REACHED IN the other's
proof closure (the dependency, not the wrapper). For the 2 independent pairs,
the canonical member is the one registered EARLIER by `provenance.date`
(`Rat.int_right_distrib`, 2026-08-25, predates the `Int.add_mul` mirror by
four days); the `CPoint` pair ties on date, so the direct-named
`apollonius_median` is canonical over the derivation-flagged
`apollonius_from_stewart`. The choice is a convention, not a mathematical
claim -- swapping which member of a pair is "canonical" changes nothing about
either count, only which fact ID a reader is pointed at.

All 15 non-canonical facts were edited to add `equivalent_to` in this commit;
no `statement` or `formal.statement` was touched, so
`scripts/check-settled-fact-statements.py`'s pinned-statement gate is
unaffected.

### Two numbers, always quoted together

- **FACTS SETTLED** = `proved` + `computed` facts, unchanged in meaning
  (2,121 proved + 2 computed = 2,123; the pre-existing headline "2,121
  proved" is this count restricted to `proved`).
- **DISTINCT PROPOSITIONS ESTABLISHED** = facts settled minus the count
  carrying a non-empty `equivalent_to` (each of the 15 pairs collapses to 1):
  2,123 − 15 = 2,108 overall, or 2,121 − 15 = **2,106** restricted to
  `proved` alone, matching the headline's own scope.

`scripts/validate-facts.py`'s summary now prints both counts on adjacent
lines. `bench-results/PARITY.md`'s headline line is updated the same way.
Quoting FACTS SETTLED without DISTINCT PROPOSITIONS ESTABLISHED is exactly
how the overstatement in the Context section happened, so no output in this
repository should do that going forward.

### The gate: `scripts/check-proposition-duplication.py`

Reuses `check-trust-closure.py`'s `parse_projection`/`identity_classes`/
`subject_of`/`collect_subjects` by import (that file is S2's; this one
builds alongside it, never edits it). Eight guards, each mutation-verified
to be killed by exactly one control in
`scripts/tests/test-proposition-duplication.sh`:

| guard | catches |
|---|---|
| `identity_classes_empty` | the identity-class computation produced NOTHING (fails even though "zero classes" superficially resembles "no duplicates" -- this project has known, standing duplicate pairs, so zero means the computation broke) |
| `identity_classes_below_floor` | a pinned floor (15, `artifacts/identity-classes/population.json`) dropping -- partial breakage a hard zero-check would miss |
| `unlabeled_duplicate_pair` | **the core case**: an identity class with 2+ settled facts and MORE THAN ONE canonical (unmarked) member -- a new duplicate pair entering the ledger |
| `no_canonical_designated` | an identity class with 2+ settled facts and NONE canonical (a dangling/cyclic `equivalent_to` graph) |
| `equivalent_to_target_absent` | `equivalent_to` names a fact id that does not exist |
| `equivalent_to_target_unsettled` | the named target is not itself `proved`/`computed` |
| `equivalent_to_chain` | the named target itself carries `equivalent_to` (A -> B -> C would break the "collapse each pair to 1" count) |
| `equivalent_to_different_proposition` | the fact's own resolved kernel subject and its target's do NOT share a canonical type -- independent of identity-class membership, since it reads `decls` directly, so a bogus `equivalent_to` slapped onto two unrelated facts is still caught |

Registered in both `justfile` (`just check-proposition-duplication`) and
`scripts/check.sh`.

## Consequences

- The headline "N proved facts" claim now has an honest companion number, and
  neither can be quoted alone without the other being one line away.
- A lane adding a new theorem whose canonical type collides with an existing
  one (a rename, a re-derivation, a second `ml430` mirror of an aliased
  Mathlib name) gets caught by `unlabeled_duplicate_pair` before merge,
  rather than accumulating silently until the next manual audit.
- `equivalent_to` is additive and optional; nothing that reads a fact without
  knowing about it breaks, and no existing evidence, checker, or status
  changes.

## Limitations -- what this still misses

**Byte-identical canonical type is a sufficient test for "same proposition"
but not a necessary one**, and this detector only catches the sufficient
direction. A duplicate that differs in any of the following is invisible to
`identity_classes` and therefore to this gate:

- A reordered hypothesis list that is logically equivalent but not
  syntactically identical (`A -> B -> C` vs `B -> A -> C`).
- Two theorems that are propositionally but not definitionally equal --
  e.g. one built with `Nat.add x 3` where the other builds `Nat.add 3 x`, or
  one exposed through an unfolded helper definition where the other calls it
  directly. `CReal.congr_of_uniformly_continuous`-style renderer differences
  (documented at length in this repository's own CLAUDE.md under "THERE IS NO
  SINGLE SPELLING") already show the renderer does not normalize everything a
  human would consider "the same shape."
- A duplicate across TWO DIFFERENT CARRIERS asserting an isomorphic fact
  (`Nat.le_total` and `Int.le_total` are deliberately NOT merged by this
  scheme, and should not be -- ADR-0716's carrier asymmetry is load-bearing
  elsewhere in this repository's own test suite).
- A duplicate where one side is a NON-theorem kind (`identity_classes` scans
  `Declaration::Theorem` only, matching ADR-0771's own scope note that
  `AxReal.add`/`AxReal.mul` share a rendered type without being equivalent
  statements -- but this also means a `Definition`-kind duplicate, if one
  ever existed, would not be found here).

So a clean run of this gate means "no NEW byte-identical-type duplicate
pair went unlabeled" -- it is not a claim that 2,106 is the true ceiling on
how much the ledger still double-counts by looser notions of "the same
proposition."

## Alternatives considered

- **Retract one member of each pair, pointing at the survivor.** Rejected:
  ADR-0542 forbids deleting or retracting a preregistered population member,
  and several of the 15 are `ml430` mirror facts. Retraction would also
  destroy the (small) independent value of an independently-proved duplicate
  as a second, unrelated derivation of the same theorem.
- **Count facts and propositions as fully separate ledgers.** Rejected as
  more machinery than the problem needs: a single additive field on the
  existing fact object, checked by one gate, gives both numbers from the same
  source of truth with no risk of the two ledgers drifting apart.
- **Normalize `formal.statement` further (alpha-equivalence up to hypothesis
  reordering, defeq-aware comparison) before computing identity classes.**
  Left for future work; it would close some of the Limitations above but adds
  real complexity (a defeq check needs the live kernel, not a rendered
  string) disproportionate to what 2 more lanes of manual audit already
  bought.

## Verification

- `python3 scripts/validate-facts.py` -- 2,273 facts, 0 errors, unchanged.
- `python3 scripts/check-settled-fact-statements.py` -- PASS, 0 drifted, 0
  amendments (no `statement`/`formal.statement` touched).
- `python3 scripts/check-proposition-duplication.py` -- before labeling:
  `failures=15`, one `UNLABELED-DUPLICATE-PAIR` per class named above; after:
  `identity_classes=15|duplicate_classes=15|settled_facts=2123|
  equivalent_facts=15|distinct_propositions=2108|failures=0`.
- `bash scripts/tests/test-proposition-duplication.sh` -- 8 guards, each
  killed by exactly one mutation.
- `python3 scripts/check-autogenesis-holdout-isolation.py` -- unaffected
  before and after (none of the 15 pairs touches
  `artifacts/autogenesis/nursery-v1.json`).

## What this lane did NOT do

- Did not edit `scripts/check-trust-closure.py` (S2's file).
- Did not flip any fact's `epistemic_status`.
- Did not touch any held-out nursery row.
- Did not attempt the Limitations above (looser-than-byte-identical
  duplicate detection); that is future work, not silently claimed here.
