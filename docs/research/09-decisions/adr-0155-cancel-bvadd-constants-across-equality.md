# ADR-0155: Cancel additive bit-vector constants across equality

Status: proposed
Date: 2026-07-14

## Context

The clean artifact-v28 full profile at revision `37ebcd47` decides and replays
all 13,462 Glaurung queries and measures Axeyum/Z3 at 1.842x. The remaining
absolute excess is split between `register-slice` (3.44 seconds, 1.58x) and
`slice-partial` (3.14 seconds, 2.97x). In `slice-partial`, post-word `bvadd`
count has 0.988 Pearson correlation with bit-blast-plus-CNF time. Its 1,584
queries retain 44,668 additions and create 13.48 million AIG nodes plus 14.81
million clauses.

Inspection of the highest-excess rows identifies a repeated exact shape after
ADR-0153: an associative modular sum has one constant leaf and one or more
symbolic leaves, and equality compares that sum with a constant. Source rows
vary both constants together, for example `symbolic_sum + c = k`. ADR-0153
combines constants *within* the sum but correctly leaves its final constant
adder. Because BV addition is a finite abelian group, the equality is exactly
equivalent to `symbolic_sum = k - c (mod 2^width)`. Removing the constant leaf
also makes offset variants of the same predicate hash-cons to one term.

This is a narrower hypothesis than subtraction normalization, general affine
normalization, equality solving, or AIG adder redesign. It is selected from the
post-v3 DAG rather than lexical source frequency.

## Proposed decision

Add exact rule `bv.eq_add_constant_cancel.v1`, subject to the Glaurung
acceptance gate.

- Match an equality over same-width bit-vectors where one operand is a constant
  `k` and the other is a flattened `bvadd` with at least one nonconstant leaf
  and at least one constant leaf.
- Sum any constant leaves modulo `2^width`, remove them, deterministically
  rebuild the remaining symbolic sum, and replace the constant side with
  `k - sum (mod 2^width)`.
- Handle either equality orientation and both scalar and arbitrary-width
  constants. Preserve symbolic multiplicity and use the existing sorted,
  balanced AC rebuild.
- Record only this transformation under the stable rule ID above. It is exact
  denotation preservation with identity model projection; original-query model
  replay remains mandatory.
- Keep work linear in the already bounded reachable add chain and introduce at
  most one adjusted constant plus the existing balanced symbolic tree.
- Advance the default rewrite identity from v3 to v4. The guarded comparator
  must verify that v4 is exactly v3 plus this one rule.

Before corpus timing, require manifest coverage, exhaustive small-width
evaluation, modular-wrap and 129-bit fixtures, both equality orientations,
non-match fixtures, lifter-shaped Z3 SAT/UNSAT differential replay, formatting,
and strict Clippy under 4 GiB. Run five representative processes only after
those gates pass. Continue to five full processes only if the rule fires in the
target families, reduces post-word/AIG/CNF structure, preserves 100% decisions
and replay, and improves representative end-to-end timing beyond noise. Accept
only if the guarded full comparison passes the existing 3% ratio / 3% Axeyum /
2% absolute-Z3 alarms and materially improves at least one excess-owning
family. Otherwise restore v3 and defer this ADR.

## Alternatives

- **Normalize all `bvsub` into addition/negation.** Deferred: `slice-partial`
  retains only 209 subtractions versus 44,668 additions, and this would expand a
  non-commutative operator before the exact equality opportunity is tested.
- **Rewrite BV1 ITE/equality Booleanization first.** Deferred: it removes small
  one-bit wrappers but not the repeated 64-bit constant adders that dominate
  the selected rows.
- **General affine normalization across both equality operands.** Deferred: it
  needs coefficient collection, growth control, and a larger proof/test surface.
- **Optimize ripple adders in the AIG lowerer.** Deferred: eliminating a
  redundant adder at the word level avoids constructing it and can expose
  sharing across whole assertions.

## Consequences

If accepted, this becomes the third exact GQ2/GQ3 production tranche and must
be re-attributed on the real capture. It does not authorize cancellation across
ordered comparisons, arithmetic overflow predicates, or any non-equality
context. GQ7 ordered-trace handoff remains the parallel functionality priority.
