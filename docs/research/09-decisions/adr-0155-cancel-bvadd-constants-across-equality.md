# ADR-0155: Cancel additive bit-vector constants across equality

Status: accepted
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

## Decision

Add exact rule `bv.eq_add_constant_cancel.v1`.

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

## Accepted evidence

The v4 implementation passes manifest coverage, exhaustive evaluator
equivalence through width 3, scalar modular wrap, symbolic multiplicity,
129-bit constants, both equality orientations, deliberate non-matches,
formatting, and strict Clippy. The pinned 128-query capture provides the
required lifter-shaped differential route: the rule fires 1,094 times across 34
SAT and 34 UNSAT rows, all decisions agree with in-process Z3, and every SAT
model replays against the original assertions. The single semantic run measures
0.051248 seconds versus Z3's 0.149495 seconds (0.343x), with 5,159 post-word DAG
nodes, 86,123 new AIG nodes, and 94,043 clauses.

Five clean representative processes improve mean Axeyum total from 0.134733 to
0.051541 seconds (-61.7%) and mean ratio from 0.909x to 0.351x (-61.3%). Five
clean full processes then improve mean Axeyum total from 13.9462 to 5.6250
seconds (-59.7%) and mean ratio from 1.8286x to 0.7297x (-60.1%). Bit blast,
CNF, and SAT improve 70.5%, 69.9%, and 68.0%; the bounded word pass increases
2.9%. The rule fires 104,465 times in a full run. Output DAG nodes fall 45.4%,
AIG requests 63.1%, new AIG nodes 76.7%, and clauses 75.4%.

Every full process decides 13,462/13,462 queries with zero errors, unknowns,
disagreements, or replay failures. `register-slice` time improves 48.8% and
`slice-partial` 82.8%; both become faster than Z3. The fail-closed comparator
verifies that v4 is exactly v3 plus this rule and passes the 3% ratio, 3%
Axeyum-total, and 2% Z3-drift gates; observed Z3 drift is 1.07%. The candidate
summary SHA-256 is
`7d7700c23fb3c361e3719b4b5296a105d88bf7bc1d3ba6da4dacc588053a6d57`;
the guarded comparison SHA-256 is
`619079beb9871391138854a946a0ee43a678a6116626d0588b2201bc87cb940c`.
