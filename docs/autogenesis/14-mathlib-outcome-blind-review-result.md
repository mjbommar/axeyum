# Mathlib outcome-blind review result

Date: 2026-08-18

## Verdict

**The candidate source is now reviewed and mutation-grouped, but still is not
a frozen evaluation nursery.** No Mathlib proof value, tactic trace, Axeyum
route, proof plan, budget, or outcome informed the decisions.

The tracked [review policy](../../artifacts/autogenesis/mathlib-nursery-review-policy-v1.json)
and [derived review artifact](../../artifacts/autogenesis/mathlib-nat-int-reviewed-nursery-v1.json)
produce this census:

| Disposition | Count |
|---|---:|
| evaluation-eligible source candidates | 202 |
| calibration-only statements | 23 |
| excluded aliases | 5 |
| excluded internal/elaborator surfaces | 10 |
| outcome-blind statement mutations | 12 |
| future evaluation statements | 214 |
| indivisible dependency/mutation groups | 120 |

This remains inside the preregistered 100--300 statement envelope. The 23
calibrations are not counted as future evaluation yield.

## Review decisions

The alias removals cover exact duplicate statements and reflexivity aliases
whose only material difference is presentation. The internal-surface removals
cover `gcdA`/`gcdB`/`xgcdAux`, the square-root iterator invariant, and the
`autoParam`-bearing bitwise helper. They can remain upstream implementation
tests without becoming claims about general mathematical self-extension.

Closed Fibonacci, factorial, square-root, and logarithm base cases plus
implementation-equivalence theorems are retained as calibration-only. They are
useful for diagnosing import, evaluation, and definitional-equality seams, but
success on them must not inflate autonomous evaluation yield.

Everything else is retained by default. This default is explicit: statement
review is not allowed to optimize the population after seeing what Axeyum can
or cannot solve.

## Mutation controls

One source in every family receives one authored statement-strength mutation.
The twelve classes include premise removal, polarity reversal, boundary
widening or substitution, operator substitution, and relation/bound
strengthening. The artifact records no expected truth value, proof, witness, or
Axeyum result.

Every mutation inherits its source's original dependency component. Review
never recomputes components after deleting an alias or internal bridge, because
that would let editorial removal erase a known leakage edge. A future split
must assign the entire surviving component and all of its mutations together.

## Controls

The generator requires disjoint review dispositions, exact candidate and
component identities, exactly one mutation per family, eligible mutation
sources, changed nonempty statements, stable content-addressed mutation IDs,
and deterministic whole-group membership. Tests reject unknown or multiply
classified candidates, mutations attached to excluded sources, missing family
coverage, outcome access, and even a rehashed mutation of the derived result.

## Remaining boundary

The state is deliberately `reviewed-groups-not-frozen-split`. Before partition
freeze, the programme still needs statement-derived proof-shape risk labels and
a conversion from pretty-printed Mathlib statements to reviewed Axeyum
fact-ledger formal statements. Split assignment must then satisfy whole-group,
family, proof-shape, mutation, and longitudinal controls without consulting
episode outcomes. Only after those checks pass can the ordinary nursery
readiness state change.
