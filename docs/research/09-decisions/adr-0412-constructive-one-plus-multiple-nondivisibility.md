# ADR-0412: Constructive one-plus-multiple nondivisibility

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.3 / R4.4 / R7.1.

## Context

The paper writes the sharpness witness factor as `u'=1+a*t` and concludes
`a does not divide u'`. The Nat library could introduce and add divisibility
witnesses, but could not cancel a known divisible summand or refute a divisor
of one. Treating the congruence sentence as an axiom would merely hide the
missing arithmetic.

## Decision

Add checked theorems

```text
dvd_add_right_cancel_of_pos    : 1<=a -> a|m -> a|(m+n) -> a|n
not_dvd_one_of_two_le          : 2<=a -> Not (a|1)
not_dvd_one_add_mul_of_two_le  : 2<=a -> Not (a|(1+a*t)).
```

For divisibility cancellation, expose both existential witnesses, reflect the
scaled quotient bound through positive `a`, use their truncated difference as
the new witness, and check restoration by additive cancellation. Refute `a|1`
by induction on its witness. Obtain the one-plus-multiple result by cancelling
the known `a*t` summand.

## Evidence

Positive controls recover `2|6` from `2|4` and `2|10`, infer `2 does not divide
1`, and infer `2 does not divide 1+2*3`. NC29--NC31 mutate respectively the
remaining summand, divisor, and multiplier; declaration checking rejects all
without insertion. The deterministic inventory now contains 59 theorems and
8 definitions, with zero axioms.

## Consequences

The paper's congruence argument can be specialized without introducing a
congruence or remainder axiom. Together with ADR-0411, this is sufficient to
prove that the closed-form witness `Z` has exactly two factors of `a`.
