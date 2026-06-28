# Checks

## Consistency

There should be no complete fact pattern where `eligible` and `ineligible` are
both true.

Expected result: `unsat`.

Current validation: finite-sample replay in
[validate-rules-as-code.py](../../../../scripts/validate-rules-as-code.py).

Proof status: proof gap. The intended Axeyum encoding is a Bool/QF_LIA query
for `eligible and ineligible`.

## Coverage

Every complete fact pattern should produce either eligible or ineligible.

Expected result: `unsat` for `not eligible and not ineligible`.

Current validation: finite-sample replay.

Proof status: proof gap. This becomes trivial once `ineligible = not eligible`
is encoded, but the pack still records it because coverage is a standard
rules-as-code check.

## Threshold Cliff

Generate examples at and just above the active threshold.

Expected result: `sat` witnesses:

- `standard_at_new_threshold`
- `standard_above_new_threshold`

Proof status: replayed witness, not an unsat proof.

## Monotonicity

With all other facts fixed, increasing income should not turn an ineligible
applicant into an eligible applicant.

Expected result: `unsat` for the bad pattern:

```text
income2 >= income1
not eligible(income1)
eligible(income2)
```

Current validation: finite-sample replay over the listed sample domain.

Proof status: proof gap until encoded as a QF_LIA query.

## Temporal Transition

The same facts may change eligibility only when the effective date changes.

Expected result: `sat` witnesses:

- `temporal_before_change`
- `temporal_after_change`

Proof status: replayed witness, not an unsat proof.

## Implementation Equivalence

The executable replay function in the validator must agree with every expected
witness in [expected.json](expected.json).

Expected result: `sat` in the sense that every documented witness is accepted by
the implementation.

Proof status: replayed. A separate Axeyum-vs-implementation equivalence query is
future work.
