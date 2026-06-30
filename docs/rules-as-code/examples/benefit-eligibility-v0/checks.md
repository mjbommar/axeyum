# Checks

## Consistency

There should be no complete fact pattern where `eligible` and `ineligible` are
both true.

Expected result: `unsat`.

Current validation: source-linked Bool/QF_LIA fixture
[consistency-bool-qf-lia-conflict.smt2](smt2/consistency-bool-qf-lia-conflict.smt2)
checked by
`cargo test -p axeyum-solver --test rules_as_code_examples`.

Proof status: checked. Axeyum must produce certified evidence and re-check it
against the parsed rule obligation.

## Coverage

Every complete fact pattern should produce either eligible or ineligible.

Expected result: `unsat` for `not eligible and not ineligible`.

Current validation: source-linked Bool/QF_LIA fixture
[coverage-bool-qf-lia-conflict.smt2](smt2/coverage-bool-qf-lia-conflict.smt2)
checked by
`cargo test -p axeyum-solver --test rules_as_code_examples`, plus finite-sample
replay over the listed sample domain.

Proof status: checked. The fixture keeps the standard rules-as-code coverage
shape visible by asserting a complete fact pattern with neither output assigned.

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

Current validation: source-linked Bool/QF_LIA fixture
[monotonicity-bool-qf-lia-conflict.smt2](smt2/monotonicity-bool-qf-lia-conflict.smt2)
checked by
`cargo test -p axeyum-solver --test rules_as_code_examples`, plus finite-sample
replay over the listed sample domain.

Proof status: checked for the fixed no-exception monotonicity obligation.

## Temporal Transition

The same facts may change eligibility only when the effective date changes.

Expected result: `sat` witnesses:

- `temporal_before_change`
- `temporal_after_change`

Proof status: replayed witness, not an unsat proof.

## Implementation Equivalence

The executable interpretation and the logical model should agree on the
active-threshold rule slice.

Expected result: `unsat` for a mismatch between `model_eligible` and
`implementation_eligible`.

Current validation: source-linked Bool/QF_LIA fixture
[implementation-equivalence-bool-qf-lia-conflict.smt2](smt2/implementation-equivalence-bool-qf-lia-conflict.smt2)
checked by
`cargo test -p axeyum-solver --test rules_as_code_examples`, plus executable
replay for the documented witnesses in [expected.json](expected.json).

Proof status: checked for the active-threshold slice. Broader generated
equivalence queries over versioned/bounded domains remain future work.
