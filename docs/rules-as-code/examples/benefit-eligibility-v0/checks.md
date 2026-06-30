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

The executable replay function in the validator must agree with every expected
witness in [expected.json](expected.json).

Expected result: `sat` in the sense that every documented witness is accepted by
the implementation.

Proof status: replayed. A separate Axeyum-vs-implementation equivalence query is
future work.
