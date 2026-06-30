# Benefit Eligibility V0

This is the first Rules-as-Code Verification Lab pack. It is a toy eligibility
rule, not legal advice and not a natural-language parser benchmark.

The pack demonstrates the intended workflow:

1. cite a human-authored source rule;
2. write a small logical model;
3. name checks and expected outcomes;
4. replay concrete witnesses against an executable model;
5. mark proof gaps explicitly and wire in Axeyum evidence one check at a time.

## Files

- [metadata.json](metadata.json) — machine-readable rule-pack metadata.
- [source.md](source.md) — source rule text with citation anchors.
- [model.md](model.md) — formal model and executable interpretation.
- [checks.md](checks.md) — consistency, coverage, threshold, monotonicity, and
  equivalence checks.
- [expected.json](expected.json) — replayed witnesses and machine-readable
  expected check status.
- [expected.md](expected.md) — human-readable witness replay, checked rows, and
  remaining proof gaps.

## Validation

Run:

```sh
python3 scripts/validate-rules-as-code.py
```

The validator checks the metadata shape, source citation files, expected check
records, and every documented witness. It also exhaustively samples the listed
age/income/date/Boolean domain to validate consistency, coverage, and income
monotonicity for this toy pack.

The consistency and monotonicity rows now also have source-linked Bool/QF_LIA
fixtures under [smt2/](smt2/) and checked Axeyum evidence through:

```sh
cargo test -p axeyum-solver --test rules_as_code_examples
```
