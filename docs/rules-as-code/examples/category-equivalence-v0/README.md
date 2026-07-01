# Category Equivalence V0

This example pack models a small policy rule where two human-facing applicant
categories are treated as the same category for a priority-review decision.

The point is not legal interpretation. The point is to exercise a rules/law
shape that the current packs did not cover: quotient-like category equivalence,
classification functions, and the QF_UF/Alethe proof route needed to explain
why equivalent categories cannot receive different priority-review results.

## Audience

- Policy engineers modeling normalized eligibility categories.
- Compliance engineers checking whether equivalent categories are treated
  uniformly.
- Axeyum contributors tracking the rules/law path from finite replay to
  QF_UF/Alethe evidence.

## Rule Summary

For the example policy:

- `resident` and `in_state` are equivalent local categories;
- `nonresident` is a separate nonlocal category;
- only local applicants in the `emergency_housing` program receive priority
  review;
- equivalent categories must not disagree on priority review for the same
  program.

The bounded model samples three categories and two programs.

## Trust Boundary

- The source clauses in [source.md](source.md) are example policy text, not law.
- The finite witnesses in [expected.json](expected.json) replay against the
  executable category-normalization model in
  `scripts/validate-rules-as-code.py`.
- The category-congruence and implementation-equivalence obligations are
  source-linked QF_UF/Alethe rows checked through the
  `rules_as_code_examples` regression harness with `Evidence::check`.
- The pack does not prove anything about real benefits, housing programs, or
  statutory classification.

## Files

- [metadata.json](metadata.json) records the pack boundary.
- [source.md](source.md) records the cited example clauses.
- [model.md](model.md) describes the formalization.
- [checks.md](checks.md) lists the verification obligations.
- [expected.md](expected.md) summarizes replay witnesses and proof status.
- [expected.json](expected.json) is the machine-readable expected-result file.

## Validation

```sh
python3 scripts/gen-rules-as-code-dashboard.py
python3 scripts/validate-rules-as-code.py
python3 scripts/query-rules-as-code.py packs --pack category_equivalence_v0 --require-any
cargo test -p axeyum-solver --test rules_as_code_examples category_equivalence
```
