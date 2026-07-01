# Procurement Scoring V0

This example pack models a small procurement award rule with price caps,
quality scores, a small-business bonus, debarment exclusion, and a submission
deadline.

The point is not procurement-law interpretation. The point is to show how a
human-authored rule model can reuse the same finite predicate, arithmetic
threshold, temporal deadline, monotonicity, and bounded implementation
equivalence shapes that already appear in the math-resource packs and earlier
rules-as-code examples.

## Audience

- Policy engineers who need deterministic rule-regression examples.
- Compliance engineers looking for source-cited counterexample rows.
- Axeyum contributors testing Bool/QF_LIA evidence on non-code policy shapes.

## Rule Summary

For the example policy:

- a debarred vendor is never awarded;
- a bid received after the deadline is never awarded;
- a bid above the maximum bid is never awarded;
- otherwise the adjusted score is the quality score plus a fixed
  small-business bonus, and the bid is awarded when the adjusted score reaches
  the threshold.

The bounded model uses integer dates encoded as `YYYYMMDD` in the solver
fixtures and ISO dates in the JSON pack.

## Trust Boundary

- The source clauses in [source.md](source.md) are example policy text, not law.
- The finite witnesses in [expected.json](expected.json) replay against the
  executable model in `scripts/validate-rules-as-code.py`.
- Checked negative rows use source-linked Bool/QF_LIA SMT-LIB fixtures under
  [`smt2/`](smt2/) and the shared
  `cargo test -p axeyum-solver --test rules_as_code_examples` regression.
- The pack does not prove anything about real procurements, real bid scoring,
  or natural-language interpretation.

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
cargo test -p axeyum-solver --test rules_as_code_examples procurement_scoring
```
