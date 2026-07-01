# Grant Allocation V0

This example pack models a small grant-allocation rule with exact rational
shares. A conforming allocation divides one unit of funding among shelter,
clinic, and administration buckets while respecting minimum program shares and
an administrative cap.

The point is not grant-law interpretation. The point is to exercise the
rules/law pattern that was missing from the current packs: rational allocation
and LP-style caps checked with QF_LRA/Farkas evidence, plus deterministic finite
replay over a bounded rational sample.

## Audience

- Policy engineers who need exact-rational allocation examples.
- Compliance engineers checking cap and minimum-share obligations.
- Axeyum contributors testing QF_LRA/Farkas evidence on non-code policy shapes.

## Rule Summary

For the example policy:

- shelter, clinic, and administrative shares are nonnegative rational numbers;
- the shares must sum to exactly `1`;
- shelter must receive at least `1/2`;
- clinic must receive at least `1/4`;
- administration must receive at most `1/4`.

The bounded model samples shares from `0`, `1/4`, `1/2`, `3/4`, and `1`.

## Trust Boundary

- The source clauses in [source.md](source.md) are example policy text, not law.
- The finite witnesses in [expected.json](expected.json) replay against the
  executable rational model in `scripts/validate-rules-as-code.py`.
- Checked negative rows use source-linked QF_LRA SMT-LIB fixtures under
  [`smt2/`](smt2/) and the shared
  `cargo test -p axeyum-solver --test rules_as_code_examples` regression.
- The pack does not prove anything about real grant administration,
  budget law, or natural-language interpretation.

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
cargo test -p axeyum-solver --test rules_as_code_examples grant_allocation
```
