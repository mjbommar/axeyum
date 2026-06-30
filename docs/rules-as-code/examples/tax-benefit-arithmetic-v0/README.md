# Tax Benefit Arithmetic V0

This rules-as-code pack models a tiny tax/benefit formula with integer
thresholds, a household-size adjustment, a cap, a phase-out rate, and an
effective-date threshold change.

It exists to reuse math-curriculum resource patterns:

- integer thresholds from `integer-lia-v0`;
- finite witness replay from `finite-predicate-v0` and `natural-arithmetic-v0`;
- monotonicity and cap obligations as small Bool/QF_LIA queries;
- implementation equivalence as a bounded mismatch query.

This pack is not a tax model and is not legal or financial advice. The source
rule is a toy human-authored rule set in [source.md](source.md).

## What Axeyum Checks

The model computes a benefit in integer units:

```text
phase_start = 40 before 2026-07-01, otherwise 45
base = 20 + 5 * (household_size - 1), for household_size in 1..3
raw = base - 2 * max(0, income - phase_start)
benefit = max(0, raw)
```

The checked rows are:

- `non_negative_benefit`: no valid input produces a negative benefit;
- `cap_respected`: no valid input produces a benefit above 30;
- `phaseout_monotonicity`: raising income cannot raise the benefit inside the
  active linear phase-out slice for a fixed household size and threshold;
- `implementation_equivalence`: the formal rule formula and bounded executable
  interpretation cannot disagree on the active linear phase-out slice.

The replayed witness rows are:

- `threshold_cliff`: income at and one unit above the new phase-out threshold;
- `temporal_transition`: the same facts before and after the effective-date
  threshold change.

## Trust Boundary

The formalization is not trusted. The source text, finite witness data, and
SMT-LIB obligations are human-authored inputs. Axeyum search is also untrusted.

Trusted work is intentionally small:

- witness replay recomputes the benefit from the source parameters;
- checked UNSAT rows parse the committed SMT-LIB artifacts, run Axeyum, emit
  certified evidence, and re-check that evidence against the original
  assertions;
- the validator also replays the complete piecewise formula over the finite
  sample, including the threshold and zero-floor branches.

## Files

- [source.md](source.md): toy source rule text and citations.
- [model.md](model.md): formalization and replay function.
- [checks.md](checks.md): check inventory and proof routes.
- [expected.json](expected.json): machine-readable witnesses and check metadata.
- [smt2/](smt2/): source-linked Bool/QF_LIA regression fixtures.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-rules-as-code.py
cargo test -p axeyum-solver --test rules_as_code_examples
```
