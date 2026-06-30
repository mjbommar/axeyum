# Expected Outcomes

The machine-readable source of truth is [expected.json](expected.json).

## Witness Rows

| Witness | Facts | Expected Benefit | Why |
|---|---|---:|---|
| `new_threshold_full_credit` | income 45, household size 3, date 2026-07-01 | 30 | At the new threshold, the capped household credit is unreduced. |
| `one_step_phaseout` | income 46, household size 3, date 2026-07-01 | 28 | One unit above threshold reduces the 30-unit credit by 2. |
| `zero_after_full_phaseout` | income 61, household size 3, date 2026-07-01 | 0 | The raw value is below zero, so the final benefit floors at 0. |
| `temporal_before_change` | income 43, household size 1, date 2026-06-30 | 14 | The old threshold is 40, so the benefit phases down by 6. |
| `temporal_after_change` | income 43, household size 1, date 2026-07-01 | 20 | The new threshold is 45, so the same income gets full base credit. |

## Checked Rows

| Check | Expected | Route |
|---|---|---|
| `non_negative_benefit` | `unsat` | Bool/QF_LIA checked evidence |
| `cap_respected` | `unsat` | Bool/QF_LIA checked evidence |
| `phaseout_monotonicity` | `unsat` | Bool/QF_LIA checked evidence for the active linear phase-out slice |
| `implementation_equivalence` | `unsat` | Bool/QF_LIA checked evidence for the active linear phase-out slice |

The checked route requires `produce_evidence` to emit certified evidence and
`Evidence::check` to re-check it against the parsed SMT-LIB assertions.
