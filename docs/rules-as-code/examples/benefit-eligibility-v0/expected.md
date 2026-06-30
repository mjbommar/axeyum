# Expected Results

The machine-readable expectations live in [expected.json](expected.json). This
page renders the important witness and proof-gap information for review.

## Replayed Witnesses

| Witness | Expected | Why |
|---|---:|---|
| `standard_at_new_threshold` | eligible | Adult resident at income 35000 on 2026-07-01 meets the new standard threshold. |
| `standard_above_new_threshold` | ineligible | Income 35001 is one unit above the new standard threshold without override. |
| `veteran_override_at_cap` | eligible | Veteran override raises the new threshold to 45000. |
| `sanction_blocks_veteran` | ineligible | Sanctions dominate ordinary eligibility and the veteran override. |
| `temporal_before_change` | ineligible | Income 33000 exceeds the old threshold on 2026-06-30. |
| `temporal_after_change` | eligible | The same income is within the new threshold on 2026-07-01. |

Every row above is replayed by
[validate-rules-as-code.py](../../../../scripts/validate-rules-as-code.py).

## Proof Gaps

| Check | Expected | Current evidence |
|---|---|---|
| `consistency` | `unsat` | Source-linked Bool/QF_LIA fixture with checked Axeyum evidence. |
| `coverage` | `unsat` | Finite-sample replay only; needs Bool/QF_LIA Axeyum proof harness. |
| `threshold_cliff` | `sat` | Concrete witnesses replay. |
| `monotonicity` | `unsat` | Source-linked Bool/QF_LIA fixture with checked Axeyum evidence for the fixed no-exception obligation. |
| `temporal_transition` | `sat` | Concrete witnesses replay. |
| `implementation_equivalence` | `sat` | Validator implementation agrees with documented witnesses; solver equivalence query is future work. |
