# Expected Results

The finite sample covers:

- bid amounts `99`, `100`, and `101`;
- quality scores `69`, `70`, `74`, and `75`;
- dates `2026-07-31`, `2026-08-01`, and `2026-08-02`;
- both values of `small_business` and `debarred`.

That gives 144 bounded fact patterns. The generated query artifact also emits
adjacent quality-score monotonicity rows for every fixed non-quality context.

## Witnesses

| Witness | Expected | Purpose |
|---|---|---|
| `ordinary_threshold_award` | `award = true` | Score 75 exactly meets the threshold. |
| `ordinary_bonus_cut_denied` | `award = false` | Score 70 without bonus misses the threshold. |
| `small_business_bonus_award` | `award = true` | Score 70 with bonus reaches 75. |
| `late_submission_denied` | `award = false` | A late bid is excluded. |
| `debarred_vendor_denied` | `award = false` | Debarment dominates price and score. |
| `bid_above_cap_denied` | `award = false` | Bid cap dominates score and bonus. |

## Check Status

| Check | Expected Result | Proof Status |
|---|---|---|
| `debarment_exclusion` | `unsat` | checked Bool/QF_LIA evidence |
| `late_submission_exclusion` | `unsat` | checked Bool/QF_LIA evidence |
| `bid_cap_respected` | `unsat` | checked Bool/QF_LIA evidence |
| `score_bonus_threshold` | `sat` | finite witness replay |
| `score_monotonicity` | `unsat` | checked Bool/QF_LIA evidence |
| `implementation_equivalence` | `unsat` | checked Bool/QF_LIA evidence |
