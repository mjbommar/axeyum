# Formal Model

## Inputs

| Name | Sort | Meaning |
|---|---|---|
| `bid_amount` | `Int` | Bid amount in example units. |
| `quality_score` | `Int` | Base technical score. |
| `small_business` | `Bool` | Whether the bonus applies. |
| `debarred` | `Bool` | Whether the exclusion applies. |
| `received_date` | `Date` | ISO date in JSON, encoded as `YYYYMMDD` in SMT-LIB fixtures. |

## Output

| Name | Sort | Meaning |
|---|---|---|
| `award` | `Bool` | Whether the example policy awards the bid. |

## Parameters

| Name | Value |
|---|---:|
| `deadline` | `2026-08-01` |
| `max_bid` | `100` |
| `award_threshold` | `75` |
| `small_business_bonus` | `5` |
| `min_quality_score` | `0` |
| `max_quality_score` | `100` |

## Definition

```text
adjusted_score = quality_score + (if small_business then 5 else 0)
award =
  not debarred
  and received_date <= deadline
  and bid_amount <= max_bid
  and adjusted_score >= award_threshold
```

The validator replays this definition over the finite sample domain in
[expected.json](expected.json). The checked SMT-LIB fixtures use small
source-linked obligations rather than the full generated finite domain.

## Relationship To Math Resources

This pack reuses the current math-resource proof shapes:

- finite predicate replay for `debarred`, `small_business`, and the `award`
  output;
- QF_LIA threshold arithmetic for bid caps, score thresholds, and encoded
  dates;
- monotonicity over quality score;
- bounded implementation equivalence by asking for a mismatch between two
  identical formalizations.
