# Source Clauses

These clauses are invented example policy text. They are intentionally small so
that every formalized obligation can cite a source sentence.

## Rule 4(a): Award Threshold

A conforming bid is awardable only when its adjusted quality score is at least
75.

## Rule 4(b): Bid Cap

A conforming bid is awardable only when the bid amount is at most 100 units.

## Rule 4(c): Debarment Exclusion

A debarred vendor is not awardable, regardless of price or quality score.

## Rule 4(d): Submission Deadline

A bid is timely only when the received date is on or before 2026-08-01. A late
bid is not awardable.

## Rule 4(e): Small-Business Bonus

For this example policy, a small-business vendor receives a 5-point scoring
bonus. The bonus is added to the quality score before applying the award
threshold.

## Rule 4(f): Implementation

An implementation of this rule computes:

```text
adjusted_score = quality_score + (small_business ? 5 : 0)
award = !debarred
        && received_date <= 2026-08-01
        && bid_amount <= 100
        && adjusted_score >= 75
```
