# Checks

## `debarment_exclusion`

Asks for a debarred vendor to receive an award. The source formula says
`award` includes `not debarred`, so the obligation is inconsistent.

Evidence: checked Bool/QF_LIA fixture
[`smt2/debarment-exclusion-bool-qf-lia-conflict.smt2`](smt2/debarment-exclusion-bool-qf-lia-conflict.smt2).

## `late_submission_exclusion`

Asks for a bid received after the deadline to receive an award. The fixture
encodes the dates as integers and links `on_time` to `received_date <=
deadline`, so the obligation is inconsistent.

Evidence: checked Bool/QF_LIA fixture
[`smt2/late-submission-exclusion-bool-qf-lia-conflict.smt2`](smt2/late-submission-exclusion-bool-qf-lia-conflict.smt2).

## `bid_cap_respected`

Asks for a bid above the 100-unit cap to receive an award. The fixture links
`within_bid_cap` to `bid_amount <= max_bid`, so the obligation is inconsistent.

Evidence: checked Bool/QF_LIA fixture
[`smt2/bid-cap-respected-bool-qf-lia-conflict.smt2`](smt2/bid-cap-respected-bool-qf-lia-conflict.smt2).

## `score_bonus_threshold`

Replays the threshold edge where a quality score of 70 is not awardable without
the small-business bonus but is awardable with the 5-point bonus.

Evidence: finite witness replay.

## `score_monotonicity`

For fixed exclusion, deadline, bid-cap, and bonus facts, asks for a higher
quality score to lose an award that a lower quality score received. Because the
award condition is `quality + bonus >= 75`, the bad monotonicity pattern is
inconsistent.

Evidence: checked Bool/QF_LIA fixture
[`smt2/score-monotonicity-bool-qf-lia-conflict.smt2`](smt2/score-monotonicity-bool-qf-lia-conflict.smt2).

## `implementation_equivalence`

Asks for a mismatch between the formal model and the executable interpretation
when both encode the same rule formula. The mismatch is inconsistent.

Evidence: checked Bool/QF_LIA fixture
[`smt2/implementation-equivalence-bool-qf-lia-conflict.smt2`](smt2/implementation-equivalence-bool-qf-lia-conflict.smt2).
