# Glaurung real-query proof holdout — 2026-07-19

Status: accepted fixed-policy correctness denominator with one retained
end-to-end coverage miss

ADR-0251 selected a disjoint 1,024-query holdout before proof completion or
timing was observed. ADR-0252 preserves the first zero-query corpus-membership
rejection, then fixes exact materialization without changing the selection or
execution policy.

- [`attempt-1-membership-rejection/`](attempt-1-membership-rejection/) records
  the pre-execution protocol failure. It contains no holdout result.
- [`accepted-fixed-policy/`](accepted-fixed-policy/) records the two corrected,
  clean-detached artifact-v34 repetitions and their fail-closed join.

The corrected result is correctness and deployability evidence, not solver
performance or full-corpus prevalence evidence.
