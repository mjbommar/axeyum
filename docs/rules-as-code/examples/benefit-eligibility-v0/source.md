# Source Rule

This source is deliberately synthetic. It is small enough to inspect and is
meant to exercise the rules-as-code workflow, not model a real benefits law.

## Rule 1(a): Age And Residency

An applicant satisfies the base demographic requirement when the applicant is a
resident and is at least 18 years old on the application date.

## Rule 1(b): Income Thresholds

For non-veteran applicants, the standard income threshold is 30000 before
2026-07-01 and 35000 on or after 2026-07-01.

## Rule 1(c): Sanctions

A sanctioned applicant is ineligible regardless of age, residency, income, or
veteran status.

## Rule 1(d): Veteran Override

A veteran applicant receives an income-threshold increase of 10000 for the
applicable date.

## Rule 1(e): Effective Date

The threshold change takes effect on 2026-07-01. Applications before that date
use the old threshold; applications on or after that date use the new threshold.
