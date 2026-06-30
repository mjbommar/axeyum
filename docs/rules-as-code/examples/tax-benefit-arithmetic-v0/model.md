# Model

## Inputs

The model uses a small bounded domain:

- `income`: nonnegative integer income unit;
- `household_size`: integer in `1..3`;
- `application_date`: either before or on/after `2026-07-01`.

## Parameters

```text
change_date = 2026-07-01
phase_start_before = 40
phase_start_after = 45
base_credit = 20
household_adjustment = 5
credit_cap = 30
max_household_size = 3
phaseout_rate = 2
```

## Replay Function

For a fact row:

```text
phase_start(date) =
  40, when date < 2026-07-01
  45, otherwise

base(household_size) =
  20 + 5 * (household_size - 1)

raw(income, household_size, date) =
  base(household_size) - 2 * max(0, income - phase_start(date))

benefit = max(0, raw)
```

Because household size is bounded to `1..3`, `base` is at most 30. The cap row
is still checked explicitly so future rule changes cannot silently exceed it.

## SMT Shape

The checked fixtures encode the same piecewise-linear function using linear
integer arithmetic plus Boolean implications:

```smt2
(assert (=> (<= income phase_start) (= benefit base)))
(assert (=> (and (> income phase_start) (>= raw 0)) (= benefit raw)))
(assert (=> (and (> income phase_start) (< raw 0)) (= benefit 0)))
```

No multiplication of two symbolic terms is used. Constants multiply integer
terms only, so the route stays in Bool/QF_LIA.

## Horizon

This pack does not model a real tax code, calendar system, filing status,
refundability, rounding law, administrative discretion, or statutory
interpretation. Those would require richer source modeling and, for unbounded
schemas, separate theorem or proof-assistant artifacts.
