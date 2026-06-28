# Model

## Inputs

| Name | Sort | Meaning |
|---|---|---|
| `age` | `Int` | Applicant age in years. |
| `income` | `Int` | Countable income in whole units. |
| `resident` | `Bool` | Whether the applicant satisfies residency. |
| `veteran` | `Bool` | Whether the veteran override applies. |
| `sanctioned` | `Bool` | Whether the disqualifying sanction applies. |
| `application_date` | `Date` | Date used only to choose the active threshold. |

## Derived Values

```text
standard_threshold(date) =
  if date < 2026-07-01 then 30000 else 35000

veteran_threshold(date) =
  standard_threshold(date) + 10000
```

## Eligibility Predicate

```text
eligible =
  resident
  and age >= 18
  and not sanctioned
  and (
    income <= standard_threshold(application_date)
    or (veteran and income <= veteran_threshold(application_date))
  )

ineligible = not eligible
```

## Axeyum Fragment

The intended solver encoding is Bool plus QF_LIA:

- Booleans encode residency, veteran status, sanctions, and rule outputs.
- Integers encode age, income, thresholds, and a bounded date/version choice.
- The first validator replays concrete witnesses directly; a future Axeyum
  harness should encode each check as a query and attach evidence to each
  `unsat` result.
