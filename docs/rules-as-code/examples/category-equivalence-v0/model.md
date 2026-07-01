# Formal Model

## Inputs

| Name | Sort | Meaning |
|---|---|---|
| `applicant_category` | `Enum(resident,in_state,nonresident)` | Human-facing category on the application. |
| `program` | `Enum(emergency_housing,standard_benefit)` | Program being reviewed. |

## Output

| Name | Sort | Meaning |
|---|---|---|
| `priority_review` | `Bool` | Whether the example policy grants priority review. |

## Parameters

| Name | Value |
|---|---|
| `equivalent_categories` | `resident == in_state` |
| `priority_program` | `emergency_housing` |

## Definition

```text
canonical(resident) = local
canonical(in_state) = local
canonical(nonresident) = nonlocal

priority_review(category, program) =
  canonical(category) == local
  and program == emergency_housing
```

The validator replays this definition over the finite category/program domain
in [expected.json](expected.json).

## Relationship To Math Resources

This pack reuses current math-resource proof shapes:

- finite replay over a bounded category/program table;
- equivalence-class and finite-function concepts for category normalization;
- checked QF_UF/Alethe evidence for congruence conflicts where equivalent
  categories are assigned different priority-status results.

The QF_UF/Alethe rows use a small `PriorityStatus` result sort in the SMT-LIB
artifacts so the source-level Bool decision is represented as an equality
conflict that the pure EUF proof emitter can certify.
