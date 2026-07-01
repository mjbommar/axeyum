# Formal Model

## Inputs

| Name | Sort | Meaning |
|---|---|---|
| `shelter_share` | `Real` | Funding share assigned to shelter services. |
| `clinic_share` | `Real` | Funding share assigned to clinic services. |
| `admin_share` | `Real` | Funding share assigned to administration. |

## Output

| Name | Sort | Meaning |
|---|---|---|
| `compliant` | `Bool` | Whether the example policy accepts the allocation. |

## Parameters

| Name | Value |
|---|---:|
| `total_share` | `1` |
| `shelter_minimum` | `1/2` |
| `clinic_minimum` | `1/4` |
| `admin_cap` | `1/4` |

## Definition

```text
balanced = shelter_share + clinic_share + admin_share == total_share
compliant =
  balanced
  and shelter_share >= shelter_minimum
  and clinic_share >= clinic_minimum
  and admin_share <= admin_cap
  and shelter_share >= 0
  and clinic_share >= 0
  and admin_share >= 0
```

The validator replays this definition over the finite rational sample domain in
[expected.json](expected.json). The checked SMT-LIB fixtures use small
source-linked QF_LRA obligations rather than the full generated finite domain.

## Relationship To Math Resources

This pack reuses the current math-resource proof shapes:

- finite rational replay over a bounded allocation table;
- QF_LRA/Farkas evidence for exact-linear budget balance, floors, and caps;
- bounded implementation equivalence by asking for a mismatch between two
  identical formalizations.
