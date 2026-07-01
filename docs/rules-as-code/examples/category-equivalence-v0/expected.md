# Expected Results

The finite sample covers the applicant categories:

- `resident`;
- `in_state`;
- `nonresident`.

and the programs:

- `emergency_housing`;
- `standard_benefit`.

That gives six bounded category/program rows. The generated query artifact also
emits the two equivalence-pair rows comparing `resident` and `in_state` across
both programs.

## Witnesses

| Witness | Expected | Purpose |
|---|---|---|
| `resident_housing_priority` | `priority_review = true` | Resident applicant receives emergency-housing priority. |
| `in_state_housing_priority` | `priority_review = true` | Equivalent in-state applicant receives the same emergency-housing priority. |
| `nonresident_housing_denied` | `priority_review = false` | Nonresident applicant is not local. |
| `resident_standard_denied` | `priority_review = false` | Local category alone is not enough outside the priority program. |

## Check Status

| Check | Expected Result | Proof Status |
|---|---|---|
| `category_witnesses` | `sat` | finite witness replay |
| `equivalent_categories_same_priority` | `unsat` | QF_UF/Alethe proof gap |
| `implementation_equivalence_qf_uf_gap` | `unsat` | QF_UF/Alethe proof gap |
