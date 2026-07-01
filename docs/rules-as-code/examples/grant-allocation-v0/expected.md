# Expected Results

The finite sample covers the rational shares:

- `0`;
- `1/4`;
- `1/2`;
- `3/4`;
- `1`.

That gives 125 bounded allocation triples. The generated query artifact also
emits the balanced-budget triples whose shares sum to exactly `1`.

## Witnesses

| Witness | Expected | Purpose |
|---|---|---|
| `floor_split_compliant` | `compliant = true` | Shelter and clinic sit exactly at their floors and admin sits exactly at the cap. |
| `clinic_heavy_compliant` | `compliant = true` | Shelter exceeds its floor, clinic meets its floor, and admin is zero. |
| `low_shelter_denied` | `compliant = false` | The budget balances but shelter is below `1/2`. |
| `over_admin_denied` | `compliant = false` | The budget balances but admin exceeds `1/4` and clinic is below its floor. |
| `over_budget_denied` | `compliant = false` | The shares sum to `5/4` instead of `1`. |

## Check Status

| Check | Expected Result | Proof Status |
|---|---|---|
| `allocation_witnesses` | `sat` | finite witness replay |
| `total_budget_respected` | `unsat` | checked QF_LRA/Farkas evidence |
| `shelter_minimum_respected` | `unsat` | checked QF_LRA/Farkas evidence |
| `clinic_minimum_respected` | `unsat` | checked QF_LRA/Farkas evidence |
| `admin_cap_respected` | `unsat` | checked QF_LRA/Farkas evidence |
| `implementation_equivalence` | `unsat` | checked QF_LRA/Farkas evidence |
