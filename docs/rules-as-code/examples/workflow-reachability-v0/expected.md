# Expected Results

The finite sample covers the workflow states:

- `submitted`;
- `under_review`;
- `approved`;
- `rejected`.

and the actions:

- `request_review`;
- `approve`;
- `reject`.

with `supervisor_review` set to both `false` and `true`. That gives 24 bounded
one-step transition rows and 144 two-step reachability rows.

## Witnesses

| Witness | Expected | Purpose |
|---|---|---|
| `submitted_request_review` | allowed, next `under_review` | The review edge exists from `submitted`. |
| `submitted_approve_denied` | denied, next `submitted` | The workflow cannot skip review. |
| `review_approve_with_supervisor` | allowed, next `approved` | Supervisor approval admits the approval edge. |
| `approved_terminal_noop` | denied, next `approved` | Terminal approved state does not reopen. |

## Check Status

| Check | Expected Result | Proof Status |
|---|---|---|
| `transition_witnesses` | `sat` | finite witness replay |
| `no_skip_to_approved` | `unsat` | checked Bool/QF_LIA evidence |
| `terminal_states_absorbing` | `unsat` | checked Bool/QF_LIA evidence |
| `implementation_equivalence` | `unsat` | checked Bool/QF_LIA evidence |
