# Formal Model

## Inputs

| Name | Sort | Meaning |
|---|---|---|
| `current_state` | `Enum(submitted,under_review,approved,rejected)` | Current workflow state before a single action. |
| `action` | `Enum(request_review,approve,reject)` | Requested workflow transition. |
| `supervisor_review` | `Bool` | Whether a supervisor has approved the review step. |

## Outputs

| Name | Sort | Meaning |
|---|---|---|
| `transition_allowed` | `Bool` | Whether the requested action is admitted by the policy. |
| `next_state` | state enum | The state after applying the action; denied transitions are no-ops. |

## Definition

```text
transition(submitted, request_review, supervisor_review) =
  (allowed = true, next = under_review)

transition(under_review, approve, true) =
  (allowed = true, next = approved)

transition(under_review, reject, supervisor_review) =
  (allowed = true, next = rejected)

otherwise =
  (allowed = false, next = current_state)
```

The two-step generated rows compose this same one-step function twice. That is
a bounded graph-reachability check, not a theorem about arbitrary workflow
lengths.

## Relationship To Math Resources

This pack reuses current math-resource proof shapes:

- finite graph reachability over a bounded transition system;
- finite replay for concrete transition and two-step path witnesses;
- Bool/QF_LIA checked evidence for small impossible-transition obligations;
- implementation-equivalence rows that compare an executable transition
  function against the declarative model.

The pack does not prove liveness, fairness, temporal logic, or unbounded
reachability. Those stay in theorem/horizon lanes until a suitable proof route
exists.
