# Example Source Rules

This is toy policy text for the Rules-as-Code Verification Lab. It is not a
legal source.

## Rule 7(a): Review Transition

An application in `submitted` may move to `under_review` only by the
`request_review` action.

## Rule 7(b): Approval Transition

An application in `under_review` may move to `approved` by the `approve` action
only when `supervisor_review` is true.

## Rule 7(c): Rejection Transition

An application in `under_review` may move to `rejected` by the `reject` action.

## Rule 7(d): Terminal States

Applications in `approved` or `rejected` are terminal in this example workflow:
no listed action moves them to another state.

## Rule 7(e): Implementation

The executable workflow engine must implement exactly the same bounded
transition relation as Rules 7(a)-7(d).
