# Checks

## `transition_witnesses`

Replays representative one-step transitions:

- a submitted application can request review and reach `under_review`;
- an approval request from `submitted` is denied and stays `submitted`;
- an under-review application can be approved when supervisor review is present;
- an approved application is terminal for the listed actions.

Evidence: finite witness replay.

## `no_skip_to_approved`

Asks for an application in `submitted` to reach `approved` directly by the
`approve` action. The source transition relation has no such edge.

Evidence today: checked Bool/QF_LIA evidence emitted by `produce_evidence` and
independently checked by `Evidence::check`, using
[`smt2/no-skip-to-approved-bool-qf-lia-conflict.smt2`](smt2/no-skip-to-approved-bool-qf-lia-conflict.smt2).

## `terminal_states_absorbing`

Asks for an `approved` workflow state to move back to `under_review`. Rule 7(d)
makes `approved` and `rejected` terminal states in this bounded model.

Evidence today: checked Bool/QF_LIA evidence emitted by `produce_evidence` and
independently checked by `Evidence::check`, using
[`smt2/terminal-states-absorbing-bool-qf-lia-conflict.smt2`](smt2/terminal-states-absorbing-bool-qf-lia-conflict.smt2).

## `implementation_equivalence`

Asks for the executable transition predicate to disagree with the declarative
model on the bounded state/action/supervisor slice.

Evidence today: checked Bool/QF_LIA evidence emitted by `produce_evidence` and
independently checked by `Evidence::check`, using
[`smt2/implementation-equivalence-bool-qf-lia-conflict.smt2`](smt2/implementation-equivalence-bool-qf-lia-conflict.smt2).
