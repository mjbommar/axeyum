# Workflow Reachability V0

This example pack models a tiny review workflow as a finite transition system.

The point is not workflow-product design. The point is to exercise a rules/law
shape not covered by scalar eligibility, allocation, or category packs:
bounded graph reachability over states, terminal-state invariants, and
implementation equivalence for an executable transition relation.

## Audience

- Policy engineers modeling state-machine rules.
- Compliance engineers looking for forbidden transitions or skipped review
  paths.
- Axeyum contributors tracking how finite graph reachability maps to replayed
  rows and checked Bool/QF_LIA evidence.

## Rule Summary

For the example workflow:

- `submitted` can move to `under_review` by `request_review`;
- `under_review` can move to `approved` by `approve` only with supervisor
  review;
- `under_review` can move to `rejected` by `reject`;
- `approved` and `rejected` are terminal states;
- the executable workflow transition function must match the declarative
  model on the bounded slice.

The bounded model samples four states, three actions, and a Boolean supervisor
flag.

## Trust Boundary

- The source clauses in [source.md](source.md) are example policy text, not law.
- The finite transition and two-step reachability rows replay against the
  executable model in `scripts/validate-rules-as-code.py`.
- The impossible-transition and implementation-equivalence obligations are
  source-linked Bool/QF_LIA rows checked through the `rules_as_code_examples`
  regression harness with `Evidence::check`.
- The pack does not prove unbounded temporal properties, liveness, fairness, or
  compliance for a real workflow engine.

## Files

- [metadata.json](metadata.json) records the pack boundary.
- [source.md](source.md) records the cited example clauses.
- [model.md](model.md) describes the formalization.
- [checks.md](checks.md) lists the verification obligations.
- [expected.md](expected.md) summarizes replay witnesses and proof status.
- [expected.json](expected.json) is the machine-readable expected-result file.

## Validation

```sh
python3 scripts/gen-rules-as-code-dashboard.py
python3 scripts/validate-rules-as-code.py
python3 scripts/query-rules-as-code.py packs --pack workflow_reachability_v0 --require-any
cargo test -p axeyum-solver --test rules_as_code_examples workflow_reachability
```
