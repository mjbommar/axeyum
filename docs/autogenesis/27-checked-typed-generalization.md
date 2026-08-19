# Checked typed generalization

Date: 2026-08-19

## Result

The statement adapter now has ADR-0484's first semantic slicing primitive:
`generalize_goal_constants` turns caller-selected exact global constant
instances into an explicit dependent `Pi` telescope. The independent kernel
checks both the source and generalized statements as closed propositions.
`verify_generalized_specialization` then checks each dependent argument type
and requires full application to recover the source proposition by kernel
definitional equality.

The boundary is intentionally fail-closed:

- a constant is identified by declaration name **and** universe arguments;
- binders must be supplied in dependency order;
- each requested instance must occur in the statement or a later binder type;
- proof-valued constants are rejected rather than converted into premises;
- projections whose structure type is abstracted are rejected in v1; and
- duplicate instances, open expressions, ill-typed terms, and non-propositions
  are typed errors.

Six controls cover exact specialization back to the source goal, dependent
telescope ordering, proof-valued rejection, duplicate and unused selections,
distinct universe instances, and transport through the canonical root-selected
export into a fresh kernel. In the transport control, the generalized target
re-admits with no axioms and neither source constant exists in the new
environment.

## Assurance boundary

This is a checked mechanism, not an automatic selection policy and not a
production receipt. The caller still chooses which constants to abstract and
which proof-free dependencies may remain. No mathlib statement has been
credited, and the sealed held-out split has not been opened.

The current primitive verifies exact specialization but does not yet return a
durable specialization certificate. The next layer must bind selection,
generalized statement identity, retained dependency identity, fresh-kernel
identity, and that specialization result into one fail-closed receipt before
rerunning the train/dev census.

## Sequence from here

```text
validated source statement
        |
        | checked explicit generalization (this increment)
        v
closed generalized proposition
        |
        | root-selected canonical export + re-import
        v
fresh proof-free producer kernel
        |
        | exact specialization receipt (next)
        v
eligible train/dev type slice
```

Automatic selection should follow, not precede, the receipt. It may propose a
dependency-ordered abstraction set, but the mechanism above remains the
authority that accepts or rejects it. Only after measured train/dev coverage
should any policy be frozen and evaluated once against held-out.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test type_slice_generalization
cargo test -p axeyum-lean-import
cargo clippy -p axeyum-lean-import --all-targets -- -D warnings
```
