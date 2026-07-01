# Finite Group Action Checks

This pack adds a finite bridge between group theory, relations/functions, and
counting. It models a two-element group acting on two-bit strings by swapping
coordinates, so every action-law, orbit, stabilizer, and Burnside count is
small enough to replay exactly.

It checks:

- finite group-action identity and compatibility laws;
- orbit and stabilizer recomputation for a chosen point;
- orbit-stabilizer cardinality replay;
- Burnside fixed-point average for the action quotient count;
- checked QF_UF/Alethe rejection of a malformed identity-action table;
- checked QF_UF/Alethe rejection of a malformed action-compatibility table;
- general group-action theorems as Lean horizon.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-group-actions-v0
```
