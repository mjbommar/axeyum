# Local subtraction-restoration replacement plan

Date: 2026-08-20

## Decision

The V2 joint quotient/remainder proof will replace exactly one dependency:
official `Nat.sub_add_cancel`, the sole `propext` carrier measured by the
dependency audit. The other 14 direct dependencies remain admissible and
empty-footprint.

The replacement is a local primitive-recursive proof inside the joint
invariant. It may not create another global theorem declaration, reuse
`Nat.sub_add_cancel` or `Nat.add_sub_of_le`, invoke proof search, read upstream
proof material, or change the mathematical route.

## Fresh source and gates

The failed V1 source remains immutable. One new path,
`scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean`, may contain the
replacement and the same exact theorem statement.

The first fresh kernel reconstruction must have an empty footprint, omit both
forbidden theorem dependencies, and enumerate its complete direct dependency
set. Only then may a second fresh reconstruction run. Both canonical theorem
identities must match.

This remains the private fuel invariant. Even two accepted runs do not
authorize the public `Nat.div_add_mod` lift, balanced Bézout, cancellation,
the Fibonacci target, evaluation credit, or a ledger write.

## Budget

One revised source path, one support declaration, and two kernel theorem
submissions are permitted. A kernel decline ends the increment with no retry.
No exact target or executor invocation is permitted.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-local-subtraction-replacement-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_local_subtraction_replacement_plan
```
